module Typing.TypingRules where

import Utils.BasicTypes
import Parser.SyntacticTypes
import Typing.SemanticTypes
import Typing.Normalization
import Typing.CoreTypes

-- Forms of judgement:
-- Γ ctx                                Γ is a context.
-- Γ ⊢ fresh -> x                       Γ does not bind x.
-- Γ ⊢ x lookup -> c_t                  Looking up x in Γ yields the type c_t.
-- Γ ⊢ e_t type -> c_t                  e_t represents the type c_t.
-- Γ ⊢ c_1 ≡ c_2 type                   c_1 and c_2 are the same type.
-- Γ ⊢ e ∈ c_t -> c_e                   Checking that e can have type c_t results in c_e.
-- Γ ⊢ e synth -> (the c_t c_e)         From e, the type c_t can be synthesized, resulting in c_e.
-- Γ ⊢ c_1 ≡ c_2 : c_t                  c_1 is the same c_t as c_2.

typingSynth :: Context -> Renaming -> SyntacticTerm -> Maybe The
typingSynth ctx r (SrcVar x) = do -- Hypothesis
    let realX = rename r x
    varTypeVal <- typingLookup ctx realX
    return $ The (readBackType ctx varTypeVal) (CoreVar realX)
typingSynth _ _ (SrcAtomLiteral sym) =  -- AtomI
    return $ The CoreAtom (CoreAtomLiteral sym)
typingSynth ctx r (SrcCar pr) = do -- SigmaE-1
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ xType _) ->
            return $ The (readBackType ctx xType) (CoreCar prOut)
        _ -> Nothing
typingSynth ctx r (SrcCdr pr) = do -- SigmaE-2
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ _ clos) ->
            return $ The (readBackType ctx (valOfClosure clos (doCar (valInCtx ctx prOut)))) (CoreCdr prOut)
        _ -> Nothing
typingSynth ctx r (SrcApplication f [arg]) = do -- FunE-1
    (The fType fOut) <- typingSynth ctx r f
    case valInCtx ctx fType of
        (PI _ xType clos) -> do
            argOut <- typingCheck ctx r arg xType
            let argOutVal = valInCtx ctx argOut
            return $ The (readBackType ctx (valOfClosure clos argOutVal)) (CoreApplication fOut argOut)
        _ -> Nothing
typingSynth ctx r (SrcApplication f args) = do -- FunE-2
    (The appFType appFOut) <- typingSynth ctx r (SrcApplication f (init args))
    case valInCtx ctx appFType of
        (PI _ xType clos) -> do
            argOut <- typingCheck ctx r (last args) xType
            let argOutVal = valInCtx ctx argOut
            return $ The (readBackType ctx (valOfClosure clos argOutVal)) (CoreApplication appFOut argOut)
        _ -> Nothing
typingSynth _ _ SrcNatZero = -- NatI-1
    return $ The CoreNat CoreNatZero
typingSynth ctx r (SrcNatAdd1 n) = do -- NatI-2
    nOut <- typingCheck ctx r n NAT
    return $ The CoreNat (CoreNatAdd1 nOut)
typingSynth _ _ (SrcNatLiteral 0) = -- NatI-3
    return $ The CoreNat CoreNatZero
typingSynth ctx r (SrcNatLiteral n) = do -- NatI-4
    nOut <- typingCheck ctx r (SrcNatLiteral (n-1)) NAT
    return $ The CoreNat (CoreNatAdd1 nOut)
typingSynth ctx r (SrcWhichNat target base step) = do -- NatE-1
    targetOut <- typingCheck ctx r target NAT
    (The baseType baseOut) <- typingSynth ctx r base
    let nMinus1 = fresh ctx "nMinus1"
    stepOut <- typingCheck ctx r step (PI nMinus1 NAT (FO_CLOS (ctxToEnv ctx) nMinus1 baseType))
    return $ The baseType (CoreWhichNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (SrcIterNat target base step) = do -- NatE-2
    targetOut <- typingCheck ctx r target NAT
    (The baseType baseOut) <- typingSynth ctx r base
    let old = fresh ctx "old"
    stepOut <- typingCheck ctx r step (valInCtx ctx (CorePi old baseType baseType))
    return $ The baseType (CoreIterNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (SrcRecNat target base step) = do -- NatE-3
    targetOut <- typingCheck ctx r target NAT
    (The baseType baseOut) <- typingSynth ctx r base
    let nMinus1 = fresh ctx "freshMinus1"
        old     = fresh ctx "fresh"
    stepOut <- typingCheck ctx r step (valInCtx ctx (CorePi nMinus1 CoreNat (CorePi old baseType baseType)))
    return $ The baseType (CoreRecNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (SrcIndNat target motive base step) = do -- NatE-4
    targetOut <- typingCheck ctx r target NAT
    motiveOut <- typingCheck ctx r motive (PI "n" NAT (HO_CLOS (\_ -> UNIVERSE)))
    let motiveOutVal = valInCtx ctx motiveOut
    baseOut <- typingCheck ctx r base (doAp motiveOutVal ZERO)
    stepOut <- typingCheck ctx r step (PI "nMinus1" NAT (HO_CLOS (\nMinus1 -> PI "ih" (doAp motiveOutVal nMinus1) (HO_CLOS (\_ -> doAp motiveOutVal (ADD1 nMinus1))))))
    return $ The (CoreApplication motiveOut targetOut) (CoreIndNat targetOut motiveOut baseOut stepOut)
typingSynth ctx r (SrcListColonColon e es) = do -- ListI-2
    (The eType eOut) <- typingSynth ctx r e
    esOut <- typingCheck ctx r es (valInCtx ctx (CoreList eType))
    return $ The (CoreList eType) (CoreListColonColon eOut esOut)
typingSynth ctx r (SrcRecList target base step) = do -- ListE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST eType) -> do
            (The baseType baseOut) <- typingSynth ctx r base
            let baseTypeVal = valInCtx ctx baseType
            stepOut <- typingCheck ctx r step (PI "e" eType (HO_CLOS (\_ -> PI "es" (LIST eType) (HO_CLOS (\_ -> PI "ih" baseTypeVal (HO_CLOS (\_ -> baseTypeVal)))))))
            return $ The baseType (CoreRecList targetOut (The baseType baseOut) stepOut)
        _ -> Nothing
typingSynth ctx r (SrcIndList target motive base step) = do -- ListE-2
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST eType) -> do
            motiveOut <- typingCheck ctx r motive (PI "xs" (LIST eType) (FO_CLOS (ctxToEnv ctx) "xs" CoreU))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal NIL)
            stepOut <- typingCheck ctx r step (PI "e" eType (HO_CLOS (\e -> PI "es" (LIST eType) (HO_CLOS (\es -> PI "ih" (doAp motiveOutVal es) (HO_CLOS (\_ -> doAp motiveOutVal (LIST_COLON_COLON e es))))))))
            return $ The (CoreApplication motiveOut targetOut) (CoreIndList targetOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (SrcHead es) = do -- VecE-1
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC eTypeVal (ADD1 _)) ->
            return $ The (readBackType ctx eTypeVal) (CoreHead esOut)
        _ -> Nothing
typingSynth ctx r (SrcTail es) = do -- VecE-2
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC eTypeVal (ADD1 lenMinus1)) ->
            return $ The (CoreVec (readBackType ctx eTypeVal) (readBack ctx NAT lenMinus1)) (CoreTail esOut)
        _ -> Nothing
typingSynth ctx r (SrcIndVec len target motive base step) = do -- VecE-3
    lenOut <- typingCheck ctx r len NAT
    let lenOutVal = valInCtx ctx lenOut
    (The vecType vecOut) <- typingSynth ctx r target
    case valInCtx ctx vecType of
        (VEC eTypeVal vecLenVal) -> do
            _ <- convert ctx NAT lenOutVal vecLenVal
            motiveOut <- typingCheck ctx r motive (PI "k" NAT (HO_CLOS (\k -> PI "es" (VEC eTypeVal k) (HO_CLOS (\_ -> UNIVERSE)))))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp (doAp motiveOutVal ZERO) VECNIL)
            stepOut <- typingCheck ctx r step (indVecStepType eTypeVal motiveOutVal)
            return $ The (CoreApplication motiveOut lenOut) (CoreIndVec lenOut vecOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (SrcEqReplace target motive base) = do -- EqE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL xTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "x" xTypeVal (HO_CLOS (\_ -> UNIVERSE)))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal fromVal)
            return $ The (readBackType ctx (doAp motiveOutVal toVal)) (CoreReplace targetOut motiveOut baseOut)
        _ -> Nothing
typingSynth ctx r (SrcEqCong target func) = do -- EqE-2
    (The targetType targetOut) <- typingSynth ctx r target
    (The funcType funcOut) <- typingSynth ctx r func
    case (valInCtx ctx targetType, valInCtx ctx funcType) of
        ((EQUAL xTypeVal fromVal toVal), (PI _ domainTypeVal clos)) -> do
            _ <- sameType ctx xTypeVal domainTypeVal
-- NOTE: The reference implementation of Pie is missing the below `sameType` check.
--  The inference rule requires that the codomain type of the pi type be independent of the domain parameter (i.e. be an arrow type),
--  but since there is no easy way to check independence, it is instead sufficient to check that the endpoints are within the same fiber.
--  In other words, since `cong` is not dependent, the below check ensures that `f(from)` and `f(to)` end up being inhabitants of the same type.
--  As far as I can tell, the reference implementation is thus unsound and does not match the inference rule contained in the book.
            let coDomainTypeVal = valOfClosure clos fromVal
            _ <- sameType ctx coDomainTypeVal (valOfClosure clos toVal)
            let coDomainTypeOut = readBackType ctx coDomainTypeVal
                funcVal = valInCtx ctx funcOut
            return $ The
                (CoreEq coDomainTypeOut (readBack ctx coDomainTypeVal (doAp funcVal fromVal)) (readBack ctx coDomainTypeVal (doAp funcVal toVal)))
                (CoreCong targetOut coDomainTypeOut funcOut)
        _ -> Nothing
typingSynth ctx r (SrcEqSymm t) = do -- EqE-3
    (The tType tOut) <- typingSynth ctx r t
    case valInCtx ctx tType of
        (EQUAL xTypeVal fromVal toVal) ->
            return $ The (readBackType ctx (EQUAL xTypeVal toVal fromVal)) (CoreSymm tOut)
        _ -> Nothing
typingSynth ctx r (SrcEqTrans t1 t2) = do -- EqE-4
    (The t1Type t1Out) <- typingSynth ctx r t1
    (The t2Type t2Out) <- typingSynth ctx r t2
    case (valInCtx ctx t1Type, valInCtx ctx t2Type) of
        ((EQUAL xTypeVal fromVal midVal), (EQUAL yTypeVal mid2Val toVal)) -> do
            _ <- sameType ctx xTypeVal yTypeVal
            _ <- convert ctx xTypeVal midVal mid2Val
            return $ The (readBackType ctx (EQUAL xTypeVal fromVal toVal)) (CoreTrans t1Out t2Out)
        _ -> Nothing
typingSynth ctx r (SrcEqIndEq target motive base) = do -- EqE-5: Based Path Induction (aka: Parameter-variant of the J-eliminator)
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL xTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "to" xTypeVal (HO_CLOS (\to -> PI "p" (EQUAL xTypeVal fromVal to) (HO_CLOS (\_ -> UNIVERSE)))))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp (doAp motiveOutVal fromVal) (SAME fromVal))
            return $ The (readBackType ctx (doAp (doAp motiveOutVal toVal) (valInCtx ctx targetOut))) (CoreIndEq targetOut motiveOut baseOut)
        _ -> Nothing
typingSynth ctx r (SrcIndEither target motive baseLeft baseRight) = do -- EitherE
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EITHER leftVal rightVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "x" (EITHER leftVal rightVal) (HO_CLOS (\_ -> UNIVERSE)))
            let motiveOutVal = valInCtx ctx motiveOut
            leftOut <- typingCheck ctx r baseLeft (PI "x" leftVal (HO_CLOS (\x -> doAp motiveOutVal (LEFT x))))
            rightOut <- typingCheck ctx r baseRight (PI "x" rightVal (HO_CLOS (\x -> doAp motiveOutVal (RIGHT x))))
            return $ The (CoreApplication motiveOut targetOut) (CoreIndEither targetOut motiveOut leftOut rightOut)
        _ -> Nothing
typingSynth _ _ SrcTrivialSole = -- TrivialI
    return $ The CoreTrivial CoreTrivialSole
typingSynth ctx r (SrcIndAbsurd target motive) = do -- AbsurdE
    targetOut <- typingCheck ctx r target ABSURD
    motiveOut <- typingCheck ctx r motive UNIVERSE
    return $ The motiveOut (CoreIndAbsurd targetOut motiveOut)
typingSynth _ _ SrcAtom = -- UI-1
    return $ The CoreU CoreAtom
typingSynth ctx r (SrcSigma [(x, aType)] dType) = do -- UI-2
    let xPrime = fresh ctx x
    aTypeOut <- typingCheck ctx r aType UNIVERSE
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- typingCheck (bindFree ctx xPrime aTypeOutVal) (extendRenaming r x xPrime) dType UNIVERSE
    return $ The CoreU (CoreSigma xPrime aTypeOut dTypeOut)
typingSynth ctx r (SrcSigma ((x, aType):aRest) dType) = do -- UI-3
    let xPrime = fresh ctx x
    aTypeOut <- typingCheck ctx r aType UNIVERSE
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- typingCheck (bindFree ctx xPrime aTypeOutVal) (extendRenaming r x xPrime) (SrcSigma aRest dType) UNIVERSE
    return $ The CoreU (CoreSigma xPrime aTypeOut dTypeOut)
typingSynth ctx r (SrcPair aType dType) = do -- UI-4
-- NOTE: I believe there is a bug in the reference implementation of UI-4.
--  They call `fresh` below instead of `fresh-binder`, but they call `fresh-binder` for `Pair` in `is-type`.
--  The `isType` and `UI-4` implementations are otherwise identical in terms of the inference rules and implementations besides the return value (annotation vs type).
    let x = freshBinder ctx dType "x"
    aTypeOut <- typingCheck ctx r aType UNIVERSE
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- typingCheck (bindFree ctx x aTypeOutVal) r dType UNIVERSE
    return $ The CoreU (CoreSigma x aTypeOut dTypeOut)
typingSynth ctx r (SrcPi [(x, xType)] rType) = do -- UI-5
    let xPrime = fresh ctx x
    xTypeOut <- typingCheck ctx r xType UNIVERSE
    let xTypeOutVal = valInCtx ctx xTypeOut
    rTypeOut <- typingCheck (bindFree ctx xPrime xTypeOutVal) (extendRenaming r x xPrime) rType UNIVERSE
    return $ The CoreU (CorePi xPrime xTypeOut rTypeOut)
typingSynth ctx r (SrcPi ((x, xType):xRest) rType) = do -- UI-6
    let xPrime = fresh ctx x
    xTypeOut <- typingCheck ctx r xType UNIVERSE
    let xTypeOutVal = valInCtx ctx xTypeOut
    rTypeOut <- typingCheck (bindFree ctx xPrime xTypeOutVal) (extendRenaming r x xPrime) (SrcPi xRest rType) UNIVERSE
    return $ The CoreU (CorePi xPrime xTypeOut rTypeOut)
typingSynth ctx r (SrcArrow argType [rType]) = do -- UI-7
    let x = freshBinder ctx rType "x"
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- typingCheck (bindFree ctx x argTypeOutVal) r rType UNIVERSE
    return $ The CoreU (CorePi x argTypeOut rTypeOut)
typingSynth ctx r (SrcArrow argType (rType1:rType2:rRest)) = do -- UI-8
    let x = freshBinder ctx (SrcApplication rType2 rRest) "x"
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- typingCheck (bindFree ctx x argTypeOutVal) r (SrcArrow rType1 (rType2:rRest)) UNIVERSE
    return $ The CoreU (CorePi x argTypeOut rTypeOut)
typingSynth _ _ SrcNat = -- UI-9
    return $ The CoreU CoreNat
typingSynth ctx r (SrcList eType) = do -- UI-10
    eTypeOut <- typingCheck ctx r eType UNIVERSE
    return $ The CoreU (CoreList eTypeOut)
typingSynth ctx r (SrcVec eType len) = do -- UI-11
    eTypeOut <- typingCheck ctx r eType UNIVERSE
    lOut <- typingCheck ctx r len NAT
    return $ The CoreU (CoreVec eTypeOut lOut)
typingSynth ctx r (SrcEq xType from to) = do -- UI-12
    xTypeOut <- typingCheck ctx r xType UNIVERSE
    let xTypeOutVal = valInCtx ctx xTypeOut
    fromOut <- typingCheck ctx r from xTypeOutVal
    toOut <- typingCheck ctx r to xTypeOutVal
    return $ The CoreU (CoreEq xTypeOut fromOut toOut)
typingSynth ctx r (SrcEither pType sType) = do -- UI-13
    pTypeOut <- typingCheck ctx r pType UNIVERSE
    sTypeOut <- typingCheck ctx r sType UNIVERSE
    return $ The CoreU (CoreEither pTypeOut sTypeOut)
typingSynth _ _ SrcTrivial = -- UI-14
    return $ The CoreU CoreTrivial
typingSynth _ _ SrcAbsurd = -- UI-15
    return $ The CoreU CoreAbsurd
typingSynth ctx r (SrcThe t e) = do
    tOut <- isType ctx r t
    eOut <- typingCheck ctx r e (valInCtx ctx tOut)
    return $ The tOut eOut
typingSynth _ _ _ = Nothing

isType :: Context -> Renaming -> SyntacticTerm -> Maybe CoreTerm
isType _ _ SrcAtom = -- AtomF
    return $ CoreAtom
isType ctx r (SrcSigma [(x, aType)] dType) = do -- SigmaF-1
    let xPrime = fresh ctx x
    aTypeOut <- isType ctx r aType
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- isType (bindFree ctx xPrime aTypeOutVal) (extendRenaming r x xPrime) dType
    return $ CoreSigma xPrime aTypeOut dTypeOut
isType ctx r (SrcSigma ((x, aType):aRest) dType) = do -- SigmaF-2
    let xPrime = fresh ctx x
    aTypeOut <- isType ctx r aType
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- isType (bindFree ctx xPrime aTypeOutVal) (extendRenaming r x xPrime) (SrcSigma aRest dType)
    return $ CoreSigma xPrime aTypeOut dTypeOut
isType ctx r (SrcPair aType dType) = do -- SigmaF-Pair
    let x = freshBinder ctx dType "x"
    aTypeOut <- isType ctx r aType
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- isType (bindFree ctx x aTypeOutVal) r dType
    return $ CoreSigma x aTypeOut dTypeOut
isType ctx r (SrcPi [(x, argType)] rType) = do -- FunF-1
    let xPrime = fresh ctx x
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- isType (bindFree ctx xPrime argTypeOutVal) (extendRenaming r x xPrime) rType
    return $ CorePi xPrime argTypeOut rTypeOut
isType ctx r (SrcPi ((x, argType):argRest) rType) = do -- FunF-2
    let xPrime = fresh ctx x
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- isType (bindFree ctx xPrime argTypeOutVal) (extendRenaming r x xPrime) (SrcPi argRest rType)
    return $ CorePi xPrime argTypeOut rTypeOut
isType ctx r (SrcArrow argType [rType]) = do -- FunFArrow-1
    let x = freshBinder ctx rType "x"
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- isType (bindFree ctx x argTypeOutVal) r rType
    return $ CorePi x argTypeOut rTypeOut
isType ctx r (SrcArrow argType (rType1:rType2:rRest)) = do -- FunFArrow-2
    let x = freshBinder ctx (SrcApplication rType2 rRest) "x"
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- isType (bindFree ctx x argTypeOutVal) r (SrcArrow rType1 (rType2:rRest))
    return $ CorePi x argTypeOut rTypeOut
isType _ _ SrcNat = -- NatF
    return $ CoreNat
isType ctx r (SrcList eType) = do -- ListF
    eTypeOut <- isType ctx r eType
    return $ CoreList eTypeOut
isType ctx r (SrcVec eType l) = do -- VecF
    eTypeOut <- isType ctx r eType
    lOut <- typingCheck ctx r l NAT
    return $ CoreVec eTypeOut lOut
isType ctx r (SrcEq xType from to) = do -- EqF
    xTypeOut <- isType ctx r xType
    let xTypeOutVal = valInCtx ctx xTypeOut
    fromOut <- typingCheck ctx r from xTypeOutVal
    toOut <- typingCheck ctx r to xTypeOutVal
    return $ CoreEq xTypeOut fromOut toOut
isType ctx r (SrcEither pType sType) = do -- EitherF
    pTypeOut <- isType ctx r pType
    sTypeOut <- isType ctx r sType
    return $ CoreEither pTypeOut sTypeOut
isType _ _ SrcTrivial = -- TrivialF
    return $ CoreTrivial
isType _ _ SrcAbsurd = -- AbsurdF
    return $ CoreAbsurd
isType _ _ SrcU = -- EL
    return $ CoreU
isType ctx r expr = typingCheck ctx r expr UNIVERSE

typingCheck :: Context -> Renaming -> SyntacticTerm -> Value -> Maybe CoreTerm
typingCheck ctx r (SrcCons a d) (SIGMA _ aType dType) = do -- SigmaI
    aOut <- typingCheck ctx r a aType
    dOut <- typingCheck ctx r d (valOfClosure dType (valInCtx ctx aOut))
    return $ CoreCons aOut dOut
typingCheck ctx r (SrcLambda [lambdaX] lambdaR) (PI _ argType rType) = do -- FunI-1
    let xPrime = fresh ctx lambdaX
    rOut <- typingCheck (bindFree ctx xPrime argType) (extendRenaming r lambdaX xPrime) lambdaR (valOfClosure rType (NEU argType (N_Var xPrime)))
    return $ CoreLambda xPrime rOut
typingCheck ctx r (SrcLambda (lambdaX:lambdaRest) lambdaR) typeVal = -- FunI-2
    typingCheck ctx r (SrcLambda [lambdaX] (SrcLambda lambdaRest lambdaR)) typeVal
typingCheck _ _ SrcListNil (LIST _) = -- ListI-1
    return $ CoreListNil
typingCheck _ _ SrcVecNil (VEC _ ZERO) = -- VecI-1
    return $ CoreVecNil
typingCheck ctx r (SrcVecColonColon e es) (VEC eType (ADD1 l)) = do -- VecI-2
    eOut <- typingCheck ctx r e eType
    esOut <- typingCheck ctx r es (VEC eType l)
    return $ CoreVecColonColon eOut esOut
typingCheck ctx r (SrcEqSame mid) (EQUAL xTypeVal fromVal toVal) = do -- EqI
    midOut <- typingCheck ctx r mid xTypeVal
    let midOutVal = valInCtx ctx midOut
    _ <- convert ctx xTypeVal fromVal midOutVal
    _ <- convert ctx xTypeVal toVal midOutVal
    return $ CoreEqSame midOut
typingCheck ctx r (SrcEitherLeft lt) (EITHER pType _) = do -- EitherI-1
    ltOut <- typingCheck ctx r lt pType
    return $ CoreEitherLeft ltOut
typingCheck ctx r (SrcEitherRight rt) (EITHER _ sType) = do -- EitherI-2
    rtOut <- typingCheck ctx r rt sType
    return $ CoreEitherRight rtOut
typingCheck ctx r expr ty = do
    (The exprTypeOut exprOut) <- typingSynth ctx r expr
    _ <- sameType ctx (valInCtx ctx exprTypeOut) ty
    return $ exprOut

alphaEquiv :: CoreTerm -> CoreTerm -> Bool
alphaEquiv e1 e2 = alphaEquivImpl 0 [] [] e1 e2

alphaEquivImpl :: Int -> Bindings -> Bindings -> CoreTerm -> CoreTerm -> Bool
alphaEquivImpl lvl b1 b2 (CorePi x1 xType1 rType1) (CorePi x2 xType2 rType2) =
    (alphaEquivImpl lvl b1 b2 xType1 xType2) && (alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) rType1 rType2)
alphaEquivImpl lvl b1 b2 (CoreSigma x1 xType1 rType1) (CoreSigma x2 xType2 rType2) =
    (alphaEquivImpl lvl b1 b2 xType1 xType2) && (alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) rType1 rType2)
alphaEquivImpl lvl b1 b2 (CoreLambda x1 body1) (CoreLambda x2 body2) =
    alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) body1 body2
-- NOTE: This is the other half of the eta rule in `readBack`
alphaEquivImpl _ _ _ (CoreThe (The CoreAbsurd _)) (CoreThe (The CoreAbsurd _)) = True
alphaEquivImpl _ b1 b2 (CoreVar x) (CoreVar y) =
    let xBinding = lookupBinding b1 x
        yBinding = lookupBinding b2 y
    in case (xBinding, yBinding) of
        (Just lvlX, Just lvlY) -> lvlX == lvlY
        (Nothing, Nothing) -> x == y
        (_, _) -> False
alphaEquivImpl _ _ _ e1 e2 = e1 == e2

lookupBinding :: Bindings -> Name -> Maybe Int
lookupBinding [] _ = Nothing
lookupBinding (h:t) x
    | fst h == x    = Just $ snd h
    | otherwise     = lookupBinding t x

bind :: Bindings -> Name -> Int -> Bindings
bind b x lvl = ((x, lvl):b)

convert :: Context -> Value -> Value -> Value -> Maybe ConvertSuccess
convert ctx typeVal aVal bVal =
    let a = readBack ctx typeVal aVal
        b = readBack ctx typeVal bVal
    in if alphaEquiv a b then Just ConvertSuccess else Nothing

sameType :: Context -> Value -> Value -> Maybe ConvertSuccess
sameType ctx given expected =
    let givenE = readBackType ctx given
        expectedE = readBackType ctx expected
    in if alphaEquiv givenE expectedE then Just ConvertSuccess else Nothing
