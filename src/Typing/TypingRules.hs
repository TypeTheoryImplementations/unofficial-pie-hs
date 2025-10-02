module Typing.TypingRules where

import Parser.SyntacticTypes
import Typing.SemanticTypes
import Typing.Normalization

-- Forms of judgement:
-- Γ ctx                                Γ is a context.
-- Γ ⊢ fresh -> x                       Γ does not bind x.
-- Γ ⊢ x lookup -> c_t                  Looking up x in Γ yields the type c_t.
-- Γ ⊢ e_t type -> c_t                  e_t represents the type c_t.
-- Γ ⊢ c_1 ≡ c_2 type                   c_1 and c_2 are the same type.
-- Γ ⊢ e ∈ c_t -> c_e                   Checking that e can have type c_t results in c_e.
-- Γ ⊢ e synth -> (the c_t c_e)         From e, the type c_t can be synthesized, resulting in c_e.
-- Γ ⊢ c_1 ≡ c_2 : c_t                  c_1 is the same c_t as c_2.

typingSynth :: Context -> Renaming -> Term -> Maybe The
typingSynth ctx r (TermVar x) = do -- Hypothesis
    let realX = rename r x
    varTypeVal <- typingLookup ctx realX
    return $ The (readBackType ctx varTypeVal) (TermVar realX)
typingSynth _ _ (TermAtomLiteral sym) =  -- AtomI
    return $ The TermAtom (TermAtomLiteral sym)
typingSynth ctx r (TermCar pr) = do -- SigmaE-1
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ xType _) ->
            return $ The (readBackType ctx xType) (TermCar prOut)
        _ -> Nothing
typingSynth ctx r (TermCdr pr) = do -- SigmaE-2
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ _ clos) ->
            return $ The (readBackType ctx (valOfClosure clos (doCar (valInCtx ctx prOut)))) (TermCdr prOut)
        _ -> Nothing
typingSynth ctx r (TermApplication f arg) = do -- FunE
    (The fType fOut) <- typingSynth ctx r f
    case valInCtx ctx fType of
        (PI _ xType clos) -> do
            argOut <- typingCheck ctx r arg xType
            return $ The (readBackType ctx (valOfClosure clos (valInCtx ctx argOut))) (TermApplication fOut argOut)
        _ -> Nothing
typingSynth _ _ TermNatZero = -- NatI-1
    return $ The TermNat TermNatZero
typingSynth ctx r (TermNatAdd1 n) = do -- NatI-2
    nOut <- typingCheck ctx r n NAT
    return $ The TermNat (TermNatAdd1 nOut)
typingSynth ctx r (TermWhichNat target (The baseType base) step) = do -- NatE-1
    targetOut <- typingCheck ctx r target NAT
    baseOut <- typingCheck ctx r base (valInCtx ctx baseType)
    let nMinus1 = fresh ctx "nMinus1"
    stepOut <- typingCheck ctx r step (PI nMinus1 NAT (FO_CLOS (ctxToEnv ctx) nMinus1 baseType))
    return $ The baseType (TermWhichNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (TermIterNat target (The baseType base) step) = do -- NatE-2
    targetOut <- typingCheck ctx r target NAT
    baseOut <- typingCheck ctx r base (valInCtx ctx baseType)
    let old = fresh ctx "old"
    stepOut <- typingCheck ctx r step (valInCtx ctx (TermPi old baseType baseType))
    return $ The baseType (TermIterNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (TermRecNat target (The baseType base) step) = do -- NatE-3
    targetOut <- typingCheck ctx r target NAT
    baseOut <- typingCheck ctx r base (valInCtx ctx baseType)
    let nMinus1 = fresh ctx "freshMinus1"
        old     = fresh ctx "fresh"
    stepOut <- typingCheck ctx r step (valInCtx ctx (TermPi nMinus1 TermNat (TermPi old baseType baseType)))
    return $ The baseType (TermRecNat targetOut (The baseType baseOut) stepOut)
typingSynth ctx r (TermIndNat target motive base step) = do -- NatE-4
    targetOut <- typingCheck ctx r target NAT
    motiveOut <- typingCheck ctx r motive (PI "n" NAT (HO_CLOS (\_ -> UNIVERSE)))
    let motiveOutVal = valInCtx ctx motiveOut
    baseOut <- typingCheck ctx r base (doAp motiveOutVal ZERO)
    stepOut <- typingCheck ctx r step (PI "nMinus1" NAT (HO_CLOS (\nMinus1 -> PI "ih" (doAp motiveOutVal nMinus1) (HO_CLOS (\_ -> doAp motiveOutVal (ADD1 nMinus1))))))
    return $ The (TermApplication motiveOut targetOut) (TermIndNat targetOut motiveOut baseOut stepOut)
typingSynth ctx r (TermListColonColon e es) = do -- ListI-2
    (The eType eOut) <- typingSynth ctx r e
    esOut <- typingCheck ctx r es (valInCtx ctx (TermList eType))
    return $ The (TermList eType) (TermListColonColon eOut esOut)
typingSynth ctx r (TermRecList target (The baseType base) step) = do -- ListE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST eType) -> do
            let baseTypeVal = valInCtx ctx baseType 
            baseOut <- typingCheck ctx r base baseTypeVal
            stepOut <- typingCheck ctx r step (PI "e" eType (HO_CLOS (\_ -> PI "es" (LIST eType) (HO_CLOS (\_ -> PI "ih" baseTypeVal (HO_CLOS (\_ -> baseTypeVal)))))))
            return $ The baseType (TermRecList targetOut (The baseType baseOut) stepOut)
        _ -> Nothing
typingSynth ctx r (TermIndList target motive base step) = do -- ListE-2
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST eType) -> do
            motiveOut <- typingCheck ctx r motive (PI "xs" (LIST eType) (FO_CLOS (ctxToEnv ctx) "xs" TermU))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal NIL)
            stepOut <- typingCheck ctx r step (PI "e" eType (HO_CLOS (\e -> PI "es" (LIST eType) (HO_CLOS (\es -> PI "ih" (doAp motiveOutVal es) (HO_CLOS (\_ -> doAp motiveOutVal (LIST_COLON_COLON e es))))))))
            return $ The (TermApplication motiveOut targetOut) (TermIndList targetOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (TermHead es) = do -- VecE-1
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC eTypeVal (ADD1 _)) ->
            return $ The (readBackType ctx eTypeVal) (TermHead esOut)
        _ -> Nothing
typingSynth ctx r (TermTail es) = do -- VecE-2
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC eTypeVal (ADD1 lenMinus1)) ->
            return $ The (TermVec (readBackType ctx eTypeVal) (readBack ctx NAT lenMinus1)) (TermTail esOut)
        _ -> Nothing
typingSynth ctx r (TermIndVec len target motive base step) = do -- VecE-3
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
            return $ The (TermApplication motiveOut lenOut) (TermIndVec lenOut vecOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (TermReplace target motive base) = do -- EqE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL xTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "x" xTypeVal (HO_CLOS (\_ -> UNIVERSE)))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal fromVal)
            return $ The (readBackType ctx (doAp motiveOutVal toVal)) (TermReplace targetOut motiveOut baseOut)
        _ -> Nothing
typingSynth ctx r (TermCong xType t f) = do -- EqE-2
    xTypeOut <- isType ctx r xType
    let xTypeVal = valInCtx ctx xTypeOut
    (The tTypeOut tOut) <- typingSynth ctx r t
    (The fTypeOut fOut) <- typingSynth ctx r f
    case (valInCtx ctx tTypeOut, valInCtx ctx fTypeOut) of
        ((EQUAL yTypeVal fromVal toVal), (PI _ zTypeVal clos)) -> do
            _ <- sameType ctx xTypeVal yTypeVal
            _ <- sameType ctx yTypeVal zTypeVal
            let coDomainTypeVal = valOfClosure clos fromVal
            let fVal = valInCtx ctx fOut
            let coDomainTypeOut = readBackType ctx coDomainTypeVal
            -- NOTE: This diverges from the Racket reference implementation, but more closely matches the actual raw inference type rule. For convenience purposes,
                -- they actually store the codomain type in the 3-param cong (and only do synth on the 2-param cong, and also have a different param order for the 3-param cong),
                -- but the actual type rule and standing convention in line with our other synth rules is to keep the domain type in the expression itself and just use
                -- the codomain type in the type annotation that is returned.
            return $ The (TermEq coDomainTypeOut (readBack ctx coDomainTypeVal (doAp fVal fromVal)) (readBack ctx coDomainTypeVal (doAp fVal toVal))) (TermCong xTypeOut tOut fOut)
        _ -> Nothing
typingSynth ctx r (TermSymm t) = do -- EqE-3
    (The tType tOut) <- typingSynth ctx r t
    case valInCtx ctx tType of
        (EQUAL xTypeVal fromVal toVal) ->
            return $ The (readBackType ctx (EQUAL xTypeVal toVal fromVal)) (TermSymm tOut)
        _ -> Nothing
typingSynth ctx r (TermTrans t1 t2) = do -- EqE-4
    (The t1Type t1Out) <- typingSynth ctx r t1
    (The t2Type t2Out) <- typingSynth ctx r t2
    case (valInCtx ctx t1Type, valInCtx ctx t2Type) of
        ((EQUAL xTypeVal fromVal midVal), (EQUAL yTypeVal mid2Val toVal)) -> do
            _ <- sameType ctx xTypeVal yTypeVal
            _ <- convert ctx xTypeVal midVal mid2Val
            return $ The (readBackType ctx (EQUAL xTypeVal fromVal toVal)) (TermTrans t1Out t2Out)
        _ -> Nothing
typingSynth ctx r (TermIndEq target motive base) = do -- EqE-5: Based Path Induction (aka: Parameter-variant of the J-eliminator)
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL xTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "to" xTypeVal (HO_CLOS (\to -> PI "p" (EQUAL xTypeVal fromVal to) (HO_CLOS (\_ -> UNIVERSE)))))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp (doAp motiveOutVal fromVal) (SAME fromVal))
            return $ The (readBackType ctx (doAp (doAp motiveOutVal toVal) (valInCtx ctx targetOut))) (TermIndEq targetOut motiveOut baseOut)
        _ -> Nothing
typingSynth ctx r (TermIndEither target motive baseLeft baseRight) = do -- EitherE
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EITHER leftVal rightVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "x" (EITHER leftVal rightVal) (HO_CLOS (\_ -> UNIVERSE)))
            let motiveOutVal = valInCtx ctx motiveOut
            leftOut <- typingCheck ctx r baseLeft (PI "x" leftVal (HO_CLOS (\x -> doAp motiveOutVal (LEFT x))))
            rightOut <- typingCheck ctx r baseRight (PI "x" rightVal (HO_CLOS (\x -> doAp motiveOutVal (RIGHT x))))
            return $ The (TermApplication motiveOut targetOut) (TermIndEither targetOut motiveOut leftOut rightOut)
        _ -> Nothing
typingSynth _ _ TermTrivialSole = -- TrivialI
    return $ The TermTrivial TermTrivialSole
typingSynth ctx r (TermIndAbsurd target motive) = do -- AbsurdE
    targetOut <- typingCheck ctx r target ABSURD
    motiveOut <- isType ctx r motive
    return $ The motiveOut (TermIndAbsurd targetOut motiveOut)
typingSynth _ _ TermAtom = -- UI-1
    return $ The TermU TermAtom
typingSynth ctx r (TermSigma x aType dType) = do -- UI-2
    let xPrime = fresh ctx x
    aTypeOut <- isType ctx r aType
    dTypeOut <- isType (bindFree ctx xPrime (valInCtx ctx aTypeOut)) (extendRenaming r x xPrime) dType
    return $ The TermU (TermSigma xPrime aTypeOut dTypeOut)
typingSynth ctx r (TermPi x xType rType) = do -- UI-5
    let xPrime = fresh ctx x
    xTypeOut <- isType ctx r xType
    rTypeOut <- isType (bindFree ctx xPrime (valInCtx ctx xTypeOut)) (extendRenaming r x xPrime) rType
    return $ The TermU (TermPi xPrime xTypeOut rTypeOut)
typingSynth _ _ TermNat = -- UI-9
    return $ The TermU TermNat
typingSynth ctx r (TermList eType) = do -- UI-10
    eTypeOut <- isType ctx r eType
    return $ The TermU (TermList eTypeOut)
typingSynth ctx r (TermVec eType len) = do -- UI-11
    eTypeOut <- isType ctx r eType
    lOut <- typingCheck ctx r len NAT
    return $ The TermU (TermVec eTypeOut lOut)
typingSynth ctx r (TermEq xType from to) = do -- UI-12
    xTypeOut <- isType ctx r xType
    let xTypeOutVal = valInCtx ctx xTypeOut
    fromOut <- typingCheck ctx r from xTypeOutVal
    toOut <- typingCheck ctx r to xTypeOutVal
    return $ The TermU (TermEq xTypeOut fromOut toOut)
typingSynth ctx r (TermEither pType sType) = do -- UI-13
    pTypeOut <- isType ctx r pType
    sTypeOut <- isType ctx r sType
    return $ The TermU (TermEither pTypeOut sTypeOut)
typingSynth _ _ TermTrivial = -- UI-14
    return $ The TermU TermTrivial
typingSynth _ _ TermAbsurd = -- UI-15
    return $ The TermU TermAbsurd
typingSynth ctx r (TermThe (The t e)) = do
    tOut <- isType ctx r t
    eOut <- typingCheck ctx r e (valInCtx ctx tOut)
    return $ The tOut eOut
typingSynth _ _ _ = Nothing

isType :: Context -> Renaming -> Term -> Maybe Term
isType _ _ TermAtom = -- AtomF
    return $ TermAtom
isType ctx r (TermSigma x aType dType) = do -- SigmaF
    let xPrime = fresh ctx x
    aTypeOut <- isType ctx r aType
    let aTypeOutVal = valInCtx ctx aTypeOut
    dTypeOut <- isType (bindFree ctx xPrime aTypeOutVal) (extendRenaming r x xPrime) dType
    return $ TermSigma xPrime aTypeOut dTypeOut
isType ctx r (TermPi x argType rType) = do -- FunF
    let xPrime = fresh ctx x
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    rTypeOut <- isType (bindFree ctx xPrime argTypeOutVal) (extendRenaming r x xPrime) rType
    return $ TermPi xPrime argTypeOut rTypeOut
isType _ _ TermNat = -- NatF
    return $ TermNat
isType ctx r (TermList eType) = do -- ListF
    eTypeOut <- isType ctx r eType
    return $ TermList eTypeOut
isType ctx r (TermVec eType l) = do -- VecF
    eTypeOut <- isType ctx r eType
    lOut <- typingCheck ctx r l NAT
    return $ TermVec eTypeOut lOut
isType ctx r (TermEq xType from to) = do -- EqF
    xTypeOut <- isType ctx r xType
    let xTypeOutVal = valInCtx ctx xTypeOut
    fromOut <- typingCheck ctx r from xTypeOutVal
    toOut <- typingCheck ctx r to xTypeOutVal
    return $ TermEq xTypeOut fromOut toOut
isType ctx r (TermEither pType sType) = do -- EitherF
    pTypeOut <- isType ctx r pType
    sTypeOut <- isType ctx r sType
    return $ TermEither pTypeOut sTypeOut
isType _ _ TermTrivial = -- TrivialF
    return $ TermTrivial
isType _ _ TermAbsurd = -- AbsurdF
    return $ TermAbsurd
isType _ _ TermU = -- EL
    return $ TermU
isType _ _ _ = Nothing

typingCheck :: Context -> Renaming -> Term -> Value -> Maybe Term
typingCheck ctx r (TermCons a d) (SIGMA _ aType dType) = do -- SigmaI
    aOut <- typingCheck ctx r a aType
    dOut <- typingCheck ctx r d (valOfClosure dType (valInCtx ctx aOut))
    return $ TermCons aOut dOut
typingCheck ctx r (TermLambda lambdaX lambdaR) (PI _ argType rType) = do -- FunI
    let xPrime = fresh ctx lambdaX
    rOut <- typingCheck (bindFree ctx xPrime argType) (extendRenaming r lambdaX xPrime) lambdaR (valOfClosure rType (NEU argType (N_Var xPrime)))
    return $ TermLambda xPrime rOut
typingCheck _ _ TermListNil (LIST _) = -- ListI-1
    return $ TermListNil
typingCheck _ _ TermVecNil (VEC _ ZERO) = -- VecI-1
    return $ TermVecNil
typingCheck ctx r (TermVecColonColon e es) (VEC eType (ADD1 l)) = do -- VecI-2
    eOut <- typingCheck ctx r e eType
    esOut <- typingCheck ctx r es (VEC eType l)
    return $ TermVecColonColon eOut esOut
typingCheck ctx r (TermEqSame mid) (EQUAL xTypeVal fromVal toVal) = do -- EqI
    midOut <- typingCheck ctx r mid xTypeVal
    let midOutVal = valInCtx ctx midOut
    _ <- convert ctx xTypeVal fromVal midOutVal
    _ <- convert ctx xTypeVal toVal midOutVal
    return $ TermEqSame midOut
typingCheck ctx r (TermEitherLeft lt) (EITHER pType _) = do -- EitherI-1
    ltOut <- typingCheck ctx r lt pType
    return $ TermEitherLeft ltOut
typingCheck ctx r (TermEitherRight rt) (EITHER _ sType) = do -- EitherI-2
    rtOut <- typingCheck ctx r rt sType
    return $ TermEitherRight rtOut
typingCheck ctx r expr ty = do
    (The exprTypeOut exprOut) <- typingSynth ctx r expr
    _ <- sameType ctx (valInCtx ctx exprTypeOut) ty
    return $ exprOut

alphaEquiv :: Term -> Term -> Bool
alphaEquiv e1 e2 = alphaEquivImpl 0 [] [] e1 e2

alphaEquivImpl :: Int -> Bindings -> Bindings -> Term -> Term -> Bool
-- alphaEquivImpl lvl b1 b2 e1 e2 =
alphaEquivImpl lvl b1 b2 (TermPi x1 xType1 rType1) (TermPi x2 xType2 rType2) =
    (alphaEquivImpl lvl b1 b2 xType1 xType2) && (alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) rType1 rType2)
alphaEquivImpl lvl b1 b2 (TermSigma x1 xType1 rType1) (TermSigma x2 xType2 rType2) =
    (alphaEquivImpl lvl b1 b2 xType1 xType2) && (alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) rType1 rType2)
alphaEquivImpl lvl b1 b2 (TermLambda x1 body1) (TermLambda x2 body2) =
    alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) body1 body2
-- NOTE: This is the other half of the eta rule in `readBack`
alphaEquivImpl _ _ _ (TermThe (The TermAbsurd _)) (TermThe (The TermAbsurd _)) = True
alphaEquivImpl _ b1 b2 (TermVar x) (TermVar y) =
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
