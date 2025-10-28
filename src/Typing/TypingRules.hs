-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Typing.TypingRules where

import Utils.BasicTypes
import Parser.SyntacticTypes
import Typing.SemanticTypes
import Typing.Normalization
import Typing.CoreTypes

typingSynth :: Context -> Renaming -> SyntacticTerm -> Maybe The
typingSynth ctx r (SrcVar varName) = do -- Hypothesis
    let realVarName = rename r varName
    varTypeVal <- typingLookup ctx realVarName
    return $ The (readBackType ctx varTypeVal) (CoreVar realVarName)
typingSynth _ _ (SrcAtomLiteral sym) =  -- AtomI
    return $ The CoreAtom (CoreAtomLiteral sym)
typingSynth ctx r (SrcCar pr) = do -- SigmaE-1
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ carType _) ->
            return $ The (readBackType ctx carType) (CoreCar prOut)
        _ -> Nothing
typingSynth ctx r (SrcCdr pr) = do -- SigmaE-2
    (The prType prOut) <- typingSynth ctx r pr
    case valInCtx ctx prType of
        (SIGMA _ _ clos) ->
            return $ The (readBackType ctx (valOfClosure clos (doCar (valInCtx ctx prOut)))) (CoreCdr prOut)
        _ -> Nothing
typingSynth ctx r (SrcApplication func [arg]) = do -- FunE-1
    (The funcType funcOut) <- typingSynth ctx r func
    case valInCtx ctx funcType of
        (PI _ carType clos) -> do
            argOut <- typingCheck ctx r arg carType
            let argOutVal = valInCtx ctx argOut
            return $ The (readBackType ctx (valOfClosure clos argOutVal)) (CoreApplication funcOut argOut)
        _ -> Nothing
typingSynth ctx r (SrcApplication func args) = do -- FunE-2
    (The appFuncType appFuncOut) <- typingSynth ctx r (SrcApplication func (init args))
    case valInCtx ctx appFuncType of
        (PI _ carType clos) -> do
            argOut <- typingCheck ctx r (last args) carType
            let argOutVal = valInCtx ctx argOut
            return $ The (readBackType ctx (valOfClosure clos argOutVal)) (CoreApplication appFuncOut argOut)
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
typingSynth ctx r (SrcListColonColon h t) = do -- ListI-2
    (The headType headOut) <- typingSynth ctx r h
    esOut <- typingCheck ctx r t (valInCtx ctx (CoreList headType))
    return $ The (CoreList headType) (CoreListColonColon headOut esOut)
typingSynth ctx r (SrcRecList target base step) = do -- ListE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST elementType) -> do
            (The baseType baseOut) <- typingSynth ctx r base
            let baseTypeVal = valInCtx ctx baseType
            stepOut <- typingCheck ctx r step (PI "e" elementType (HO_CLOS (\_ -> PI "es" (LIST elementType) (HO_CLOS (\_ -> PI "ih" baseTypeVal (HO_CLOS (\_ -> baseTypeVal)))))))
            return $ The baseType (CoreRecList targetOut (The baseType baseOut) stepOut)
        _ -> Nothing
typingSynth ctx r (SrcIndList target motive base step) = do -- ListE-2
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (LIST elementType) -> do
            motiveOut <- typingCheck ctx r motive (PI "xs" (LIST elementType) (FO_CLOS (ctxToEnv ctx) "xs" CoreU))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal NIL)
            stepOut <- typingCheck ctx r step (PI "e" elementType (HO_CLOS (\e -> PI "es" (LIST elementType) (HO_CLOS (\es -> PI "ih" (doAp motiveOutVal es) (HO_CLOS (\_ -> doAp motiveOutVal (LIST_COLON_COLON e es))))))))
            return $ The (CoreApplication motiveOut targetOut) (CoreIndList targetOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (SrcHead es) = do -- VecE-1
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC elementTypeVal (ADD1 _)) ->
            return $ The (readBackType ctx elementTypeVal) (CoreHead esOut)
        _ -> Nothing
typingSynth ctx r (SrcTail es) = do -- VecE-2
    (The esTypeOut esOut) <- typingSynth ctx r es
    case valInCtx ctx esTypeOut of
        (VEC elementTypeVal (ADD1 lenMinus1)) ->
            return $ The (CoreVec (readBackType ctx elementTypeVal) (readBack ctx NAT lenMinus1)) (CoreTail esOut)
        _ -> Nothing
typingSynth ctx r (SrcIndVec len target motive base step) = do -- VecE-3
    lenOut <- typingCheck ctx r len NAT
    let lenOutVal = valInCtx ctx lenOut
    (The vecType vecOut) <- typingSynth ctx r target
    case valInCtx ctx vecType of
        (VEC elementTypeVal vecLenVal) -> do
            _ <- convert ctx NAT lenOutVal vecLenVal
            motiveOut <- typingCheck ctx r motive (PI "k" NAT (HO_CLOS (\k -> PI "es" (VEC elementTypeVal k) (HO_CLOS (\_ -> UNIVERSE)))))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp (doAp motiveOutVal ZERO) VECNIL)
            stepOut <- typingCheck ctx r step (indVecStepType elementTypeVal motiveOutVal)
            return $ The (CoreApplication motiveOut lenOut) (CoreIndVec lenOut vecOut motiveOut baseOut stepOut)
        _ -> Nothing
typingSynth ctx r (SrcEqReplace target motive base) = do -- EqE-1
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL eqTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "x" eqTypeVal (HO_CLOS (\_ -> UNIVERSE)))
            let motiveOutVal = valInCtx ctx motiveOut
            baseOut <- typingCheck ctx r base (doAp motiveOutVal fromVal)
            return $ The (readBackType ctx (doAp motiveOutVal toVal)) (CoreReplace targetOut motiveOut baseOut)
        _ -> Nothing
typingSynth ctx r (SrcEqCong target func) = do -- EqE-2
    (The targetType targetOut) <- typingSynth ctx r target
    (The funcType funcOut) <- typingSynth ctx r func
    case (valInCtx ctx targetType, valInCtx ctx funcType) of
        ((EQUAL eqTypeVal fromVal toVal), (PI _ domainTypeVal clos)) -> do
            _ <- sameType ctx eqTypeVal domainTypeVal
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
typingSynth ctx r (SrcEqSymm eqExpr) = do -- EqE-3
    (The eqExprType eqExprOut) <- typingSynth ctx r eqExpr
    case valInCtx ctx eqExprType of
        (EQUAL eqTypeVal fromVal toVal) ->
            return $ The (readBackType ctx (EQUAL eqTypeVal toVal fromVal)) (CoreSymm eqExprOut)
        _ -> Nothing
typingSynth ctx r (SrcEqTrans t1 t2) = do -- EqE-4
    (The t1Type t1Out) <- typingSynth ctx r t1
    (The t2Type t2Out) <- typingSynth ctx r t2
    case (valInCtx ctx t1Type, valInCtx ctx t2Type) of
        ((EQUAL eqType1Val fromVal midVal), (EQUAL eqType2Val mid2Val toVal)) -> do
            _ <- sameType ctx eqType1Val eqType2Val
            _ <- convert ctx eqType1Val midVal mid2Val
            return $ The (readBackType ctx (EQUAL eqType1Val fromVal toVal)) (CoreTrans t1Out t2Out)
        _ -> Nothing
typingSynth ctx r (SrcEqIndEq target motive base) = do -- EqE-5: Based Path Induction (aka: Parameter-variant of the J-eliminator)
    (The targetType targetOut) <- typingSynth ctx r target
    case valInCtx ctx targetType of
        (EQUAL eqTypeVal fromVal toVal) -> do
            motiveOut <- typingCheck ctx r motive (PI "to" eqTypeVal (HO_CLOS (\to -> PI "p" (EQUAL eqTypeVal fromVal to) (HO_CLOS (\_ -> UNIVERSE)))))
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
typingSynth ctx r (SrcSigma [(carName, carType)] cdrType) = do -- UI-2
    let newCarName = fresh ctx carName
    carTypeOut <- typingCheck ctx r carType UNIVERSE
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- typingCheck (bindFree ctx newCarName carTypeOutVal) (extendRenaming r carName newCarName) cdrType UNIVERSE
    return $ The CoreU (CoreSigma newCarName carTypeOut cdrTypeOut)
typingSynth ctx r (SrcSigma ((carName, carType):otherNamedFields) cdrType) = do -- UI-3
    let newCarName = fresh ctx carName
    carTypeOut <- typingCheck ctx r carType UNIVERSE
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- typingCheck (bindFree ctx newCarName carTypeOutVal) (extendRenaming r carName newCarName) (SrcSigma otherNamedFields cdrType) UNIVERSE
    return $ The CoreU (CoreSigma newCarName carTypeOut cdrTypeOut)
typingSynth ctx r (SrcPair carType cdrType) = do -- UI-4
-- NOTE: I believe there is a bug in the reference implementation of UI-4.
--  They call `fresh` below instead of `fresh-binder`, but they call `fresh-binder` for `Pair` in `is-type`.
--  The `isType` and `UI-4` implementations are otherwise identical in terms of the inference rules and implementations besides the return value (annotation vs type).
    let carName = freshBinder ctx cdrType "x"
    carTypeOut <- typingCheck ctx r carType UNIVERSE
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- typingCheck (bindFree ctx carName carTypeOutVal) r cdrType UNIVERSE
    return $ The CoreU (CoreSigma carName carTypeOut cdrTypeOut)
typingSynth ctx r (SrcPi [(argName, argType)] returnType) = do -- UI-5
    let newArgName = fresh ctx argName
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- typingCheck (bindFree ctx newArgName argTypeOutVal) (extendRenaming r argName newArgName) returnType UNIVERSE
    return $ The CoreU (CorePi newArgName argTypeOut returnTypeOut)
typingSynth ctx r (SrcPi ((argName, argType):otherNamedArgs) returnType) = do -- UI-6
    let newArgName = fresh ctx argName
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- typingCheck (bindFree ctx newArgName argTypeOutVal) (extendRenaming r argName newArgName) (SrcPi otherNamedArgs returnType) UNIVERSE
    return $ The CoreU (CorePi newArgName argTypeOut returnTypeOut)
typingSynth ctx r (SrcArrow argType [returnType]) = do -- UI-7
    let argName = freshBinder ctx returnType "x"
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- typingCheck (bindFree ctx argName argTypeOutVal) r returnType UNIVERSE
    return $ The CoreU (CorePi argName argTypeOut returnTypeOut)
typingSynth ctx r (SrcArrow argType (returnType1:returnType2:restOfReturnTypes)) = do -- UI-8
-- NOTE: `(SrcApplication returnType1 (returnType2:restOfReturnTypes))` is just a hack to allow us to pass a list of terms that we want to make sure the `argName` does not appear in.
    let argName = freshBinder ctx (SrcApplication returnType1 (returnType2:restOfReturnTypes)) "x"
    argTypeOut <- typingCheck ctx r argType UNIVERSE
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- typingCheck (bindFree ctx argName argTypeOutVal) r (SrcArrow returnType1 (returnType2:restOfReturnTypes)) UNIVERSE
    return $ The CoreU (CorePi argName argTypeOut returnTypeOut)
typingSynth _ _ SrcNat = -- UI-9
    return $ The CoreU CoreNat
typingSynth ctx r (SrcList elementType) = do -- UI-10
    elementTypeOut <- typingCheck ctx r elementType UNIVERSE
    return $ The CoreU (CoreList elementTypeOut)
typingSynth ctx r (SrcVec elementType len) = do -- UI-11
    elementTypeOut <- typingCheck ctx r elementType UNIVERSE
    lOut <- typingCheck ctx r len NAT
    return $ The CoreU (CoreVec elementTypeOut lOut)
typingSynth ctx r (SrcEq eqType from to) = do -- UI-12
    eqTypeOut <- typingCheck ctx r eqType UNIVERSE
    let eqTypeOutVal = valInCtx ctx eqTypeOut
    fromOut <- typingCheck ctx r from eqTypeOutVal
    toOut <- typingCheck ctx r to eqTypeOutVal
    return $ The CoreU (CoreEq eqTypeOut fromOut toOut)
typingSynth ctx r (SrcEither leftType rightType) = do -- UI-13
    leftTypeOut <- typingCheck ctx r leftType UNIVERSE
    rightTypeOut <- typingCheck ctx r rightType UNIVERSE
    return $ The CoreU (CoreEither leftTypeOut rightTypeOut)
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
isType ctx r (SrcSigma [(carName, carType)] cdrType) = do -- SigmaF-1
    let newCarName = fresh ctx carName
    carTypeOut <- isType ctx r carType
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- isType (bindFree ctx newCarName carTypeOutVal) (extendRenaming r carName newCarName) cdrType
    return $ CoreSigma newCarName carTypeOut cdrTypeOut
isType ctx r (SrcSigma ((carName, carType):otherNamedFields) cdrType) = do -- SigmaF-2
    let newCarName = fresh ctx carName
    carTypeOut <- isType ctx r carType
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- isType (bindFree ctx newCarName carTypeOutVal) (extendRenaming r carName newCarName) (SrcSigma otherNamedFields cdrType)
    return $ CoreSigma newCarName carTypeOut cdrTypeOut
isType ctx r (SrcPair carType cdrType) = do -- SigmaF-Pair
    let carName = freshBinder ctx cdrType "x"
    carTypeOut <- isType ctx r carType
    let carTypeOutVal = valInCtx ctx carTypeOut
    cdrTypeOut <- isType (bindFree ctx carName carTypeOutVal) r cdrType
    return $ CoreSigma carName carTypeOut cdrTypeOut
isType ctx r (SrcPi [(argName, argType)] returnType) = do -- FunF-1
    let newArgName = fresh ctx argName
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- isType (bindFree ctx newArgName argTypeOutVal) (extendRenaming r argName newArgName) returnType
    return $ CorePi newArgName argTypeOut returnTypeOut
isType ctx r (SrcPi ((argName, argType):otherNamedArgs) returnType) = do -- FunF-2
    let newArgName = fresh ctx argName
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- isType (bindFree ctx newArgName argTypeOutVal) (extendRenaming r argName newArgName) (SrcPi otherNamedArgs returnType)
    return $ CorePi newArgName argTypeOut returnTypeOut
isType ctx r (SrcArrow argType [returnType]) = do -- FunFArrow-1
    let argName = freshBinder ctx returnType "x"
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- isType (bindFree ctx argName argTypeOutVal) r returnType
    return $ CorePi argName argTypeOut returnTypeOut
isType ctx r (SrcArrow argType (returnType1:returnType2:restOfReturnTypes)) = do -- FunFArrow-2
-- NOTE: `(SrcApplication returnType1 (returnType2:restOfReturnTypes))` is just a hack to allow us to pass a list of terms that we want to make sure the `argName` does not appear in.
    let argName = freshBinder ctx (SrcApplication returnType1 (returnType2:restOfReturnTypes)) "x"
    argTypeOut <- isType ctx r argType
    let argTypeOutVal = valInCtx ctx argTypeOut
    returnTypeOut <- isType (bindFree ctx argName argTypeOutVal) r (SrcArrow returnType1 (returnType2:restOfReturnTypes))
    return $ CorePi argName argTypeOut returnTypeOut
isType _ _ SrcNat = -- NatF
    return $ CoreNat
isType ctx r (SrcList elementType) = do -- ListF
    elementTypeOut <- isType ctx r elementType
    return $ CoreList elementTypeOut
isType ctx r (SrcVec elementType len) = do -- VecF
    elementTypeOut <- isType ctx r elementType
    lenOut <- typingCheck ctx r len NAT
    return $ CoreVec elementTypeOut lenOut
isType ctx r (SrcEq eqType from to) = do -- EqF
    eqTypeOut <- isType ctx r eqType
    let eqTypeOutVal = valInCtx ctx eqTypeOut
    fromOut <- typingCheck ctx r from eqTypeOutVal
    toOut <- typingCheck ctx r to eqTypeOutVal
    return $ CoreEq eqTypeOut fromOut toOut
isType ctx r (SrcEither leftType rightType) = do -- EitherF
    leftTypeOut <- isType ctx r leftType
    rightTypeOut <- isType ctx r rightType
    return $ CoreEither leftTypeOut rightTypeOut
isType _ _ SrcTrivial = -- TrivialF
    return $ CoreTrivial
isType _ _ SrcAbsurd = -- AbsurdF
    return $ CoreAbsurd
isType _ _ SrcU = -- EL
    return $ CoreU
isType ctx r expr = typingCheck ctx r expr UNIVERSE

typingCheck :: Context -> Renaming -> SyntacticTerm -> Value -> Maybe CoreTerm
typingCheck ctx r (SrcCons car cdr) (SIGMA _ carType cdrType) = do -- SigmaI
    carOut <- typingCheck ctx r car carType
    cdrOut <- typingCheck ctx r cdr (valOfClosure cdrType (valInCtx ctx carOut))
    return $ CoreCons carOut cdrOut
typingCheck ctx r (SrcLambda [argName] lambdaBody) (PI _ argType returnType) = do -- FunI-1
    let newArgName = fresh ctx argName
    returnOut <- typingCheck (bindFree ctx newArgName argType) (extendRenaming r argName newArgName) lambdaBody (valOfClosure returnType (NEU argType (N_Var newArgName)))
    return $ CoreLambda newArgName returnOut
typingCheck ctx r (SrcLambda (argName:otherArgNames) lambdaBody) typeVal = -- FunI-2
    typingCheck ctx r (SrcLambda [argName] (SrcLambda otherArgNames lambdaBody)) typeVal
typingCheck _ _ SrcListNil (LIST _) = -- ListI-1
    return $ CoreListNil
typingCheck _ _ SrcVecNil (VEC _ ZERO) = -- VecI-1
    return $ CoreVecNil
typingCheck ctx r (SrcVecColonColon h t) (VEC elementType (ADD1 lenMinus1)) = do -- VecI-2
    hOut <- typingCheck ctx r h elementType
    tOut <- typingCheck ctx r t (VEC elementType lenMinus1)
    return $ CoreVecColonColon hOut tOut
typingCheck ctx r (SrcEqSame mid) (EQUAL eqTypeVal fromVal toVal) = do -- EqI
    midOut <- typingCheck ctx r mid eqTypeVal
    let midOutVal = valInCtx ctx midOut
    _ <- convert ctx eqTypeVal fromVal midOutVal
    _ <- convert ctx eqTypeVal toVal midOutVal
    return $ CoreEqSame midOut
typingCheck ctx r (SrcEitherLeft left) (EITHER leftType _) = do -- EitherI-1
    leftOut <- typingCheck ctx r left leftType
    return $ CoreEitherLeft leftOut
typingCheck ctx r (SrcEitherRight right) (EITHER _ rightType) = do -- EitherI-2
    rightOut <- typingCheck ctx r right rightType
    return $ CoreEitherRight rightOut
typingCheck ctx r expr ty = do
    (The exprTypeOut exprOut) <- typingSynth ctx r expr
    _ <- sameType ctx (valInCtx ctx exprTypeOut) ty
    return $ exprOut

alphaEquiv :: CoreTerm -> CoreTerm -> Bool
alphaEquiv e1 e2 = alphaEquivImpl 0 [] [] e1 e2

alphaEquivImpl :: Int -> Bindings -> Bindings -> CoreTerm -> CoreTerm -> Bool
alphaEquivImpl lvl b1 b2 (CorePi argName1 argType1 returnType1) (CorePi argName2 argType2 returnType2) =
    (alphaEquivImpl lvl b1 b2 argType1 argType2) && (alphaEquivImpl (lvl+1) (bind b1 argName1 lvl) (bind b2 argName2 lvl) returnType1 returnType2)
alphaEquivImpl lvl b1 b2 (CoreSigma argName1 argType1 returnType1) (CoreSigma argName2 argType2 returnType2) =
    (alphaEquivImpl lvl b1 b2 argType1 argType2) && (alphaEquivImpl (lvl+1) (bind b1 argName1 lvl) (bind b2 argName2 lvl) returnType1 returnType2)
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
alphaEquivImpl lvl b1 b2 (CoreThe (The t1 e1)) (CoreThe (The t2 e2)) =
    (alphaEquivImpl lvl b1 b2 t1 t2) && (alphaEquivImpl lvl b1 b2 e1 e2)
alphaEquivImpl _ _ _ CoreAtom CoreAtom = True
alphaEquivImpl _ _ _ (CoreAtomLiteral a1) (CoreAtomLiteral a2) = a1 == a2
alphaEquivImpl lvl b1 b2 (CoreCons car1 cdr1) (CoreCons car2 cdr2) =
    (alphaEquivImpl lvl b1 b2 car1 car2) && (alphaEquivImpl lvl b1 b2 cdr1 cdr2)
alphaEquivImpl lvl b1 b2 (CoreCar p1) (CoreCar p2) =
    alphaEquivImpl lvl b1 b2 p1 p2
alphaEquivImpl lvl b1 b2 (CoreCdr p1) (CoreCdr p2) =
    alphaEquivImpl lvl b1 b2 p1 p2
alphaEquivImpl lvl b1 b2 (CoreApplication f arg1) (CoreApplication g arg2) =
    (alphaEquivImpl lvl b1 b2 f g) && (alphaEquivImpl lvl b1 b2 arg1 arg2)
alphaEquivImpl _ _ _ CoreNat CoreNat = True
alphaEquivImpl _ _ _ CoreNatZero CoreNatZero = True
alphaEquivImpl lvl b1 b2 (CoreNatAdd1 n1) (CoreNatAdd1 n2) =
    alphaEquivImpl lvl b1 b2 n1 n2
alphaEquivImpl lvl b1 b2 (CoreWhichNat target1 (The baseType1 baseExpr1) step1) (CoreWhichNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIterNat target1 (The baseType1 baseExpr1) step1) (CoreIterNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreRecNat target1 (The baseType1 baseExpr1) step1) (CoreRecNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIndNat target1 motive1 base1 step1) (CoreIndNat target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreList elementType1) (CoreList elementType2) =
    alphaEquivImpl lvl b1 b2 elementType1 elementType2
alphaEquivImpl _ _ _ CoreListNil CoreListNil = True
alphaEquivImpl lvl b1 b2 (CoreListColonColon h1 t1) (CoreListColonColon h2 t2) =
    (alphaEquivImpl lvl b1 b2 h1 h2) && (alphaEquivImpl lvl b1 b2 t1 t2)
alphaEquivImpl lvl b1 b2 (CoreRecList target1 (The baseType1 baseExpr1) step1) (CoreRecList target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIndList target1 motive1 base1 step1) (CoreIndList target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreVec elementType1 len1) (CoreVec elementType2 len2) =
    (alphaEquivImpl lvl b1 b2 elementType1 elementType2) && (alphaEquivImpl lvl b1 b2 len1 len2)
alphaEquivImpl _ _ _ CoreVecNil CoreVecNil = True
alphaEquivImpl lvl b1 b2 (CoreVecColonColon h1 t1) (CoreVecColonColon h2 t2) =
    (alphaEquivImpl lvl b1 b2 h1 h2) && (alphaEquivImpl lvl b1 b2 t1 t2)
alphaEquivImpl lvl b1 b2 (CoreHead vec1) (CoreHead vec2) =
    alphaEquivImpl lvl b1 b2 vec1 vec2
alphaEquivImpl lvl b1 b2 (CoreTail vec1) (CoreTail vec2) =
    alphaEquivImpl lvl b1 b2 vec1 vec2
alphaEquivImpl lvl b1 b2 (CoreIndVec n1 target1 motive1 base1 step1) (CoreIndVec n2 target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 n1 n2) && (alphaEquivImpl lvl b1 b2 target1 target2)
    && (alphaEquivImpl lvl b1 b2 motive1 motive2) && (alphaEquivImpl lvl b1 b2 base1 base2)
    && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreEq eqType1 from1 to1) (CoreEq eqType2 from2 to2) =
    (alphaEquivImpl lvl b1 b2 eqType1 eqType2) && (alphaEquivImpl lvl b1 b2 from1 from2)
    && (alphaEquivImpl lvl b1 b2 to1 to2)
alphaEquivImpl lvl b1 b2 (CoreEqSame expr1) (CoreEqSame expr2) =
    alphaEquivImpl lvl b1 b2 expr1 expr2
alphaEquivImpl lvl b1 b2 (CoreSymm expr1) (CoreSymm expr2) =
    alphaEquivImpl lvl b1 b2 expr1 expr2
alphaEquivImpl lvl b1 b2 (CoreCong target1 coDomainType1 func1) (CoreCong target2 coDomainType2 func2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 coDomainType1 coDomainType2)
    && (alphaEquivImpl lvl b1 b2 func1 func2)
alphaEquivImpl lvl b1 b2 (CoreReplace target1 motive1 base1) (CoreReplace target2 motive2 base2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2)
alphaEquivImpl lvl b1 b2 (CoreTrans fromMid1 midTo1) (CoreTrans fromMid2 midTo2) =
    (alphaEquivImpl lvl b1 b2 fromMid1 fromMid2) && (alphaEquivImpl lvl b1 b2 midTo1 midTo2)
alphaEquivImpl lvl b1 b2 (CoreIndEq target1 motive1 base1) (CoreIndEq target2 motive2 base2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2)
alphaEquivImpl lvl b1 b2 (CoreEither leftType1 rightType1) (CoreEither leftType2 rightType2) =
    (alphaEquivImpl lvl b1 b2 leftType1 leftType2) && (alphaEquivImpl lvl b1 b2 rightType1 rightType2)
alphaEquivImpl lvl b1 b2 (CoreEitherLeft left1) (CoreEitherLeft left2) =
    alphaEquivImpl lvl b1 b2 left1 left2
alphaEquivImpl lvl b1 b2 (CoreEitherRight right1) (CoreEitherRight right2) =
    alphaEquivImpl lvl b1 b2 right1 right2
alphaEquivImpl lvl b1 b2 (CoreIndEither target1 base1 leftStep1 rightStep1) (CoreIndEither target2 base2 leftStep2 rightStep2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 base1 base2)
    && (alphaEquivImpl lvl b1 b2 leftStep1 leftStep2) && (alphaEquivImpl lvl b1 b2 rightStep1 rightStep2)
alphaEquivImpl _ _ _ CoreTrivial CoreTrivial = True
alphaEquivImpl _ _ _ CoreTrivialSole CoreTrivialSole = True
alphaEquivImpl _ _ _ CoreAbsurd CoreAbsurd = True
alphaEquivImpl lvl b1 b2 (CoreIndAbsurd target1 motive1) (CoreIndAbsurd target2 motive2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
alphaEquivImpl _ _ _ CoreU CoreU = True
alphaEquivImpl _ _ _ _ _ = False -- mismatched `CoreTerm` constructors

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
