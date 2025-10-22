-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Typing.Normalization where

import Typing.SemanticTypes
import Utils.BasicTypes
import Typing.CoreTypes

-- NOTE: We make use of Haskell's built-in laziness. So we call the function directly and get the Value, but Haskell will automagically memoize it
--     NOTE: This allows use to get rid of all the box and DELAY boilerplate/logic that is present in the reference implementation which is written in Racket

extendEnv :: Env -> Name -> Value -> Env
extendEnv env x v = ((x, v):env)

valOfClosure :: Closure -> Value -> Value
valOfClosure closure val =
    case closure of
        (FO_CLOS env argName expr) -> reflect (extendEnv env argName val) expr
        (HO_CLOS fun) -> fun val

doAp :: Value -> Value -> Value
doAp ratorVal randVal =
    case ratorVal of
        LAM _ body -> valOfClosure body randVal
        NEU (PI _ aType body) ne ->
            NEU (valOfClosure body randVal) (N_Ap ne (THE aType randVal))
        _ -> error "There is a logic error in the implementation where `doAp` has been called on an invalid target"

doWhichNat :: Value -> Value -> Value -> Value -> Value
doWhichNat targetVal baseTypeVal baseVal stepVal =
    case targetVal of
        ZERO -> baseVal
        (ADD1 nMinus1Val) -> doAp
                                stepVal
                                nMinus1Val
        (NEU NAT ne) ->
            NEU baseTypeVal
                (N_Which_Nat
                    ne
                    (THE baseTypeVal baseVal)
                    (THE (PI "n" NAT (HO_CLOS (\_ -> baseTypeVal)))
                        stepVal))
        _ -> error "There is a logic error in the implementation where `doWhichNat` has been called on an invalid target"
doIterNat :: Value -> Value -> Value -> Value -> Value
doIterNat targetVal baseTypeVal baseVal stepVal =
    case targetVal of
        ZERO -> baseVal
        (ADD1 nMinus1Val) -> doAp
                                stepVal
                                (doIterNat nMinus1Val baseTypeVal baseVal stepVal)
        (NEU NAT ne) ->
            NEU baseTypeVal
                (N_Iter_Nat
                    ne
                    (THE baseTypeVal baseVal)
                    (THE (PI "n" baseTypeVal (HO_CLOS (\_ -> baseTypeVal)))
                        stepVal)
                )
        _ -> error "There is a logic error in the implementation where `doIterNat` has been called on an invalid target"
doRecNat :: Value -> Value -> Value -> Value -> Value
doRecNat targetVal baseTypeVal baseVal stepVal =
    case targetVal of
        ZERO -> baseVal
        (ADD1 nMinus1Val) -> doAp
                                (doAp stepVal nMinus1Val)
                                (doRecNat nMinus1Val baseTypeVal baseVal stepVal)
        (NEU NAT ne) ->
            NEU baseTypeVal
                (N_Rec_Nat ne
                    (THE baseTypeVal baseVal)
                    (THE (PI "nMinus1" NAT (HO_CLOS (\_ ->
                            PI "ih" baseTypeVal (HO_CLOS (\_ -> baseTypeVal)))))
                        stepVal))
        _ -> error "There is a logic error in the implementation where `doRecNat` has been called on an invalid target"
doIndNat :: Value -> Value -> Value -> Value -> Value
doIndNat targetVal motiveVal baseVal stepVal =
    case targetVal of
        ZERO -> baseVal
        (ADD1 nMinus1Val) -> doAp
                                (doAp stepVal nMinus1Val)
                                (doIndNat nMinus1Val motiveVal baseVal stepVal)
        (NEU NAT ne) ->
            NEU (doAp motiveVal targetVal)
                (N_Ind_Nat ne
                    (THE (PI "x" NAT (HO_CLOS (\_ -> UNIVERSE)))
                        motiveVal)
                    (THE (doAp motiveVal ZERO) baseVal)
                    (THE (PI "nMinus1" NAT (HO_CLOS (\nMinus1 ->
                            PI "ih" (doAp motiveVal nMinus1) (HO_CLOS (\_ ->
                                (doAp motiveVal (ADD1 nMinus1)))))))
                        stepVal))
        _ -> error "There is a logic error in the implementation where `doIndNat` has been called on an invalid target"

doCar :: Value -> Value
doCar pVal =
    case pVal of
        (CONS a _) -> a
        (NEU (SIGMA _ aType _) ne) -> NEU aType (N_Car ne)
        _ -> error "There is a logic error in the implementation where `doCar` has been called on an invalid target"
doCdr :: Value -> Value
doCdr pVal =
    case pVal of
        (CONS _ d) -> d
        (NEU (SIGMA _ _ dType) ne) ->
            NEU 
                (valOfClosure dType (doCar pVal))
                (N_Cdr ne)
        _ -> error "There is a logic error in the implementation where `doCdr` has been called on an invalid target"

doRecList :: Value -> Value -> Value -> Value -> Value
doRecList targetVal baseTypeVal baseVal stepVal =
    case targetVal of
        NIL -> baseVal
        (LIST_COLON_COLON h t) -> doAp
                                        (doAp (doAp stepVal h) t)
                                        (doRecList t baseTypeVal baseVal stepVal)
        (NEU (LIST elementType) ne) ->
            NEU baseTypeVal
                (N_Rec_List ne
                    (THE baseTypeVal baseVal)
                    (THE (PI "h" elementType (HO_CLOS (\_ ->
                        PI "t" (LIST elementType) (HO_CLOS (\_ ->
                            PI "ih" baseTypeVal (HO_CLOS (\_ ->
                                baseTypeVal)))))))
                        stepVal))
        _ -> error "There is a logic error in the implementation where `doRecList` has been called on an invalid target"
doIndList :: Value -> Value -> Value -> Value -> Value
doIndList targetVal motiveVal baseVal stepVal =
    case targetVal of
        NIL -> baseVal
        (LIST_COLON_COLON h t) ->
            doAp
                (doAp (doAp stepVal h) t)
                (doIndList t motiveVal baseVal stepVal)
        (NEU (LIST elementType) ne) ->
            let motiveTypeVal = PI "xs" (LIST elementType) (HO_CLOS (\_ -> UNIVERSE)) in
                NEU
                    (doAp motiveVal targetVal)
                    (N_Ind_List ne
                        (THE motiveTypeVal motiveVal)
                        (THE (doAp motiveVal NIL) baseVal)
                        (THE (PI "h" elementType (HO_CLOS (\h ->
                            PI "t" (LIST elementType) (HO_CLOS (\t ->
                                PI "ih" (doAp motiveVal t) (HO_CLOS (\_ ->
                                    (doAp motiveVal (LIST_COLON_COLON h t))
                                )))))))
                            stepVal))
        _ -> error "There is a logic error in the implementation where `doIndList` has been called on an invalid target"

doIndAbsurd :: Value -> Value -> Value
doIndAbsurd targetVal motiveVal =
    case targetVal of
        (NEU ABSURD ne) ->
            NEU motiveVal
                (N_Ind_Absurd ne (THE UNIVERSE motiveVal))
        _ -> error "There is a logic error in the implementation where `doIndAbsurd` has been called on an invalid target"

doReplace :: Value -> Value -> Value -> Value
doReplace targetVal motiveVal baseVal =
    case targetVal of
        (SAME _) -> baseVal
        (NEU (EQUAL aTypeVal fromVal toVal) ne) ->
            NEU (doAp motiveVal toVal)
                (N_Replace ne
                    (THE (PI "x" aTypeVal (HO_CLOS (\_ -> UNIVERSE))) motiveVal)
                    (THE (doAp motiveVal fromVal) baseVal))
        _ -> error "There is a logic error in the implementation where `doReplace` has been called on an invalid target"
doTrans :: Value -> Value -> Value
doTrans target1Val target2Val =
    case (target1Val, target2Val) of
        ((SAME val), (SAME _)) -> SAME val
        ((SAME fromVal), (NEU (EQUAL aTypeVal _ toVal) ne2)) ->
            NEU
                (EQUAL aTypeVal fromVal toVal)
                (N_Trans2
                                (THE (EQUAL aTypeVal fromVal fromVal) (SAME fromVal))
                                ne2)
        ((NEU (EQUAL aTypeVal fromVal _) ne1), (SAME toVal)) ->
            NEU
                (EQUAL aTypeVal fromVal toVal)
                (N_Trans1
                                ne1
                                (THE (EQUAL aTypeVal toVal toVal) (SAME toVal)))
        (NEU (EQUAL aTypeVal fromVal _) ne1, (NEU (EQUAL _ _ toVal) ne2)) ->
            NEU
                (EQUAL aTypeVal fromVal toVal)
                (N_Trans12 ne1 ne2)
        _ -> error "There is a logic error in the implementation where `doTrans` has been called on an invalid target"
doCong :: Value -> Value -> Value -> Value
doCong targetVal coDomainTypeVal funcVal =
    case targetVal of
        (SAME val) -> SAME (doAp funcVal val)
        (NEU (EQUAL domainTypeVal fromVal toVal) ne) ->
            NEU
                (EQUAL coDomainTypeVal (doAp funcVal fromVal) (doAp funcVal toVal))
                (N_Cong ne (THE (PI "x" domainTypeVal (HO_CLOS (\_ -> coDomainTypeVal))) funcVal))
        _ -> error "There is a logic error in the implementation where `doCong` has been called on an invalid target"
doSymm :: Value -> Value
doSymm targetVal =
    case targetVal of
        (SAME val) -> (SAME val)
        (NEU (EQUAL aTypeVal fromVal toVal) ne) ->
            (NEU (EQUAL aTypeVal toVal fromVal) (N_Symm ne))
        _ -> error "There is a logic error in the implementation where `doSymm` has been called on an invalid target"
doIndEq :: Value -> Value -> Value -> Value
doIndEq targetVal motiveVal baseVal =
    case targetVal of
        (SAME _) -> baseVal
        (NEU (EQUAL aTypeVal fromVal toVal) ne) ->
            NEU
                (doAp (doAp motiveVal toVal) targetVal)
                (N_Ind_Eq ne
                    (THE
                        (PI "to" aTypeVal (HO_CLOS (\to ->
                            PI "p" (EQUAL aTypeVal fromVal to) (HO_CLOS (\_ ->
                                UNIVERSE)))))
                        motiveVal)
                    (THE
                        (doAp (doAp motiveVal fromVal)
                            (SAME fromVal))
                        baseVal))
        _ -> error "There is a logic error in the implementation where `doIndEq` has been called on an invalid target"

doHead :: Value -> Value
doHead targetVal =
    case targetVal of
        (VEC_COLON_COLON hVal _) -> hVal
        (NEU (VEC elementTypeVal (ADD1 _)) ne) ->
            NEU elementTypeVal (N_Head ne)
        _ -> error "There is a logic error in the implementation where `doHead` has been called on an invalid target"
doTail :: Value -> Value
doTail targetVal =
    case targetVal of
        (VEC_COLON_COLON _ tailVal) -> tailVal
        (NEU (VEC elementTypeVal (ADD1 lenMinus1Val)) ne) ->
            NEU (VEC elementTypeVal lenMinus1Val) (N_Tail ne)
        _ -> error "There is a logic error in the implementation where `doTail` has been called on an invalid target"

indVecStepType :: Value -> Value -> Value
indVecStepType elementTypeVal motiveVal =
    PI "k" NAT (HO_CLOS (\k ->
        PI "e" elementTypeVal (HO_CLOS (\e ->
            PI "es" (VEC elementTypeVal k) (HO_CLOS (\es ->
                PI "ih" (doAp (doAp motiveVal k) es) (HO_CLOS (\_ ->
                    doAp (doAp motiveVal (ADD1 k)) (VEC_COLON_COLON e es)))))))))
doIndVec :: Value -> Value -> Value -> Value -> Value -> Value
doIndVec lenVal vecVal motiveVal baseVal stepVal =
    case (lenVal, vecVal) of
        (ZERO, VECNIL) -> baseVal
        ((ADD1 lenMinus1Val), (VEC_COLON_COLON h t)) ->
            doAp (doAp (doAp (doAp stepVal lenMinus1Val) h) t) -- NOTE: For some reason the reference implementation uses `(do-tail vec-v)` on this line instead of `t`
                (doIndVec lenMinus1Val t motiveVal baseVal stepVal)
        ((NEU (NAT) len), (NEU (VEC elementTypeVal _) ne)) ->
            NEU
                (doAp (doAp motiveVal lenVal) vecVal)
                (N_Ind_Vec12
                    len
                    ne
                    (THE (PI "k" NAT (HO_CLOS (\k ->
                        PI "es" (VEC elementTypeVal k) (HO_CLOS (\_ ->
                            UNIVERSE)))))
                        motiveVal)
                    (THE (doAp (doAp motiveVal ZERO) VECNIL) baseVal)
                    (THE (indVecStepType elementTypeVal motiveVal) stepVal))
        (_, (NEU (VEC elementTypeVal _) ne)) ->
            NEU
                (doAp (doAp motiveVal lenVal) vecVal)
                (N_Ind_Vec2
                    (THE NAT lenVal)
                    ne
                    (THE (PI "k" NAT (HO_CLOS (\k ->
                        PI "es" (VEC elementTypeVal k) (HO_CLOS (\_ ->
                            UNIVERSE)))))
                        motiveVal)
                    (THE (doAp (doAp motiveVal ZERO) VECNIL) baseVal)
                    (THE (indVecStepType elementTypeVal motiveVal) stepVal))
        _ -> error "There is a logic error in the implementation where `doIndVec` has been called on an invalid target"

doIndEither :: Value -> Value -> Value -> Value -> Value
doIndEither target motive l r =
    case target of
        (LEFT x) -> doAp l x
        (RIGHT x) -> doAp r x
        (NEU (EITHER leftTypeVal rightTypeVal) ne) ->
            let motiveTypeVal = PI "x" (EITHER leftTypeVal rightTypeVal) (HO_CLOS (\_ -> UNIVERSE)) in
                NEU
                    (doAp motive target)
                    (N_Ind_Either
                        ne
                        (THE motiveTypeVal motive)
                        (THE
                            (PI "x" leftTypeVal (HO_CLOS (\x ->
                                doAp motive (LEFT x))))
                                l)
                        (THE
                            (PI "x" rightTypeVal (HO_CLOS (\x ->
                                doAp motive (RIGHT x))))
                            r))
        _ -> error "There is a logic error in the implementation where `doIndEither` has been called on an invalid target"

varVal :: Env -> Name -> Value
varVal [] x = error $ "Variable " ++ x ++ " not in the Env!"
varVal (ctxHead : ctxTail) x
    | fst ctxHead == x  = snd ctxHead
    | otherwise         = varVal ctxTail x

reflect :: Env -> CoreTerm -> Value
reflect env (CoreThe (The _ expr)) =
    reflect env expr
reflect _ CoreU = UNIVERSE
reflect _ CoreNat = NAT
reflect _ CoreNatZero = ZERO
reflect env (CoreNatAdd1 n) = ADD1 (reflect env n)
reflect env (CorePi x aType bType) =
    let aTypeVal = reflect env aType
    in PI x aTypeVal (FO_CLOS env x bType)
reflect env (CoreLambda x bType) =
    LAM x (FO_CLOS env x bType)
reflect env (CoreWhichNat target (The baseType base) step) =
    doWhichNat (reflect env target) (reflect env baseType) (reflect env base) (reflect env step)
reflect env (CoreIterNat target (The baseType base) step) =
    doIterNat (reflect env target) (reflect env baseType) (reflect env base) (reflect env step)
reflect env (CoreRecNat target (The baseType base) step) =
    doRecNat (reflect env target) (reflect env baseType) (reflect env base) (reflect env step)
reflect env (CoreIndNat target motive base step) =
    doIndNat (reflect env target) (reflect env motive) (reflect env base) (reflect env step)
reflect _ (CoreAtom) = ATOM
reflect env (CoreSigma x aType dType) =
    let aTypeVal = reflect env aType
    in SIGMA x aTypeVal (FO_CLOS env x dType)
reflect env (CoreCons a d) =
    CONS (reflect env a) (reflect env d)
reflect env (CoreCar p) =
    doCar (reflect env p)
reflect env (CoreCdr p) =
    doCdr (reflect env p)
reflect _ (CoreAtomLiteral a) = QUOTE a
reflect _ CoreTrivial = TRIVIAL
reflect _ CoreTrivialSole = SOLE
reflect _ CoreListNil = NIL
reflect env (CoreListColonColon h t) =
    LIST_COLON_COLON (reflect env h) (reflect env t)
reflect env (CoreList elementType) =
    LIST (reflect env elementType)
reflect env (CoreIndList target motive base step) =
    doIndList (reflect env target) (reflect env motive) (reflect env base) (reflect env step)
reflect env (CoreRecList target (The baseType base) step) =
    doRecList (reflect env target) (reflect env baseType) (reflect env base) (reflect env step)
reflect _ CoreAbsurd = ABSURD
reflect env (CoreIndAbsurd target motive) =
    doIndAbsurd (reflect env target) (reflect env motive)
reflect env (CoreEq aType from to) =
    EQUAL (reflect env aType) (reflect env from) (reflect env to)
reflect env (CoreEqSame e) =
    SAME (reflect env e)
reflect env (CoreReplace target motive base) =
    doReplace (reflect env target) (reflect env motive) (reflect env base)
reflect env (CoreTrans p1 p2) =
    doTrans (reflect env p1) (reflect env p2)
reflect env (CoreCong p1 p2 p3) =
    doCong (reflect env p1) (reflect env p2) (reflect env p3)
reflect env (CoreSymm p) =
    doSymm (reflect env p)
reflect env (CoreIndEq target motive base) =
    doIndEq (reflect env target) (reflect env motive) (reflect env base)
reflect env (CoreVec elementType len) =
    VEC (reflect env elementType) (reflect env len)
reflect _ CoreVecNil = VECNIL
reflect env (CoreVecColonColon h t) =
    VEC_COLON_COLON (reflect env h) (reflect env t)
reflect env (CoreHead es) =
    doHead (reflect env es)
reflect env (CoreTail es) =
    doTail (reflect env es)
reflect env (CoreIndVec len es mot base step) =
    doIndVec (reflect env len) (reflect env es) (reflect env mot) (reflect env base) (reflect env step)
reflect env (CoreEither left right) =
    EITHER (reflect env left) (reflect env right)
reflect env (CoreEitherLeft left) =
    LEFT (reflect env left)
reflect env (CoreEitherRight right) =
    RIGHT (reflect env right)
reflect env (CoreIndEither target motive left right) =
    doIndEither (reflect env target) (reflect env motive) (reflect env left) (reflect env right)
reflect env (CoreApplication rator rand) =
    doAp (reflect env rator) (reflect env rand)
reflect env (CoreVar x) =
    varVal env x

extendRenaming :: Renaming -> Name -> Name -> Renaming
extendRenaming r from to = ((from, to):r)

valInCtx :: Context -> CoreTerm -> Value
valInCtx ctx expr = reflect (ctxToEnv ctx) expr

ctxToEnv :: Context -> Env
ctxToEnv ((x, Def _ val):ctxTail) =
    [(x, val)] ++ (ctxToEnv ctxTail)
ctxToEnv ((x, Free typeVal):ctxTail) =
    [(x, NEU typeVal (N_Var x))] ++ (ctxToEnv ctxTail)
ctxToEnv ((_, Claim _):ctxTail) =
    ctxToEnv ctxTail
ctxToEnv [] = []

readBackType :: Context -> Value -> CoreTerm
readBackType _ UNIVERSE = CoreU
readBackType _ NAT = CoreNat
readBackType ctx (PI x xTypeVal clos) =
    let xTypeTerm       = readBackType ctx xTypeVal
        xPrime          = fresh ctx x
        ctxUnderXPrime  = bindFree ctx xPrime xTypeVal
    in (CorePi xPrime xTypeTerm (readBackType ctxUnderXPrime (valOfClosure clos (NEU xTypeVal (N_Var xPrime)))))
readBackType _ ATOM = CoreAtom
readBackType ctx (SIGMA x xTypeVal clos) =
    let xTypeTerm       = readBackType ctx xTypeVal
        xPrime          = fresh ctx x
        ctxUnderXPrime  = bindFree ctx xPrime xTypeVal
    in (CoreSigma xPrime xTypeTerm (readBackType ctxUnderXPrime (valOfClosure clos (NEU xTypeVal (N_Var xPrime)))))
readBackType _ TRIVIAL = CoreTrivial
readBackType ctx (LIST eTypeVal) = (CoreList (readBackType ctx eTypeVal))
readBackType _ ABSURD = CoreAbsurd
readBackType ctx (EQUAL xTypeVal fromVal toVal) =
    CoreEq (readBackType ctx xTypeVal) (readBack ctx xTypeVal fromVal) (readBack ctx xTypeVal toVal)
readBackType ctx (VEC eTypeVal lenVal) =
    CoreVec (readBackType ctx eTypeVal) (readBack ctx NAT lenVal)
readBackType ctx (EITHER leftVal rightVal) =
    CoreEither (readBackType ctx leftVal) (readBackType ctx rightVal)
readBackType ctx (NEU UNIVERSE ne) =
    readBackNeutral ctx ne
readBackType _ _ = error "There is a logic error in the implementation where `readBackType` has been called on a `Value` that is not a type"

readBack :: Context -> Value -> Value -> CoreTerm
readBack ctx UNIVERSE v = readBackType ctx v
readBack _ NAT ZERO = CoreNatZero
readBack ctx NAT (ADD1 nMinus1) =
    CoreNatAdd1 (readBack ctx NAT nMinus1)
readBack ctx (PI x xType clos) f =
    let y = case f of
                (LAM yPrime _) -> yPrime
                _ -> x
        xPrime = fresh ctx y
        neuVal = NEU xType (N_Var xPrime)
    in (CoreLambda xPrime (readBack (bindFree ctx xPrime xType) (valOfClosure clos neuVal) (doAp f neuVal)))
readBack ctx (SIGMA _ xType clos) pVal =
    let car = doCar pVal
    in (CoreCons (readBack ctx xType car) (readBack ctx (valOfClosure clos car) (doCdr pVal)))
readBack _ ATOM (QUOTE a) = CoreAtomLiteral a
readBack _ TRIVIAL _ = CoreTrivialSole -- NOTE: η-expansion
readBack _ (LIST _) NIL = CoreListNil
readBack ctx (LIST eType) (LIST_COLON_COLON h t) =
    CoreListColonColon (readBack ctx eType h) (readBack ctx (LIST eType) t)
-- NOTE: This is apparently half of an η law with the other half being in `alphaEquiv`???
readBack ctx ABSURD (NEU _ ne) =
    CoreThe $ The CoreAbsurd (readBackNeutral ctx ne)
readBack ctx (EQUAL xType _ _) (SAME v) = CoreEqSame (readBack ctx xType v)
readBack _ (VEC _ ZERO) _ = CoreVecNil
readBack ctx (VEC xType (ADD1 lenMinus1)) (VEC_COLON_COLON h t) =
    CoreVecColonColon (readBack ctx xType h) (readBack ctx (VEC xType lenMinus1) t)
readBack ctx (EITHER leftType _) (LEFT leftVal) =
    CoreEitherLeft (readBack ctx leftType leftVal)
readBack ctx (EITHER _ rightType) (RIGHT rightVal) =
    CoreEitherRight (readBack ctx rightType rightVal)
readBack ctx _ (NEU _ ne) = readBackNeutral ctx ne
readBack _ _ _ = error "There is a logic error in the implementation where `readBack` has been called on a `Value` that is not a non-neutral non-type value"

readBackNeutral :: Context -> Neutral -> CoreTerm
readBackNeutral ctx (N_Which_Nat target (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreWhichNat (readBackNeutral ctx target) (The (readBackType ctx baseTypeVal) (readBack ctx baseTypeVal baseVal)) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Iter_Nat target (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreIterNat (readBackNeutral ctx target) (The (readBackType ctx baseTypeVal) (readBack ctx baseTypeVal baseVal)) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Rec_Nat target (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreRecNat (readBackNeutral ctx target) (The (readBackType ctx baseTypeVal) (readBack ctx baseTypeVal baseVal)) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Ind_Nat target (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreIndNat (readBackNeutral ctx target) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Car target) =
    CoreCar (readBackNeutral ctx target)
readBackNeutral ctx (N_Cdr target) =
    CoreCdr (readBackNeutral ctx target)
readBackNeutral ctx (N_Ind_List target (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreIndList (readBackNeutral ctx target) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Rec_List target (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreRecList (readBackNeutral ctx target) (The (readBackType ctx baseTypeVal) (readBack ctx baseTypeVal baseVal)) (readBack ctx stepTypeVal stepVal)
-- NOTE: This is half of an η law with the other half being in `alphaEquiv`
readBackNeutral ctx (N_Ind_Absurd target (THE typeVal val)) =
    CoreIndAbsurd (CoreThe (The CoreAbsurd (readBackNeutral ctx target))) (readBack ctx typeVal val)
readBackNeutral ctx (N_Replace target (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal)) =
    CoreReplace (readBackNeutral ctx target) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal)
readBackNeutral ctx (N_Trans12 p1 p2) =
    CoreTrans (readBackNeutral ctx p1) (readBackNeutral ctx p2)
readBackNeutral ctx (N_Trans1 ne (THE t v)) =
    CoreTrans (readBackNeutral ctx ne) (readBack ctx t v)
readBackNeutral ctx (N_Trans2 (THE t v) ne) =
    CoreTrans (readBack ctx t v) (readBackNeutral ctx ne)
readBackNeutral ctx (N_Cong ne (THE (PI y yTypeVal clos) val)) =
-- NOTE: The reason `valOfClosure clos ABSURD` is valid is because the only place `N_Cong` is constructed (`doCong`), the lambda ignores its parameter.
    CoreCong (readBackNeutral ctx ne) (readBackType ctx (valOfClosure clos ABSURD)) (readBack ctx (PI y yTypeVal clos) val)
readBackNeutral ctx (N_Symm ne) =
    CoreSymm (readBackNeutral ctx ne)
readBackNeutral ctx (N_Ind_Eq ne (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal)) =
    CoreIndEq (readBackNeutral ctx ne) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal)
readBackNeutral ctx (N_Head ne) =
    CoreHead (readBackNeutral ctx ne)
readBackNeutral ctx (N_Tail ne) =
    CoreTail (readBackNeutral ctx ne)
readBackNeutral ctx (N_Ind_Vec2 (THE lenTypeVal lenVal) es (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreIndVec (readBack ctx lenTypeVal lenVal) (readBackNeutral ctx es) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Ind_Vec12 len es (THE motiveTypeVal motiveVal) (THE baseTypeVal baseVal) (THE stepTypeVal stepVal)) =
    CoreIndVec (readBackNeutral ctx len) (readBackNeutral ctx es) (readBack ctx motiveTypeVal motiveVal) (readBack ctx baseTypeVal baseVal) (readBack ctx stepTypeVal stepVal)
readBackNeutral ctx (N_Ind_Either target (THE motiveTypeVal motiveVal) (THE leftTypeVal leftVal) (THE rightTypeVal rightVal)) =
    CoreIndEither (readBackNeutral ctx target) (readBack ctx motiveTypeVal motiveVal) (readBack ctx leftTypeVal leftVal) (readBack ctx rightTypeVal rightVal)
readBackNeutral ctx (N_Ap target (THE argTypeVal argVal)) =
    CoreApplication (readBackNeutral ctx target) (readBack ctx argTypeVal argVal)
readBackNeutral _ (N_Var x) =
    CoreVar x
readBackNeutral _ _ = error "There is a logic error in the implementation where `readBackNeutral` has been called on a Neutral with an ill-formed type annotation"
