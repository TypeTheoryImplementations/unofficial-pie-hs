module Typing.Normalization where

import Typing.ActualSemTypes
import Parser.SyntacticTypes

-- NOTE: We make use of Haskell's built-in laziness. So we call the function directly and get the Value, but Haskell will automagically memoize it
--     NOTE: This allows use to get rid of all the box and DELAY boilerplate/logic that is present in the reference implementation which is written in Racket
later :: Env -> Term -> Value
later env expr = v where v = reflect env expr

valOfClosure :: Closure -> Value -> Value
valOfClosure closure val =
    case closure of
        (FO_CLOS env argName expr) -> reflect ((argName, val):env) expr
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
                    (THE (SIGMA "h" elementType (HO_CLOS (\_ ->
                        SIGMA "t" (LIST elementType) (HO_CLOS (\_ ->
                            SIGMA "ih" baseTypeVal (HO_CLOS (\_ ->
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
                        (THE (SIGMA "h" elementType (HO_CLOS (\h ->
                            SIGMA "t" (LIST elementType) (HO_CLOS (\t ->
                                SIGMA "ih" (doAp motiveVal t) (HO_CLOS (\_ ->
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
                    (THE (SIGMA "x" aTypeVal (HO_CLOS (\_ -> UNIVERSE))) motiveVal)
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
doCong targetVal baseTypeVal funcVal =
    case targetVal of
        (SAME val) -> SAME (doAp funcVal val)
        (NEU (EQUAL aTypeVal fromVal toVal) ne) ->
            NEU
                (EQUAL baseTypeVal (doAp funcVal fromVal) (doAp funcVal toVal))
                (N_Cong ne (THE (SIGMA "x" aTypeVal (HO_CLOS (\_ -> baseTypeVal))) funcVal))
        _ -> error "There is a logic error in the implementation where `doCong` has been called on an invalid target"
doSymm :: Value -> Value
doSymm targetVal =
    case targetVal of
        (SAME val) -> (SAME val)
        (NEU (EQUAL aTypeVal fromVal toVal) ne) ->
            (NEU (EQUAL aTypeVal toVal fromVal) ne)
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
                        (SIGMA "to" aTypeVal (HO_CLOS (\to ->
                            SIGMA "p" (EQUAL aTypeVal fromVal to) (HO_CLOS (\_ ->
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
    SIGMA "k" NAT (HO_CLOS (\k ->
        SIGMA "e" elementTypeVal (HO_CLOS (\e ->
            SIGMA "es" (VEC elementTypeVal k) (HO_CLOS (\es ->
                SIGMA "ih" (doAp (doAp motiveVal k) es) (HO_CLOS (\_ ->
                    doAp (doAp motiveVal (ADD1 k)) (VEC_COLON_COLON e es)))))))))
doIndVec :: Value -> Value -> Value -> Value -> Value -> Value
doIndVec lenVal vecVal motiveVal baseVal stepVal =
    case (lenVal, vecVal) of
        (ZERO, VECNIL) -> baseVal
        ((ADD1 lenMinus1Val), (VEC_COLON_COLON h t)) ->
            doAp (doAp (doAp (doAp stepVal lenMinus1Val) h) (doTail vecVal))
                (doIndVec lenMinus1Val t motiveVal baseVal stepVal)
        ((NEU (NAT) len), (NEU (VEC elementTypeVal _) ne)) ->
            NEU
                (doAp (doAp motiveVal lenVal) vecVal)
                (N_Ind_Vec12
                    len
                    ne
                    (THE (SIGMA "k" NAT (HO_CLOS (\k ->
                        SIGMA "es" (VEC elementTypeVal k) (HO_CLOS (\_ ->
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
                    (THE (SIGMA "k" NAT (HO_CLOS (\k ->
                        SIGMA "es" (VEC elementTypeVal k) (HO_CLOS (\_ ->
                            UNIVERSE)))))
                        motiveVal)
                    (THE (doAp (doAp motiveVal ZERO) VECNIL) baseVal)
                    (THE (indVecStepType elementTypeVal motiveVal) stepVal))
-- TODO: What about `N_Ind_Vec1`? It's in Neutral, but it seems to never be implemented in the reference impl???
        _ -> error "There is a logic error in the implementation where `doIndVec` has been called on an invalid target"

doIndEither :: Value -> Value -> Value -> Value -> Value
doIndEither target motive l r =
    case target of
        (LEFT x) -> doAp l x
        (RIGHT x) -> doAp r x
        (NEU (EITHER leftTypeVal rightTypeVal) ne) ->
            let motiveTypeVal = SIGMA "x" (EITHER leftTypeVal rightTypeVal) (HO_CLOS (\_ -> UNIVERSE)) in
                NEU
                    (doAp motive target)
                    (N_Ind_Either
                        ne
                        (THE motiveTypeVal motive)
                        (THE
                            (SIGMA "x" leftTypeVal (HO_CLOS (\x ->
                                doAp motive (LEFT x))))
                                l)
                        (THE
                            (SIGMA "x" rightTypeVal (HO_CLOS (\x ->
                                doAp motive (RIGHT x))))
                            r))
        _ -> error "There is a logic error in the implementation where `doIndEither` has been called on an invalid target"

varVal :: Env -> Name -> Value
varVal [] x = error $ "Variable " ++ x ++ " not in the Env!"
varVal (ctxHead : ctxTail) x
    | fst ctxHead == x  = snd ctxHead
    | otherwise         = varVal ctxTail x

reflect :: Env -> Term -> Value
reflect env (TermThe (The _ expr)) =
    reflect env expr
reflect _ TermU = UNIVERSE
reflect _ TermNat = NAT
reflect _ TermNatZero = ZERO
reflect env (TermNatAdd1 n) = ADD1 (later env n)
reflect env (TermPi (x, aType) bType) =
    let aTypeVal = later env aType
    in PI x aTypeVal (FO_CLOS env x bType)
reflect env (TermLambda x bType) =
    LAM x (FO_CLOS env x bType)
reflect env (TermWhichNat target (The baseType base) step) =
    doWhichNat (later env target) (later env baseType) (later env base) (later env step)
reflect env (TermIterNat target (The baseType base) step) =
    doIterNat (later env target) (later env baseType) (later env base) (later env step)
reflect env (TermRecNat target (The baseType base) step) =
    doRecNat (later env target) (later env baseType) (later env base) (later env step)
reflect env (TermIndNat target motive base step) =
    doIndNat (later env target) (later env motive) (later env base) (later env step)
reflect _ (TermAtom) = ATOM
reflect env (TermSigma (x, aType) dType) =
    let aTypeVal = later env aType
    in SIGMA x aTypeVal (FO_CLOS env x dType)
reflect env (TermCons a d) =
    CONS (later env a) (later env d)
reflect env (TermCar p) =
    doCar (later env p)
reflect env (TermCdr p) =
    doCdr (later env p)
reflect _ (TermAtomLiteral a) = QUOTE a
reflect _ TermTrivial = TRIVIAL
reflect _ TermTrivialSole = SOLE
reflect _ TermListNil = NIL
reflect env (TermListColonColon h t) =
    LIST_COLON_COLON (later env h) (later env t)
reflect env (TermList elementType) =
    LIST (later env elementType)
reflect env (TermIndList target motive base step) =
    doIndList (later env target) (later env motive) (later env base) (later env step)
reflect env (TermRecList target (The baseType base) step) =
    doRecList (later env target) (later env baseType) (later env base) (later env step)
reflect _ TermAbsurd = ABSURD
reflect env (TermIndAbsurd target motive) =
    doIndAbsurd (later env target) (later env motive)
reflect env (TermEq aType from to) =
    EQUAL (later env aType) (later env from) (later env to)
reflect env (TermEqSame e) =
    SAME (later env e)
reflect env (TermReplace target motive base) =
    doReplace (later env target) (later env motive) (later env base)
reflect env (TermTrans p1 p2) =
    doTrans (later env p1) (later env p2)
reflect env (TermCong p1 p2 p3) =
    doCong (later env p1) (later env p2) (later env p3)
reflect env (TermSymm p) =
    doSymm (later env p)
reflect env (TermIndEq target motive base) =
    doIndEq (later env target) (later env motive) (later env base)
reflect env (TermVec elementType len) =
    VEC (later env elementType) (later env len)
reflect _ TermVecNil = VECNIL
reflect env (TermVecColonColon h t) =
    VEC_COLON_COLON (later env h) (later env t)
reflect env (TermHead es) =
    doHead (later env es)
reflect env (TermTail es) =
    doTail (later env es)
reflect env (TermIndVec len es mot base step) =
    doIndVec (later env len) (later env es) (later env mot) (later env base) (later env step)
reflect env (TermEither left right) =
    EITHER (later env left) (later env right)
reflect env (TermEitherLeft left) =
    LEFT (later env left)
reflect env (TermEitherRight right) =
    RIGHT (later env right)
reflect env (TermIndEither target motive left right) =
    doIndEither (later env target) (later env motive) (later env left) (later env right)
reflect env (TermApplication rator rand) =
    doAp (later env rator) (later env rand)
reflect env (TermVar x) =
    varVal env x
-- TermType is only used internally for type checking and should never be passed to normalization in any context
reflect _ TermType = error "TermType is not a valid term"


