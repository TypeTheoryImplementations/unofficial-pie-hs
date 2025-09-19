module Typing.ActualSemTypes where

import Parser.SyntacticTypes

type Env = [(Name, Value)]

data Closure
    = FO_CLOS { foClosEnv :: Env, foClosVar :: Name, foClosExpr :: Term }
    | HO_CLOS { hoClosProc :: (Value -> Value) }

data Value
    = UNIVERSE

    | NAT
    | ZERO
    | ADD1 { add1Smaller :: Value }

    | ATOM
    | QUOTE { quoteName :: Name }

    | PI { piArgName :: Name, piArgType :: Value, piResultType :: Closure }
    | LAM { lamArgName :: Name, lamBody :: Closure }

    | SIGMA { sigmaCarName :: Name, sigmaCarType :: Value, sigmaCdrType :: Closure }
    | CONS { sigmaCar :: Value, sigmaCdr :: Value }

    | TRIVIAL
    | SOLE

    | LIST { listEntryType :: Value }
    | NIL
    | LIST_COLON_COLON { listColonColonHead :: Value, listColonColonTail :: Value }

    | ABSURD

    | EQUAL { equalType :: Value, equalFrom :: Value, equalTo :: Value }
    | SAME { sameValue :: Value }

    | VEC { vecEntryType :: Value, vecLength :: Value }
    | VECNIL
    | VEC_COLON_COLON { vecColonColonHead :: Value, vecColonColonTail :: Value }

    | EITHER { eitherLeftType :: Value, eitherRightType :: Value }
    | LEFT { leftValue :: Value }
    | RIGHT { rightValue :: Value }

    | NEU { neuType :: Value, neuNeutral :: Neutral }

data Neutral
    = N_Var { nVarName :: Name }

    | N_Which_Nat { nWhichNatTarget :: Neutral, nWhichNatBase :: Norm, nWhichNatStep :: Norm }
    | N_Iter_Nat { nIterNatTarget :: Neutral, nIterNatBase :: Norm, nIterNatStep :: Norm }
    | N_Rec_Nat { nRecNatTarget :: Neutral, nRecNatBase :: Norm, nRecNatStep :: Norm }
    | N_Ind_Nat { nIndNatTarget :: Neutral, nIndNatMotive :: Norm, nIndNatBase :: Norm, nIndNatStep :: Norm }

    | N_Car { nCarTarget :: Neutral }
    | N_Cdr { nCdrtarget :: Neutral }

    | N_Rec_List { nRecListTarget :: Neutral, nRecListBase :: Norm, nRecListStep :: Norm }
    | N_Ind_List { nRecListTarget :: Neutral, nRecListMotive :: Norm, nRecListBase :: Norm, nRecListStep :: Norm }

    | N_Ind_Absurd { nIndAbsurdTarget :: Neutral, nIndAbsurdMotive :: Norm }

    | N_Replace { nReplaceTarget :: Neutral, nReplaceMotive :: Norm, nReplaceBase :: Norm }
    | N_Trans1 { nTrans1Target1 :: Neutral, nTrans1Target2 :: Norm }
    | N_Trans2 { nTrans2Target1 :: Norm, nTrans2Target2 :: Neutral }
    | N_Trans12 { nTrans12Target1 :: Neutral, nTrans12Target2 :: Neutral }
    | N_Cong { nCongTarget :: Neutral, nCongFunction :: Norm }
    | N_Symm { nSymmTarget :: Neutral }
    | N_Ind_Eq { nIndEqTarget :: Neutral, nIndEqMotive :: Norm, nIndEqBase :: Norm }

    | N_Head { nHeadTarget :: Neutral }
    | N_Tail { nTailTarget :: Neutral }
    | N_Ind_Vec1 { nIndVec1Target1 :: Neutral, nIndVec1Target2 :: Norm, nIndVec1Motive :: Norm, nIndVec1Base :: Norm, nIndVec1Step :: Norm }
    | N_Ind_Vec2 { nIndVec2Target1 :: Norm, nIndVec2Target2 :: Neutral, nIndVec2Motive :: Norm, nIndVec2Base :: Norm, nIndVec2Step :: Norm }
    | N_Ind_Vec12 { nIndVec12Target1 :: Neutral, nIndVec12Target2 :: Neutral, nIndVec12Motive :: Norm, nIndVec12Base :: Norm, nIndVec12Step :: Norm }

    | N_Ind_Either { nIndEitherTarget :: Neutral, nIndEitherMotive :: Norm, nIndEitherBaseLeft :: Norm, nIndEitherBaseRight :: Norm }

    | N_Ap { nApRator :: Neutral, nApRand :: Norm }

data Norm = THE { normTheType :: Value, normTheValue :: Value }


