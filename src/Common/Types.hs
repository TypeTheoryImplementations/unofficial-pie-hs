-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Common.Types (Name, Error, Renaming, Binder(..), Context, Env, Closure(..), Value(..), Neutral(..), Norm(..), The(..), CoreTerm(..), TopLevelDecls, TopLevelDecl(..), SyntacticTerm(..)) where

import qualified Data.Text as T

type Name = T.Text -- [a-zA-Z] or [0-9] or '-' (first character must be a letter); kebab-case allowed

type Error = String

type Renaming = [(Name, Name)]

data Binder
    = Claim { claimType :: Value }
    | Def { defType :: Value, defValue :: Value }
    | Free { freeType :: Value }

type Context = [(Name, Binder)]

type Env = [(Name, Value)]

data Closure
    = FO_CLOS { foClosEnv :: Env, foClosVar :: Name, foClosExpr :: CoreTerm }
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
    | N_Cdr { nCdrTarget :: Neutral }

    | N_Rec_List { nRecListTarget :: Neutral, nRecListBase :: Norm, nRecListStep :: Norm }
    | N_Ind_List { nIndListTarget :: Neutral, nIndListMotive :: Norm, nIndListBase :: Norm, nIndListStep :: Norm }

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
    -- NOTE: There is no `N_Ind_Vec1` because if the second param is not a neutral,
        -- then we would know the value of the first param too (since it is part of the second param's type), thus, it would not be a neutral indVec at all.
    | N_Ind_Vec2 { nIndVec2Target1 :: Norm, nIndVec2Target2 :: Neutral, nIndVec2Motive :: Norm, nIndVec2Base :: Norm, nIndVec2Step :: Norm }
    | N_Ind_Vec12 { nIndVec12Target1 :: Neutral, nIndVec12Target2 :: Neutral, nIndVec12Motive :: Norm, nIndVec12Base :: Norm, nIndVec12Step :: Norm }

    | N_Ind_Either { nIndEitherTarget :: Neutral, nIndEitherMotive :: Norm, nIndEitherBaseLeft :: Norm, nIndEitherBaseRight :: Norm }

    | N_Ap { nApRator :: Neutral, nApRand :: Norm }

data Norm = THE { normTheType :: Value, normTheValue :: Value }

data The = The CoreTerm CoreTerm
    deriving (Eq, Show)

data CoreTerm
    = CoreThe The

    | CoreVar Name

    | CoreAtom
    | CoreAtomLiteral T.Text

    | CoreSigma Name CoreTerm CoreTerm
    | CoreCons CoreTerm CoreTerm

    | CoreCar CoreTerm
    | CoreCdr CoreTerm

    | CorePi Name CoreTerm CoreTerm
    | CoreLambda Name CoreTerm
    | CoreApplication CoreTerm CoreTerm

    | CoreNat
    | CoreNatZero
    | CoreNatAdd1 CoreTerm

    | CoreWhichNat CoreTerm The CoreTerm
    | CoreIterNat CoreTerm The CoreTerm
    | CoreRecNat CoreTerm The CoreTerm
    | CoreIndNat CoreTerm CoreTerm CoreTerm CoreTerm

    | CoreList CoreTerm
    | CoreListNil
    | CoreListColonColon CoreTerm CoreTerm

    | CoreRecList CoreTerm The CoreTerm
    | CoreIndList CoreTerm CoreTerm CoreTerm CoreTerm

    | CoreVec CoreTerm CoreTerm
    | CoreVecNil
    | CoreVecColonColon CoreTerm CoreTerm

    | CoreHead CoreTerm
    | CoreTail CoreTerm
    | CoreIndVec CoreTerm CoreTerm CoreTerm CoreTerm CoreTerm

    | CoreEq CoreTerm CoreTerm CoreTerm
    | CoreEqSame CoreTerm

    | CoreSymm CoreTerm
    | CoreCong CoreTerm CoreTerm CoreTerm
    | CoreReplace CoreTerm CoreTerm CoreTerm
    | CoreTrans CoreTerm CoreTerm
    | CoreIndEq CoreTerm CoreTerm CoreTerm

    | CoreEither CoreTerm CoreTerm
    | CoreEitherLeft CoreTerm
    | CoreEitherRight CoreTerm

    | CoreIndEither CoreTerm CoreTerm CoreTerm CoreTerm

    | CoreTrivial
    | CoreTrivialSole

    | CoreAbsurd

    | CoreIndAbsurd CoreTerm CoreTerm

    | CoreU
    deriving (Eq, Show)

type TopLevelDecls = [TopLevelDecl]

data TopLevelDecl
    = TopLevelClaim Name SyntacticTerm
    | TopLevelDef Name SyntacticTerm
    | TopLevelCheckSame SyntacticTerm SyntacticTerm SyntacticTerm
    | TopLevelFree SyntacticTerm
    deriving (Eq, Show)

data SyntacticTerm
    = SrcThe SyntacticTerm SyntacticTerm

    | SrcVar Name

    | SrcAtom
    | SrcAtomLiteral T.Text

    | SrcPair SyntacticTerm SyntacticTerm
    | SrcSigma [(Name, SyntacticTerm)] SyntacticTerm -- The list must have at least one element in it
    | SrcCons SyntacticTerm SyntacticTerm

    | SrcCar SyntacticTerm
    | SrcCdr SyntacticTerm

    | SrcArrow SyntacticTerm [SyntacticTerm]  -- The list must have at least one element in it
    | SrcPi [(Name, SyntacticTerm)] SyntacticTerm  -- The list must have at least one element in it
    | SrcLambda [Name] SyntacticTerm  -- The list must have at least one element in it
    | SrcApplication SyntacticTerm [SyntacticTerm]  -- The list must have at least one element in it

    | SrcNat
    | SrcNatZero
    | SrcNatAdd1 SyntacticTerm
    | SrcNatLiteral Integer

    | SrcWhichNat SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcIterNat SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcRecNat SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcIndNat SyntacticTerm SyntacticTerm SyntacticTerm SyntacticTerm

    | SrcList SyntacticTerm
    | SrcListNil
    | SrcListColonColon SyntacticTerm SyntacticTerm

    | SrcRecList SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcIndList SyntacticTerm SyntacticTerm SyntacticTerm SyntacticTerm

    | SrcVec SyntacticTerm SyntacticTerm
    | SrcVecNil
    | SrcVecColonColon SyntacticTerm SyntacticTerm

    | SrcHead SyntacticTerm
    | SrcTail SyntacticTerm
    | SrcIndVec SyntacticTerm SyntacticTerm SyntacticTerm SyntacticTerm SyntacticTerm

    | SrcEq SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcEqSame SyntacticTerm

    | SrcEqSymm SyntacticTerm
    | SrcEqCong SyntacticTerm SyntacticTerm
    | SrcEqReplace SyntacticTerm SyntacticTerm SyntacticTerm
    | SrcEqTrans SyntacticTerm SyntacticTerm
    | SrcEqIndEq SyntacticTerm SyntacticTerm SyntacticTerm

    | SrcEither SyntacticTerm SyntacticTerm
    | SrcEitherLeft SyntacticTerm
    | SrcEitherRight SyntacticTerm

    | SrcIndEither SyntacticTerm SyntacticTerm SyntacticTerm SyntacticTerm

    | SrcTrivial
    | SrcTrivialSole

    | SrcAbsurd

    | SrcIndAbsurd SyntacticTerm SyntacticTerm

    | SrcU
    deriving (Eq, Show)
