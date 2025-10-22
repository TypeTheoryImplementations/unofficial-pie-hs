module Typing.SemanticTypes where

import Data.List
import Utils.BasicTypes
import Typing.CoreTypes
import Parser.SyntacticTypes

data Binder
    = Claim { claimType :: Value }
    | Def { defType :: Value, defValue :: Value }
    | Free { freeType :: Value }

type Bindings = [(Name, Int)]

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

-- NOTE: We skip Claims because we require variables to actually be defined in order for them to be used.
--      Skipping claims during variable lookup disallows all undefined variables automatically.
--      Claims are only used when generating/checking the type for Defs.
typingLookup :: Context -> Name -> Maybe Value
typingLookup [] _ = Nothing
typingLookup ((_, Claim _):ctxTail) x =
    typingLookup ctxTail x
typingLookup ((y, b):ctxTail) x
    | x == y    = Just $ binderType b
    | otherwise = typingLookup ctxTail x

binderType :: Binder -> Value
binderType (Claim typeVal) = typeVal
binderType (Def typeVal _) = typeVal
binderType (Free typeVal) = typeVal

renameLookup :: Renaming -> Name -> Maybe Name
renameLookup [] _ = Nothing
renameLookup (renameHead : renameTail) x
    | fst renameHead == x   = Just $ snd renameHead
    | otherwise             = renameLookup renameTail x

rename :: Renaming -> Name -> Name
rename r x = case renameLookup r x of 
    Nothing -> x
    Just y  -> y

bindFree :: Context -> Name -> Value -> Context
bindFree ctx x typeVal = case typingLookup ctx x of
    Just _ -> error (x ++ " already bound in context")
    Nothing -> ((x, Free typeVal):ctx)

fresh :: Context -> Name -> Name
fresh ctx x = freshen (namesOnly ctx) x

freshBinder :: Context -> SyntacticTerm -> Name -> Name
freshBinder ctx expr x = freshen ((namesOnly ctx) ++ (occurringNames expr)) x

namesOnly :: Context -> [Name]
namesOnly [] = []
namesOnly (ctxHead : ctxTail) = [fst ctxHead] ++ (namesOnly ctxTail)



occurringNames :: SyntacticTerm -> [Name]
occurringNames (SrcThe t e) =
    (occurringNames t) ++ (occurringNames e)
occurringNames (SrcNatAdd1 n) =
    occurringNames n
occurringNames (SrcWhichNat target base step) =
    (occurringNames target) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcIterNat target base step) =
    (occurringNames target) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcRecNat target base step) =
    (occurringNames target) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcIndNat target motive base step) =
    (occurringNames target) ++ (occurringNames motive) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcArrow t0 ts) =
    (occurringNames t0) ++ (concatMap occurringNames ts)
occurringNames (SrcPi bindings t) =
    (concatMap occurringBinderNames bindings) ++ (occurringNames t)
occurringNames (SrcLambda bindings t) =
    bindings ++ (occurringNames t)
occurringNames (SrcSigma bindings t) =
    (concatMap occurringBinderNames bindings) ++ (occurringNames t)
occurringNames (SrcPair a d) =
    (occurringNames a) ++ (occurringNames d)
occurringNames (SrcCons a d) =
    (occurringNames a) ++ (occurringNames d)
occurringNames (SrcCar p) =
    occurringNames p
occurringNames (SrcCdr p) =
    occurringNames p
occurringNames (SrcListColonColon a d) =
    (occurringNames a) ++ (occurringNames d)
occurringNames (SrcList e) =
    occurringNames e
occurringNames (SrcRecList target base step) =
    (occurringNames target) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcIndList target motive base step) =
    (occurringNames target) ++ (occurringNames motive) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcIndAbsurd target motive) =
    (occurringNames target) ++ (occurringNames motive)
occurringNames (SrcEq xType from to) =
    (occurringNames xType) ++ (occurringNames from) ++ (occurringNames to)
occurringNames (SrcEqSame e) =
    occurringNames e
occurringNames (SrcEqReplace target motive base) =
    (occurringNames target) ++ (occurringNames motive) ++ (occurringNames base)
occurringNames (SrcEqTrans target1 target2) =
    (occurringNames target1) ++ (occurringNames target2)
occurringNames (SrcEqCong target func) =
    (occurringNames target) ++ (occurringNames func)
occurringNames (SrcEqSymm target) =
    occurringNames target
occurringNames (SrcEqIndEq target motive base) =
    (occurringNames target) ++ (occurringNames motive) ++ (occurringNames base)
occurringNames (SrcVec e len) =
    (occurringNames e) ++ (occurringNames len)
occurringNames (SrcVecColonColon hd tl) =
    (occurringNames hd) ++ (occurringNames tl)
occurringNames (SrcHead target) =
    occurringNames target
occurringNames (SrcTail target) =
    occurringNames target
occurringNames (SrcIndVec len target motive base step) =
    (occurringNames len) ++ (occurringNames target) ++ (occurringNames motive) ++ (occurringNames base) ++ (occurringNames step)
occurringNames (SrcEither a b) =
    (occurringNames a) ++ (occurringNames b)
occurringNames (SrcEitherLeft e) =
    occurringNames e
occurringNames (SrcEitherRight e) =
    occurringNames e
occurringNames (SrcIndEither target motive l r) =
    (occurringNames target) ++ (occurringNames motive) ++ (occurringNames l) ++ (occurringNames r)
occurringNames (SrcApplication f args) =
    (occurringNames f) ++ (concatMap occurringNames args)
occurringNames (SrcVar x) =
    [x]
occurringNames _ =
    []

occurringBinderNames :: (Name, SyntacticTerm) -> [Name]
occurringBinderNames (x, t) = [x] ++ (occurringNames t)



inUsedNames :: [Name] -> Name -> Maybe Int
inUsedNames usedNames x = elemIndex x usedNames

freshen :: [Name] -> Name -> Name
freshen usedNames x = case inUsedNames usedNames x of
    Just _ -> freshen usedNames (x ++ "'")
    Nothing -> x
