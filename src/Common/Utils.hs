-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Common.Utils (bug, typingLookup, bindFree, fresh, namesOnly, freshen) where

import GHC.Stack (HasCallStack)
import qualified Data.Text as T

import Common.Types

bug :: HasCallStack => Error -> a
bug = error

binderType :: Binder -> Value
binderType (Claim typeVal) = typeVal
binderType (Def typeVal _) = typeVal
binderType (Free typeVal) = typeVal

-- NOTE: We skip Claims because we require variables to actually be defined in order for them to be used.
--  Skipping claims during variable lookup disallows all undefined variables automatically.
--  Claims are only used when generating/checking the type for Defs.
typingLookup :: Context -> Name -> Either Error Value
typingLookup [] x = Left $ (T.unpack x) <> " is missing a definition or free expression bound to it in the context."
typingLookup ((_, Claim _):ctxTail) x =
    typingLookup ctxTail x
typingLookup ((y, b):ctxTail) x
    | x == y    = return $ binderType b
    | otherwise = typingLookup ctxTail x

bindFree :: Context -> Name -> Value -> Context
bindFree ctx x typeVal = case typingLookup ctx x of
    Right _ -> bug $ (T.unpack x) <> " is already bound in the context."
    Left _ -> (x, Free typeVal) : ctx

fresh :: Context -> Name -> Name
fresh ctx x = freshen (namesOnly ctx) x

namesOnly :: Context -> [Name]
namesOnly = map fst

freshen :: [Name] -> Name -> Name
freshen usedNames x
    | x `elem` usedNames = freshen usedNames (x <> "'")
    | otherwise          = x

