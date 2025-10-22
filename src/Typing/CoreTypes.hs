-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Typing.CoreTypes where

import Utils.BasicTypes

data The = The CoreTerm CoreTerm
    deriving (Eq, Show)

data CoreTerm
    = CoreThe The

    | CoreVar Name

    | CoreAtom
    | CoreAtomLiteral String

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

