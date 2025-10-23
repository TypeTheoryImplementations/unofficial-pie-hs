-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Parser.SyntacticTypes where

import Utils.BasicTypes

data SyntacticTerm
    = SrcThe SyntacticTerm SyntacticTerm

    | SrcVar Name

    | SrcAtom
    | SrcAtomLiteral String

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
