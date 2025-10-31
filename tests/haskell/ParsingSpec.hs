-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: (0BSD OR AGPL-3.0-only)

module ParsingSpec where

import Test.Hspec

import Common.Types
import Parser.Parser

import Text.Megaparsec (parse)

spec :: Spec
spec = do
    describe "Parser" $ do
        it "Parses a simple expression" $ do
            let input = "x"
            let expectedResult = SrcVar "x"
            parse parseTopLevel "x" input `shouldBe` Right [TopLevelFree expectedResult]
        it "Parses Single Param Arrow" $ do
            let input = "(-> Nat Nat)"
            let expectedResult = SrcArrow SrcNat [SrcNat]
            parse parseTopLevel "(-> Nat Nat)" input `shouldBe` Right [TopLevelFree expectedResult]
