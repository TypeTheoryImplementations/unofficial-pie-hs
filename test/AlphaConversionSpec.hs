module AlphaConversionSpec where

import Test.Hspec
import Parser

-- TODO: Maybe change descriptions/strings for `describe` and `it` to be more consistent

freeVariables :: Spec
freeVariables = do
    describe "Free Variable Tests" $ do
        it "Single Free Variable" $
            alphaRename (Variable "x") `shouldBe` (Variable "x")

shadowing :: Spec
shadowing = do
    describe "Shadowing Tests" $ do
        it "Shadowed Variable" $
            let term = Lambda "x" Type (Lambda "x" Type (Variable "x"))
                expectedTerm = Lambda "x" Type (Lambda "x'" Type (Variable "x'"))
            in alphaRename term `shouldBe` expectedTerm

globalCollision :: Spec
globalCollision = do
    describe "Global Collision Tests" $ do
        it "Global Unique Identifiers" $
            let term = Application (Lambda "x" Type (Variable "x")) (Lambda "x" Type (Variable "x"))
                expectedTerm = Application (Lambda "x" Type (Variable "x")) (Lambda "x'" Type (Variable "x'"))
            in alphaRename term `shouldBe` expectedTerm

spec :: Spec
spec = do
    describe "Alpha Conversion Tests" $ do
        freeVariables
        shadowing
        globalCollision
