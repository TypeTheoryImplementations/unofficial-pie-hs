-- Copyright (C) 2025 Lincoln Sand
-- SPDX-License-Identifier: AGPL-3.0-only

module Typing.AlphaConversion (alphaEquiv) where

import Common.Types

type Bindings = [(Name, Int)]

alphaEquiv :: CoreTerm -> CoreTerm -> Bool
alphaEquiv e1 e2 = alphaEquivImpl 0 [] [] e1 e2

alphaEquivImpl :: Int -> Bindings -> Bindings -> CoreTerm -> CoreTerm -> Bool
alphaEquivImpl lvl b1 b2 (CorePi argName1 argType1 returnType1) (CorePi argName2 argType2 returnType2) =
    (alphaEquivImpl lvl b1 b2 argType1 argType2) && (alphaEquivImpl (lvl+1) (bind b1 argName1 lvl) (bind b2 argName2 lvl) returnType1 returnType2)
alphaEquivImpl lvl b1 b2 (CoreSigma argName1 argType1 returnType1) (CoreSigma argName2 argType2 returnType2) =
    (alphaEquivImpl lvl b1 b2 argType1 argType2) && (alphaEquivImpl (lvl+1) (bind b1 argName1 lvl) (bind b2 argName2 lvl) returnType1 returnType2)
alphaEquivImpl lvl b1 b2 (CoreLambda x1 body1) (CoreLambda x2 body2) =
    alphaEquivImpl (lvl+1) (bind b1 x1 lvl) (bind b2 x2 lvl) body1 body2
-- NOTE: This is the other half of the eta rule in `readBack`
alphaEquivImpl _ _ _ (CoreThe (The CoreAbsurd _)) (CoreThe (The CoreAbsurd _)) = True
alphaEquivImpl _ b1 b2 (CoreVar x) (CoreVar y) =
    let xBinding = lookup x b1
        yBinding = lookup y b2
    in case (xBinding, yBinding) of
        (Just lvlX, Just lvlY) -> lvlX == lvlY
        (Nothing, Nothing) -> x == y
        (_, _) -> False
alphaEquivImpl lvl b1 b2 (CoreThe (The t1 e1)) (CoreThe (The t2 e2)) =
    (alphaEquivImpl lvl b1 b2 t1 t2) && (alphaEquivImpl lvl b1 b2 e1 e2)
alphaEquivImpl _ _ _ CoreAtom CoreAtom = True
alphaEquivImpl _ _ _ (CoreAtomLiteral a1) (CoreAtomLiteral a2) = a1 == a2
alphaEquivImpl lvl b1 b2 (CoreCons car1 cdr1) (CoreCons car2 cdr2) =
    (alphaEquivImpl lvl b1 b2 car1 car2) && (alphaEquivImpl lvl b1 b2 cdr1 cdr2)
alphaEquivImpl lvl b1 b2 (CoreCar p1) (CoreCar p2) =
    alphaEquivImpl lvl b1 b2 p1 p2
alphaEquivImpl lvl b1 b2 (CoreCdr p1) (CoreCdr p2) =
    alphaEquivImpl lvl b1 b2 p1 p2
alphaEquivImpl lvl b1 b2 (CoreApplication f arg1) (CoreApplication g arg2) =
    (alphaEquivImpl lvl b1 b2 f g) && (alphaEquivImpl lvl b1 b2 arg1 arg2)
alphaEquivImpl _ _ _ CoreNat CoreNat = True
alphaEquivImpl _ _ _ CoreNatZero CoreNatZero = True
alphaEquivImpl lvl b1 b2 (CoreNatAdd1 n1) (CoreNatAdd1 n2) =
    alphaEquivImpl lvl b1 b2 n1 n2
alphaEquivImpl lvl b1 b2 (CoreWhichNat target1 (The baseType1 baseExpr1) step1) (CoreWhichNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIterNat target1 (The baseType1 baseExpr1) step1) (CoreIterNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreRecNat target1 (The baseType1 baseExpr1) step1) (CoreRecNat target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIndNat target1 motive1 base1 step1) (CoreIndNat target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreList elementType1) (CoreList elementType2) =
    alphaEquivImpl lvl b1 b2 elementType1 elementType2
alphaEquivImpl _ _ _ CoreListNil CoreListNil = True
alphaEquivImpl lvl b1 b2 (CoreListColonColon h1 t1) (CoreListColonColon h2 t2) =
    (alphaEquivImpl lvl b1 b2 h1 h2) && (alphaEquivImpl lvl b1 b2 t1 t2)
alphaEquivImpl lvl b1 b2 (CoreRecList target1 (The baseType1 baseExpr1) step1) (CoreRecList target2 (The baseType2 baseExpr2) step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 baseType1 baseType2)
    && (alphaEquivImpl lvl b1 b2 baseExpr1 baseExpr2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreIndList target1 motive1 base1 step1) (CoreIndList target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2) && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreVec elementType1 len1) (CoreVec elementType2 len2) =
    (alphaEquivImpl lvl b1 b2 elementType1 elementType2) && (alphaEquivImpl lvl b1 b2 len1 len2)
alphaEquivImpl _ _ _ CoreVecNil CoreVecNil = True
alphaEquivImpl lvl b1 b2 (CoreVecColonColon h1 t1) (CoreVecColonColon h2 t2) =
    (alphaEquivImpl lvl b1 b2 h1 h2) && (alphaEquivImpl lvl b1 b2 t1 t2)
alphaEquivImpl lvl b1 b2 (CoreHead vec1) (CoreHead vec2) =
    alphaEquivImpl lvl b1 b2 vec1 vec2
alphaEquivImpl lvl b1 b2 (CoreTail vec1) (CoreTail vec2) =
    alphaEquivImpl lvl b1 b2 vec1 vec2
alphaEquivImpl lvl b1 b2 (CoreIndVec n1 target1 motive1 base1 step1) (CoreIndVec n2 target2 motive2 base2 step2) =
    (alphaEquivImpl lvl b1 b2 n1 n2) && (alphaEquivImpl lvl b1 b2 target1 target2)
    && (alphaEquivImpl lvl b1 b2 motive1 motive2) && (alphaEquivImpl lvl b1 b2 base1 base2)
    && (alphaEquivImpl lvl b1 b2 step1 step2)
alphaEquivImpl lvl b1 b2 (CoreEq eqType1 from1 to1) (CoreEq eqType2 from2 to2) =
    (alphaEquivImpl lvl b1 b2 eqType1 eqType2) && (alphaEquivImpl lvl b1 b2 from1 from2)
    && (alphaEquivImpl lvl b1 b2 to1 to2)
alphaEquivImpl lvl b1 b2 (CoreEqSame expr1) (CoreEqSame expr2) =
    alphaEquivImpl lvl b1 b2 expr1 expr2
alphaEquivImpl lvl b1 b2 (CoreSymm expr1) (CoreSymm expr2) =
    alphaEquivImpl lvl b1 b2 expr1 expr2
alphaEquivImpl lvl b1 b2 (CoreCong target1 coDomainType1 func1) (CoreCong target2 coDomainType2 func2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 coDomainType1 coDomainType2)
    && (alphaEquivImpl lvl b1 b2 func1 func2)
alphaEquivImpl lvl b1 b2 (CoreReplace target1 motive1 base1) (CoreReplace target2 motive2 base2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2)
alphaEquivImpl lvl b1 b2 (CoreTrans fromMid1 midTo1) (CoreTrans fromMid2 midTo2) =
    (alphaEquivImpl lvl b1 b2 fromMid1 fromMid2) && (alphaEquivImpl lvl b1 b2 midTo1 midTo2)
alphaEquivImpl lvl b1 b2 (CoreIndEq target1 motive1 base1) (CoreIndEq target2 motive2 base2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
    && (alphaEquivImpl lvl b1 b2 base1 base2)
alphaEquivImpl lvl b1 b2 (CoreEither leftType1 rightType1) (CoreEither leftType2 rightType2) =
    (alphaEquivImpl lvl b1 b2 leftType1 leftType2) && (alphaEquivImpl lvl b1 b2 rightType1 rightType2)
alphaEquivImpl lvl b1 b2 (CoreEitherLeft left1) (CoreEitherLeft left2) =
    alphaEquivImpl lvl b1 b2 left1 left2
alphaEquivImpl lvl b1 b2 (CoreEitherRight right1) (CoreEitherRight right2) =
    alphaEquivImpl lvl b1 b2 right1 right2
alphaEquivImpl lvl b1 b2 (CoreIndEither target1 base1 leftStep1 rightStep1) (CoreIndEither target2 base2 leftStep2 rightStep2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 base1 base2)
    && (alphaEquivImpl lvl b1 b2 leftStep1 leftStep2) && (alphaEquivImpl lvl b1 b2 rightStep1 rightStep2)
alphaEquivImpl _ _ _ CoreTrivial CoreTrivial = True
alphaEquivImpl _ _ _ CoreTrivialSole CoreTrivialSole = True
alphaEquivImpl _ _ _ CoreAbsurd CoreAbsurd = True
alphaEquivImpl lvl b1 b2 (CoreIndAbsurd target1 motive1) (CoreIndAbsurd target2 motive2) =
    (alphaEquivImpl lvl b1 b2 target1 target2) && (alphaEquivImpl lvl b1 b2 motive1 motive2)
alphaEquivImpl _ _ _ CoreU CoreU = True
alphaEquivImpl _ _ _ _ _ = False -- mismatched `CoreTerm` constructors

bind :: Bindings -> Name -> Int -> Bindings
bind b x lvl = (x, lvl) : b
