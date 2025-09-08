module Typing.TypingRules where

import Parser.Parser

-- Forms of judgement:
-- Γ ctx                                Γ is a context.
-- Γ ⊢ fresh -> x                       Γ does not bind x.
-- Γ ⊢ x lookup -> c_t                  Looking up x in Γ yields the type c_t.
-- Γ ⊢ e_t type -> c_t                  e_t represents the type c_t.
-- Γ ⊢ c_1 ≡ c_2 type                   c_1 and c_2 are the same type.
-- Γ ⊢ e ∈ c_t -> c_e                   Checking that e can have type c_t results in c_e.
-- Γ ⊢ e synth -> (the c_t c_e)         From e, the type c_t can be synthesized, resulting in c_e.
-- Γ ⊢ c_1 ≡ c_2 : c_t                  c_1 is the same c_t as c_2.

type Context = [(Name, Term)]

unused :: Name -> Name
unused = id

-- NOTE: Be careful about name collisions
subst :: Context -> Name -> Term -> Term -> Term
subst ctx replaceThis withThis inExpression = undefined -- TODO: Implement me!!!

-- TODO: Replace `applyMotive` with some sort of NbE implementation that uses lambdas/closures instead of an extended string-based context
applyMotive :: Context -> Term -> Term -> Term
applyMotive = undefined

typingLookup :: Context -> Name -> Maybe Term
typingLookup [] _ = Nothing
typingLookup (ctxHead : ctxTail) x
    | fst ctxHead == x  = Just $ snd ctxHead
    | otherwise         = typingLookup ctxTail x

typingSynth:: Context -> Term -> Maybe The
typingSynth ctx (TermVar x) = do -- Hypothesis
    xType <- typingLookup ctx x
    return $ The xType (TermVar x)
typingSynth _ (TermAtomLiteral sym) =  -- AtomI
    return $ The TermAtom (TermAtomLiteral sym)
typingSynth ctx (TermCar pr) = do -- SigmaE-1
    (The (TermSigma (_, aType) _) prOut) <- typingSynth ctx pr -- TODO: This is too strict. `typingSynth` might not return exactly `TermSigma`,
        -- TODO: but instead something definitionally/judgmentally equal to `TermSigma`
    return $ The aType (TermCar prOut)
typingSynth ctx (TermCdr pr) = do -- SigmaE-2
    (The (TermSigma (x, _) dType) prOut) <- typingSynth ctx pr -- TODO: This is too strict. `typingSynth` might not return exactly `TermSigma`,
        -- TODO: but instead something definitionally/judgmentally equal to `TermSigma`
    return $ The (subst ctx x (TermCar prOut) dType) ((TermCdr prOut)) -- TODO: Replace all occurences of `x` with `TermCar prOut` in `dType` in a capture avoiding way
typingSynth ctx (TermApplication f arg) = do -- FunE
    (The (TermPi (x, argType) rType) fOut) <- typingSynth ctx f -- TODO: This is too strict. `typingSynth` might not return exactly `TermPi`,
        -- TODO: but instead something definitionally/judgmentally equal to `TermPi`
    argOut <- typingCheck ctx (arg, argType)
    return $ The (subst ctx x argOut rType) (TermApplication fOut argOut) -- TODO: Replace all occurences of `x` with `argOut` in `rType` in a capture avoiding way 
typingSynth _ TermNatZero = -- NatI-1
    return $ The TermNat TermNatZero
typingSynth ctx (TermNatAdd1 n) = do -- NatI-2
    nOut <- typingCheck ctx (n, TermNat)
    return $ The TermNat (TermNatAdd1 nOut)
typingSynth ctx (TermWhichNat t (The bType b) s) = do -- NatE-1
    tOut <- typingCheck ctx (t, TermNat)
    bOut <- typingCheck ctx (b, bType)
    sOut <- typingCheck ctx (s, (TermPi (unused "x", TermNat) bType))
    return $ The bType (TermWhichNat tOut (The bType bOut) sOut)
typingSynth ctx (TermIterNat t (The bType b) s) = do -- NatE-2
    tOut <- typingCheck ctx (t, TermNat)
    bOut <- typingCheck ctx (b, bType)
    sOut <- typingCheck ctx (s, (TermPi (unused "x", bType) bType))
    return $ The bType (TermIterNat tOut (The bType bOut) sOut)
typingSynth ctx (TermRecNat t (The bType b) s) = do -- NatE-3
    tOut <- typingCheck ctx (t, TermNat)
    bOut <- typingCheck ctx (b, bType)
    sOut <- typingCheck ctx (s, TermPi (unused "n", TermNat) (TermPi (unused "x", bType) bType))
    return $ The bType (TermRecNat tOut (The bType bOut) sOut)
typingSynth ctx (TermIndNat t m b s) = do -- NatE-4
    tOut <- typingCheck ctx (t, TermNat)
    mOut <- typingCheck ctx (m, TermPi (unused "x", TermNat) TermU)
    bOut <- typingCheck ctx (b, applyMotive ctx mOut TermNatZero)
    -- TODO: Maybe figure out a way using NbE or embededed closures/lambdas to do motive application instead of via the context, which is kinda gross to do
        -- TODO: I am quite unhappy with this as-is, but it should be ok for now (and mostly matches the reference impl fwiw afaict)
    sOut <- typingCheck ctx (s, (TermPi ("k", TermNat) (TermPi (unused "almost", applyMotive extendedCtx mOut (TermVar "k")) (applyMotive extendedCtx mOut (TermNatAdd1 (TermVar "k"))))))
    return $ The (applyMotive ctx mOut tOut) (TermIndNat tOut mOut bOut sOut)
    where extendedCtx = (("k", TermNat):ctx)
typingSynth ctx (TermListColonColon e es) = do -- ListI-2
    (The eType eOut) <- typingSynth ctx e
    esOut <- typingCheck ctx (es, TermList eType)
    return $ The (TermList eType) (TermListColonColon eOut esOut)
typingSynth ctx (TermRecList t (The bType b) s) = do -- ListE-1
    (The (TermList eType) tOut) <- typingSynth ctx t -- TODO: This is too strict. `typingSynth` might not return exactly `TermList eType`,
        -- TODO: but instead something definitionally/judgmentally equal to `TermList eType`
    bOut <- typingCheck ctx (b, bType)
    sOut <- typingCheck ctx (s, (TermPi (unused "x", eType) (TermPi (unused "xs", (TermList eType)) (TermPi (unused "almost", bType) bType))))
    return $ The bType (TermRecList tOut (The bType bOut) sOut)
typingSynth ctx (TermIndList t m b s) = do -- ListE-2
    (The (TermList eType) tOut) <- typingSynth ctx t -- TODO: This is too strict. `typingSynth` might not return exactly `TermList eType`,
        -- TODO: but instead something definitionally/judgmentally equal to `TermList eType`
    mOut <- typingCheck ctx (m, TermPi (unused "xs", (TermList eType)) TermU)
    let extendedCtx = (("xs", TermList eType):("x", eType):ctx)
    bOut <- typingCheck ctx (b, applyMotive ctx mOut TermListNil)
    sOut <- typingCheck ctx (s, TermPi ("x", eType) (TermPi ("xs", TermList eType) (TermPi (unused "almost", applyMotive extendedCtx mOut (TermVar "xs")) (applyMotive extendedCtx mOut (TermListColonColon (TermVar "x") (TermVar "xs"))))))
    return $ The (applyMotive ctx mOut tOut) (TermIndList tOut mOut bOut sOut)
typingSynth ctx (TermHead t) = do -- VecE-1
    (The (TermVec eType (TermNatAdd1 _)) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    return $ The eType (TermHead tOut)
typingSynth ctx (TermTail t) = do -- VecE-2
    (The (TermVec eType (TermNatAdd1 l)) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    return $ The (TermVec eType l) (TermTail tOut)
typingSynth ctx (TermIndVec l t m b s) = do -- VecE-3
    lOut <- typingCheck ctx (l, TermNat)
    (The (TermVec eType n) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    if(lOut == n) then do -- TODO: This is doing a syntactic equality check. But this should actually be doing a definitional/judgmental equality check
        mOut <- typingCheck ctx (m, TermPi ("k", TermNat) (TermPi (unused "es", TermVec eType (TermVar "k")) TermU))
        bOut <- typingCheck ctx (b, applyMotive ctx (applyMotive ctx mOut TermNatZero) TermVecNil)
        let extendedCtx = (("es", TermVec eType (TermVar "k")):("e", eType):("k", TermNat):ctx)
        sOut <- typingCheck ctx (s, TermPi ("k", TermNat) (TermPi ("e", eType) (TermPi ("es", TermVec eType (TermVar "k")) (TermPi (unused "almost", applyMotive extendedCtx (applyMotive extendedCtx mOut (TermVar "k")) (TermVar "es")) (applyMotive extendedCtx (applyMotive extendedCtx mOut (TermNatAdd1 (TermVar "k"))) (TermVecColonColon (TermVar "e") (TermVar "es")))))))
        return $ The (applyMotive ctx (applyMotive ctx mOut lOut) tOut) (TermIndVec lOut tOut mOut bOut sOut)
    else Nothing
typingSynth ctx (TermReplace t m b) = do -- EqE-1
    (The (TermEq xType from to) tOut) <- typingSynth ctx t
    mOut <- typingCheck ctx (m, TermPi (unused "x", xType) TermU)
    bOut <- typingCheck ctx (b, applyMotive ctx mOut from)
    return $ The (applyMotive ctx mOut to) (TermReplace tOut mOut bOut)
typingSynth ctx (TermCong xType t f) = do -- EqE-2
    -- NOTE: Technically you could just ignore `xType` and use `xType1` instead and thus have a 2-param cong input (this is what the reference impl and book both do).
        -- NOTE: The reason Core Pie passes it in is so that the AST node is the same for the param and return of the synth function (simplifies AST).
    (The (TermEq xType1 from to) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    (The (TermPi (_, xType2) yType) fOut) <- typingSynth ctx f -- TODO: This should also be a non-syntactic view
    if xType == xType1 && xType1 == xType2 then -- TODO: Should be definitional equality, not syntactic
-- TODO: MASSIVE ISSUE: `cong` IS UNSOUND BECAUSE I NEVER CHECK TO MAKE SURE THAT `yType` HAS NO DEPENDENCE ON THE `xType2` DOMAIN PARAMETER
-- TODO: We should check that the type of `applyMotive ctx fOut from` and the type of `applyMotive ctx fOut to` are judgmentally equal
-- TODO: Technically `yType` should be non-dependent, but since we are planning to just check the codomain types at the left and right endpoints, we should actually be using `yType` evaluated at one of said endpoints.
        return $ The (TermEq yType (applyMotive ctx fOut from) (applyMotive ctx fOut to)) (TermCong xType tOut fOut)
    else Nothing
typingSynth ctx (TermSymm t) = do -- EqE-3
    (The (TermEq xType from to) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    return $ The (TermEq xType to from) (TermSymm tOut)
typingSynth ctx (TermTrans t1 t2) = do -- EqE-4
    (The (TermEq xType from mid1) t1Out) <- typingSynth ctx t1 -- TODO: This should also be a non-syntactic view
    (The (TermEq yType mid2 to) t2Out) <- typingSynth ctx t2 -- TODO: This should also be a non-syntactic view
    if xType == yType && mid1 == mid2 then -- TODO: Should be definitional equality, not syntactic
        return $ The (TermEq xType from to) (TermTrans t1Out t2Out)
    else Nothing
typingSynth ctx (TermIndEq t m b) = do -- EqE-5: Based Path Induction (aka: Parameter-variant of the J-eliminator)
    (The (TermEq xType from to) tOut) <- typingSynth ctx t -- TODO: This should also be a non-syntactic view
    mOut <- typingCheck ctx (m, TermPi ("x", xType) (TermPi (unused "t", (TermEq xType from (TermVar "x"))) TermU))
    bOut <- typingCheck ctx (b, applyMotive ctx (applyMotive ctx mOut from) (TermEqSame from))
    return $ The (applyMotive ctx (applyMotive ctx mOut to) tOut) (TermIndEq tOut mOut bOut)
typingSynth ctx (TermIndEither t m bl br) = do -- EitherE
    (The (TermEither pType sType) tOut) <- typingSynth ctx t
    mOut <- typingCheck ctx (m, TermPi (unused "x", TermEither pType sType) TermU)
    blOut <- typingCheck ctx (bl, TermPi ("x", pType) (applyMotive (("x", pType):ctx) mOut (TermEitherLeft (TermVar "x"))))
    brOut <- typingCheck ctx (br, TermPi ("x", sType) (applyMotive (("x", sType):ctx) mOut (TermEitherRight (TermVar "x"))))
    return $ The (applyMotive ctx mOut tOut) (TermIndEither tOut mOut blOut brOut)
typingSynth _ TermTrivialSole = -- TrivialI
    return $ The TermTrivial TermTrivialSole
typingSynth ctx (TermIndAbsurd t m) = do -- AbsurdE
    tOut <- typingCheck ctx (t, TermAbsurd)
    mOut <- typingCheck ctx (m, TermType)
    return $ The mOut (TermIndAbsurd tOut mOut)
typingSynth _ TermAtom = -- UI-1
    return $ The TermU TermAtom
typingSynth ctx (TermSigma (x, aType) dType) = do -- UI-2
    aTypeOut <- typingCheck ctx (aType, TermU)
    dTypeOut <- typingCheck ((x, aTypeOut):ctx) (dType, TermU)
    return $ The TermU (TermSigma (x, aTypeOut) dTypeOut)
typingSynth ctx (TermPi (x, xType) rType) = do -- UI-5
    xTypeOut <- typingCheck ctx (xType, TermU)
    rTypeOut <- typingCheck ((x, xTypeOut):ctx) (rType, TermU)
    return $ The TermU (TermPi (x, xTypeOut) rTypeOut)
typingSynth _ TermNat = -- UI-9
    return $ The TermU TermNat
typingSynth ctx (TermList eType) = do -- UI-10
    eTypeOut <- typingCheck ctx (eType, TermU)
    return $ The TermU (TermList eTypeOut)
typingSynth ctx (TermVec eType l) = do -- UI-11
    eTypeOut <- typingCheck ctx (eType, TermU)
    lOut <- typingCheck ctx (l, TermNat)
    return $ The TermU (TermVec eTypeOut lOut)
typingSynth ctx (TermEq xType from to) = do -- UI-12
    xTypeOut <- typingCheck ctx (xType, TermU)
    fromOut <- typingCheck ctx (from, xTypeOut)
    toOut <- typingCheck ctx (to, xTypeOut)
    return $ The TermU (TermEq xTypeOut fromOut toOut)
typingSynth ctx (TermEither pType sType) = do -- UI-13
    pTypeOut <- typingCheck ctx (pType, TermU)
    sTypeOut <- typingCheck ctx (sType, TermU)
    return $ The TermU (TermEither pTypeOut sTypeOut)
typingSynth _ TermTrivial = -- UI-14
    return $ The TermU TermTrivial
typingSynth _ TermAbsurd = -- UI-15
    return $ The TermU TermAbsurd
typingSynth _ _ = Nothing

typingCheck :: Context -> (Term, Term) -> Maybe Term
typingCheck _ (TermAtom, TermType) = -- AtomF
    return $ TermAtom
typingCheck ctx ((TermSigma (x, aType) dType), TermType) = do -- SigmaF
    aTypeOut <- typingCheck ctx (aType, TermType)
    dTypeOut <- typingCheck ((x, aTypeOut):ctx) (dType, TermType)
    return $ TermSigma (x, aTypeOut) dTypeOut
typingCheck ctx ((TermCons a d), (TermSigma (x, aType) dType)) = do -- SigmaI
    aOut <- typingCheck ctx (a, aType)
    dOut <- typingCheck ctx (d, (subst ctx x aOut dType)) -- TODO: Replace all occurences of `x` with `aOut` in `dType` in a capture avoiding way
    return $ TermCons aOut dOut
typingCheck ctx ((TermPi (x, argType) rType), TermType) = do -- FunF
    argTypeOut <- typingCheck ctx (argType, TermType)
    rTypeOut <- typingCheck ((x, argTypeOut):ctx) (rType, TermType)
    return $ TermPi (x, argTypeOut) rTypeOut
typingCheck ctx ((TermLambda lambdaX r), (TermPi (piX, argType) rType)) = -- FunI
    if lambdaX == piX then do -- TODO: This is too strict and rejects valid code where only the lambda and Pi param names differ
    -- TODO: Replace this with proper alpha renaming/subst
        rOut <- typingCheck ((piX, argType):ctx) (r, rType)
        return $ TermLambda lambdaX rOut
    else Nothing
typingCheck _ (TermNat, TermType) = -- NatF
    return $ TermNat
typingCheck ctx (TermList eType, TermType) = do -- ListF
    eTypeOut <- typingCheck ctx (eType, TermType)
    return $ TermList eTypeOut
typingCheck _ (TermListNil, TermList _) = -- ListI-1
    return $ TermListNil
typingCheck ctx (TermVec eType l, TermType) = do -- VecF
    eTypeOut <- typingCheck ctx (eType, TermType)
    lOut <- typingCheck ctx (l, TermNat)
    return $ TermVec eTypeOut lOut
typingCheck _ (TermVecNil, TermVec _ TermNatZero) = -- VecI-1
    return $ TermVecNil
typingCheck ctx (TermVecColonColon e es, TermVec eType (TermNatAdd1 l)) = do -- VecI-2
    eOut <- typingCheck ctx (e, eType)
    esOut <- typingCheck ctx (es, TermVec eType l)
    return $ TermVecColonColon eOut esOut
typingCheck ctx (TermEq xType from to, TermType) = do -- EqF
    xTypeOut <- typingCheck ctx (xType, TermType)
    fromOut <- typingCheck ctx (from, xTypeOut)
    toOut <- typingCheck ctx (to, xTypeOut)
    return $ TermEq xTypeOut fromOut toOut
typingCheck ctx (TermEqSame mid, TermEq xType from to) = do -- EqI
    midOut <- typingCheck ctx (mid, xType)
    if from == midOut && midOut == to then -- TODO: Both of these checks should be judgmental/definitional equality, not syntactic equality
        return $ TermEqSame midOut
    else Nothing
typingCheck ctx (TermEither pType sType, TermType) = do -- EitherF
    pTypeOut <- typingCheck ctx (pType, TermType)
    sTypeOut <- typingCheck ctx (sType, TermType)
    return $ TermEither pTypeOut sTypeOut
typingCheck ctx (TermEitherLeft lt, TermEither pType _) = do -- EitherI-1
    ltOut <- typingCheck ctx (lt, pType)
    return $ TermEitherLeft ltOut
typingCheck ctx (TermEitherRight rt, TermEither _ sType) = do -- EitherI-2
    rtOut <- typingCheck ctx (rt, sType)
    return $ TermEitherRight rtOut
typingCheck _ (TermTrivial, TermType) = -- TrivialF
    return $ TermTrivial
typingCheck _ (TermAbsurd, TermType) = -- AbsurdF
    return $ TermAbsurd
typingCheck _ (TermU, TermType) = -- UF
    return $ TermU -- NOTE: U is a type, but not a term of U
typingCheck ctx (e, TermType) = -- EL
    typingCheck ctx (e, TermU)
typingCheck _ _ = Nothing



