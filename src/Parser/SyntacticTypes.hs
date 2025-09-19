module Parser.SyntacticTypes(Term(..), Name, The(..), Context) where

type Context = [(Name, Term)]

type Name = String -- [a-zA-Z] or [0-9] or '-' (first character must be a letter); kebab-case allowed

data The = The Term Term
    deriving (Eq, Show)

-- NOTE: Preface all constructors with `Term`
data Term
    = TermThe The

    | TermVar Name

    | TermAtom
    | TermAtomLiteral String

    | TermSigma (Name, Term) Term
    | TermCons Term Term
    | TermCar Term
    | TermCdr Term

    | TermPi (Name, Term) Term
    | TermLambda Name Term
    | TermApplication Term Term

    | TermNat
    | TermNatZero
    | TermNatAdd1 Term

    | TermWhichNat Term The Term
    | TermIterNat Term The Term
    | TermRecNat Term The Term
    | TermIndNat Term Term Term Term

    | TermList Term
    | TermListNil
    | TermListColonColon Term Term

    | TermRecList Term The Term
    | TermIndList Term Term Term Term

    | TermVec Term Term
    | TermVecNil
    | TermVecColonColon Term Term
    | TermHead Term
    | TermTail Term

    | TermIndVec Term Term Term Term Term

    | TermEq Term Term Term
    | TermEqSame Term

    | TermSymm Term
    | TermCong Term Term Term
    | TermReplace Term Term Term
    | TermTrans Term Term
    | TermIndEq Term Term Term

    | TermEither Term Term
    | TermEitherLeft Term
    | TermEitherRight Term

    | TermIndEither Term Term Term Term

    | TermTrivial
    | TermTrivialSole

    | TermAbsurd
    | TermIndAbsurd Term Term

    | TermU

    -- NOTE: TermType is a fake term that is used only for internal tagging within type checking
    | TermType
    deriving (Eq, Show)

