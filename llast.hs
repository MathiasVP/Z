module LLAst where
import Types

type TIdentifier = Identifier

data LLDecl = LLTypeDecl TIdentifier [TIdentifier] Type
            | LLFunDecl Identifier [TIdentifier] Type LLStatement
  deriving (Show)

data BinOp
  = Or | And | Eq | Neq | Lt | Gt | Le | Ge | Add | Sub | Mult | Div
  deriving Show

data UnaryOp
  = UMinus | Bang
  deriving Show

data Lit
  = IntLit Int
  | BoolLit Bool
  | StringLit String
  | RealLit Double
  deriving Show

data Pred
  = IsTuple Int
  | IsList Int
  | IsRecord
  | HasField String
  | IsInt Int
  | IsString String
  | IsBool Bool
  deriving Show

data LLStatement
  = LLLitExpr Identifier Lit
  | LLBinOp BinOp Identifier Identifier Identifier
  | LLUnaryOp UnaryOp Identifier Identifier
  | LLCallExpr Identifier Identifier [Identifier]
  | LLListExpr Identifier [Identifier]
  | LLTupleExpr Identifier [Identifier]
  | LLRecordExpr Identifier [(String, Identifier)]
  | LLGetIdx Identifier Identifier Identifier
  | LLSetIdx Identifier Identifier Identifier
  | LLGetField Identifier Identifier String
  | LLSetField Identifier String Identifier
  | LLSetProj Identifier Int Identifier
  | LLGetProj Identifier Identifier Int
  | LLAssign Identifier Identifier
  | LLLambdaExpr Identifier [Identifier] LLStatement
  | LLIf Identifier LLStatement LLStatement
  | LLPred Pred Identifier LLStatement LLStatement
  | LLWhile LLStatement Identifier LLStatement
  | LLSeq LLStatement LLStatement
  | LLReturn Identifier
  | LLBreak
  | LLContinue
  | LLDeclare LLDecl
  | LLNop
  deriving Show

instance Monoid LLStatement where
  mempty = LLNop
  mappend LLNop stmt = stmt
  mappend stmt LLNop = stmt
  mappend stmt1 stmt2 = LLSeq stmt1 stmt2