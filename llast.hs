module LLAst where
import Text.PrettyPrint
import TTypes
import Hash
import qualified Data.List as List

type TIdentifier = Identifier

data LLDecl = LLTypeDecl TIdentifier TType
            | LLFunDecl Identifier [TIdentifier] TType LLStatement
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
  | HasField String -- Precondition: IsRecord
  | IsInt Int
  | IsString String
  | IsBool Bool
  deriving Show

data LLStatement
  = LLLitExpr Identifier Lit
  | LLBinOp BinOp Identifier Identifier Identifier
  | LLUnaryOp UnaryOp Identifier Identifier
  | LLCallExpr (Maybe Identifier) Identifier [Identifier]
  | LLInternalExpr (Maybe Identifier) String [Identifier]
  | LLListExpr Identifier [Identifier]
  | LLTupleExpr Identifier [Identifier]
  | LLRecordExpr Identifier [(String, Identifier)]
  | LLGetIdx Identifier Identifier Identifier -- List get
  | LLSetIdx Identifier Identifier Identifier -- List set
  | LLGetField Identifier Identifier String -- Record get
  | LLSetField Identifier String Identifier -- Record set
  | LLGetProj Identifier Identifier Int -- Tuple get
--  | LLSetProj Identifier Int Identifier -- Tuple set
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
