module TypedAst(module TypedAst, module Ast) where
import Ast
import TTypes
import Unique()
import Data.List()
import Hash

data TypedDeclData
  = TTypeDecl TType
  | TFunDecl [TypedMatchExpr] TType TypedStatement
    deriving (Show, Ord, Eq)

type TypedDecl = (Identifier, TypedDeclData)

data TExpr = TIntExpr Int
           | TRealExpr Double
           | TBoolExpr Bool
           | TStringExpr String
           | TOrExpr TypedExpr TypedExpr
           | TAndExpr TypedExpr TypedExpr
           | TEqExpr TypedExpr TypedExpr
           | TNeqExpr TypedExpr TypedExpr
           | TLtExpr TypedExpr TypedExpr
           | TGtExpr TypedExpr TypedExpr
           | TLeExpr TypedExpr TypedExpr
           | TGeExpr TypedExpr TypedExpr
           | TAddExpr TypedExpr TypedExpr
           | TSubExpr TypedExpr TypedExpr
           | TMultExpr TypedExpr TypedExpr
           | TDivExpr TypedExpr TypedExpr
           | TUnaryMinusExpr TypedExpr
           | TBangExpr TypedExpr
           | TCallExpr TypedExpr TypedExpr
           | TListExpr [TypedExpr]
           | TTupleExpr [TypedExpr]
           | TRecordExpr [(String, TypedExpr)]
           | TLValue TypedLValueExpr
           | TLambdaExpr [TypedMatchExpr] TypedStatement
  deriving (Show, Ord, Eq)

type TypedExpr = (TExpr, TType)

data TMatchExpr = TTupleMatchExpr [TypedMatchExpr]
                | TListMatchExpr [TypedMatchExpr]
                | TRecordMatchExpr [(String, TypedMatchExpr)]
                | TVarMatch Identifier
                | TIntMatchExpr Int
                | TStringMatchExpr String
                | TBoolMatchExpr Bool
  deriving (Show, Eq, Ord)

type TypedMatchExpr = (TMatchExpr, TType)

data TLValueExpr = TVarExpr Identifier
                 | TFieldAccessExpr TypedLValueExpr String
                 | TArrayAccessExpr TypedLValueExpr TypedExpr
  deriving (Show, Ord, Eq)

type TypedLValueExpr = (TLValueExpr, TType)

data TypedStatement = TIfStatement TypedExpr TypedStatement (Maybe TypedStatement)
                    | TWhileStatement TypedExpr TypedStatement
                    | TForStatement TypedMatchExpr TypedExpr TypedStatement
                    | TCompoundStatement [TypedStatement]
                    | TAssignStatement (Either TypedMatchExpr TypedLValueExpr) TypedExpr
                    | TMatchStatement TypedExpr [(TypedMatchExpr, TypedStatement)]
                    | TReturnStatement TypedExpr
                    | TBreakStatement
                    | TContinueStatement
                    | TDeclStatement TypedDecl
  deriving (Show, Ord, Eq)
