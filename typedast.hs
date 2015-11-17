module TypedAst(module TypedAst, module Ast) where
import Ast

data TypedDecl = TTypeDecl String [String] Type
               | TFunDecl String [String] [TypedMatchExpr] Type TypedStatement
    deriving (Show)

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
  deriving (Show)

type TypedExpr = (TExpr, Type)

data TMatchExpr = TTupleMatchExpr [TypedMatchExpr]
                | TListMatchExpr [TypedMatchExpr]
                | TRecordMatchExpr [(String, TypedMatchExpr)]
                | TVarMatch String
                | TIntMatchExpr Int
                | TStringMatchExpr String
                | TBoolMatchExpr Bool
  deriving (Show, Eq, Ord)

type TypedMatchExpr = (TMatchExpr, Type)

data TLValueExpr = TVarExpr String
                 | TFieldAccessExpr TypedLValueExpr String
                 | TArrayAccessExpr TypedLValueExpr TypedExpr
  deriving (Show)

type TypedLValueExpr = (TLValueExpr, Type)

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
  deriving (Show)
