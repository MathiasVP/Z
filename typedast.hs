module TypedAst(module TypedAst, module Ast) where
import Ast
import TTypes
import Unique()
import Data.List()
import Data.Hashable
import Hash

data TypedDecl
  = TTypeDecl Identifier TType
  | TFunDecl Identifier [Identifier] [TypedMatchExpr] TType TypedStatement
    deriving (Show, Ord, Eq)

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

instance Hashable TypedStatement where
  hashWithSalt n (TIfStatement e sThen sElse) =
    hashWithSalt n (e, sThen, sElse) `combine` 3
  hashWithSalt n (TWhileStatement e s) =
    hashWithSalt n (e, s) `combine` 5
  hashWithSalt n (TForStatement me e s) =
    hashWithSalt n (me, e, s) `combine` 7
  hashWithSalt n (TCompoundStatement ss) =
    hashWithSalt n ss `combine` 11
  hashWithSalt n (TAssignStatement lhs e) =
    hashWithSalt n (lhs, e) `combine` 13
  hashWithSalt n (TMatchStatement e actions) =
    hashWithSalt n (e, actions) `combine` 17
  hashWithSalt n (TReturnStatement e) =
    hashWithSalt n e `combine` 19
  hashWithSalt n TBreakStatement =
    n `combine` 23
  hashWithSalt n TContinueStatement =
    n `combine` 29
  hashWithSalt n (TDeclStatement decl) =
    hashWithSalt n decl `combine` 31

instance Hashable TLValueExpr where
  hashWithSalt n (TVarExpr var) =
    hashWithSalt n var `combine` 3
  hashWithSalt n (TFieldAccessExpr lve s) =
    hashWithSalt n (lve, s) `combine` 5
  hashWithSalt n (TArrayAccessExpr lve e) =
    hashWithSalt n (lve, e) `combine` 7

instance Hashable TMatchExpr where
  hashWithSalt n (TTupleMatchExpr exprs) =
    hashWithSalt n exprs `combine` 3
  hashWithSalt n (TListMatchExpr exprs) =
    hashWithSalt n exprs `combine` 5
  hashWithSalt n (TRecordMatchExpr fields) =
    hashWithSalt n fields `combine` 7
  hashWithSalt n (TVarMatch var) =
    hashWithSalt n var `combine` 9
  hashWithSalt n (TIntMatchExpr m) =
    hashWithSalt n m `combine` 11
  hashWithSalt n (TStringMatchExpr s) =
    hashWithSalt n s `combine` 13
  hashWithSalt n (TBoolMatchExpr b) =
    hashWithSalt n b `combine` 17

instance Hashable TExpr where
  hashWithSalt n (TIntExpr m) =
    hashWithSalt n m `combine` 3
  hashWithSalt n (TRealExpr r) =
    hashWithSalt n r `combine` 5
  hashWithSalt n (TBoolExpr b) =
    hashWithSalt n b `combine` 7
  hashWithSalt n (TStringExpr s) =
    hashWithSalt n s `combine` 9
  hashWithSalt n (TOrExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 11
  hashWithSalt n (TAndExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 15
  hashWithSalt n (TEqExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 17
  hashWithSalt n (TNeqExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 19
  hashWithSalt n (TLtExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 23
  hashWithSalt n (TGtExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 29
  hashWithSalt n (TLeExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 31
  hashWithSalt n (TGeExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 37
  hashWithSalt n (TAddExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 41
  hashWithSalt n (TSubExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 43
  hashWithSalt n (TMultExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 47
  hashWithSalt n (TDivExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 51
  hashWithSalt n (TUnaryMinusExpr e) =
    hashWithSalt n e `combine` 53
  hashWithSalt n (TBangExpr e) =
    hashWithSalt n e `combine` 59
  hashWithSalt n (TCallExpr e1 e2) =
    hashWithSalt n (e1, e2) `combine` 61
  hashWithSalt n (TListExpr es) =
    hashWithSalt n es `combine` 59
  hashWithSalt n (TTupleExpr es) =
    hashWithSalt n es `combine` 61
  hashWithSalt n (TRecordExpr fields) =
    hashWithSalt n fields `combine` 67
  hashWithSalt n (TLValue lve) =
    hashWithSalt n lve `combine` 71
  hashWithSalt n (TLambdaExpr mes s) =
    hashWithSalt n (mes, s) `combine` 73

instance Hashable TypedDecl where
  hashWithSalt n (TTypeDecl name ty) =
    hashWithSalt n (name, ty) `combine` 23
  hashWithSalt n (TFunDecl name tyargs mes ty s) =
    hashWithSalt n (name, tyargs, mes, ty, s) `combine` 31
