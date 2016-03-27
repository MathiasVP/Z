{-# LANGUAGE LambdaCase #-}
module MatchCheck where

import Prelude hiding (and)
import Types
import TypedAst
import TypeUtils
import Utils
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set(Set)
import Data.Map(Map, (!))
import Data.Maybe
import Data.Tuple
import Data.Ord
import Control.Monad.Loops
import Control.Monad.Writer.Lazy
import Control.Monad.State

data CoveringResult
  = Covered
  | Nonexhaustive Pattern
  | Redundant TypedMatchExpr
  deriving Show
  
data MatchEdge = IntEdge Int
               | StringEdge String
               | BoolEdge Bool
               | TupleEdge [Type]
  
data MatchTree = TupleIdx Int Type [(MatchTree, MatchEdge)]
               | ListIdx Int Type [(MatchTree, MatchEdge)]
               | Variable Type [(MatchTree, MatchEdge)]
               | RecordField String Type [(MatchTree, MatchEdge)]
               | Union Type Type [(MatchTree, MatchEdge)]
               | Leaf [TypedMatchExpr]

data Pattern = BottomPattern Type --Match nothing of given type
             | TopPattern Type --Match anything of given type
             | IntPattern Int
             | StringPattern String
             | BoolPattern Bool
             | ArrayPattern [Pattern]
             | TuplePattern [Pattern]
             | RecordPattern [(String, Pattern)]
             | DifferencePattern Pattern Pattern
             | UnionPattern Pattern Pattern
  deriving (Eq, Ord, Show)
{-
instance Show Pattern where
  show (BottomPattern ty) = "_"
  show (TopPattern ty) = "_"
  show (IntPattern n) = show n
  show (StringPattern s) = "\"" ++ s ++ "\""
  show (BoolPattern b) = show b
  show (ArrayPattern ps) = "[" ++ List.intercalate ", " (List.map show ps) ++ "]"
  show (TuplePattern ps) = "(" ++ List.intercalate ", " (List.map show ps) ++ ")"
  show (RecordPattern ps) = "{" ++ List.intercalate ", " (List.map f ps) ++ "}"
    where f (s, p) = s ++ " = " ++ show p
  show (UnionPattern p1 p2) = "(" ++ show p1 ++ " | " ++ show p2 ++ ")"
  show (DifferencePattern p1 p2) = "(" ++ show p1 ++ " - " ++ show p2 ++ ")"
-}

matchCheck :: Env -> [TypedDecl] -> Writer [CoveringResult] Bool
matchCheck env = allM (check env)

check :: Env -> TypedDecl -> Writer [CoveringResult] Bool
check env (TTypeDecl name args ty) = return True
check env (TFunDecl name tyargs tmexprs retTy stmt) =
  ands (checkStmt env stmt : List.map (checkMatchExpr env) tmexprs)

ands = List.foldr (liftM2 (&&)) (return True)

matchable :: Type -> Bool
matchable (Arrow _ _) = False
matchable RealType = False
matchable _ = True

checkStmt :: Env -> TypedStatement -> Writer [CoveringResult] Bool
checkStmt env (TIfStatement expr stmtThen Nothing) =
  ands [checkExpr env expr, checkStmt env stmtThen]
checkStmt env (TIfStatement expr stmtThen (Just stmtElse)) =
  ands [checkExpr env expr, checkStmt env stmtThen, checkStmt env stmtElse]
checkStmt env (TWhileStatement expr stmt) =
  ands [checkExpr env expr, checkStmt env stmt]
checkStmt env (TForStatement mexpr expr stmt) =
  ands [checkMatchExpr env mexpr, checkExpr env expr, checkStmt env stmt]
checkStmt env (TCompoundStatement stmts) =
  ands (List.map (checkStmt env) stmts)
checkStmt env (TAssignStatement (Left mexpr) expr) =
  ands [checkMatchExpr env mexpr, checkExpr env expr]
checkStmt env (TAssignStatement (Right lvexpr) expr) =
  ands [checkLvalExpr env lvexpr, checkExpr env expr]
checkStmt env (TMatchStatement (expr, ty) actions)
  | matchable ty = do
    --tell (covering env (ideal env ty) (List.map fst actions))
    return True
  | otherwise =
    return True
checkStmt env (TReturnStatement expr) = checkExpr env expr
checkStmt _ TBreakStatement = return True
checkStmt _ TContinueStatement = return True
checkStmt env (TDeclStatement decl) = check env decl

checkExpr :: Env -> TypedExpr -> Writer [CoveringResult] Bool
checkExpr env (TIntExpr n, t) = return True
checkExpr env (TRealExpr d, t) = return True
checkExpr env (TBoolExpr b, t) = return True
checkExpr env (TStringExpr s, t) = return True
checkExpr env (TOrExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TAndExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TEqExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TNeqExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TLtExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TGtExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TLeExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TGeExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TAddExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TSubExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TMultExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TDivExpr expr1 expr2, t) =
  ands [checkExpr env expr1, checkExpr env expr2]
checkExpr env (TUnaryMinusExpr expr, t) =
  checkExpr env expr
checkExpr env (TBangExpr expr, t) = checkExpr env expr
checkExpr env (TCallExpr funexpr argexpr, t) =
  ands [checkExpr env funexpr, checkExpr env argexpr]
checkExpr env (TListExpr exprs, t) =
  ands (List.map (checkExpr env) exprs)
checkExpr env (TTupleExpr exprs, t) =
  ands (List.map (checkExpr env) exprs)
checkExpr env (TRecordExpr fields, t) =
  ands (List.map ((checkExpr env) . snd) fields)
checkExpr env (TLValue lvexpr, t) =
  checkLvalExpr env lvexpr
checkExpr env (TLambdaExpr mexprs stmt, t) =
  ands (checkStmt env stmt : (List.map (checkMatchExpr env) mexprs))

checkMatchExpr :: Env -> TypedMatchExpr -> Writer [CoveringResult] Bool
checkMatchExpr env (mexpr, ty)
  | matchable ty = do
    --tell (covering env (ideal env ty) [(mexpr, ty)])
    return True
  | otherwise =
    return True

checkLvalExpr :: Env -> TypedLValueExpr -> Writer [CoveringResult] Bool
checkLvalExpr env (TVarExpr s, t) = return True
checkLvalExpr env (TFieldAccessExpr lvalue s, t) = return True
checkLvalExpr env (TArrayAccessExpr lvalue expr, t) = checkExpr env expr

build :: Env -> [TypedMatchExpr] -> [(MatchTree, MatchEdge)]
build env ((mexpr, ty):tmexprs) =
  case (mexpr, ty) of
    (TTupleMatchExpr tmexprs, Tuple types) -> List.foldr ($) leafsGen _ _ 
      where leafsGen = zipWith TupleIdx [0..length tmexprs] types
            subtrees = build env tmexprs
    (TListMatchExpr tmexprs, _) -> undefined
    (TRecordMatchExpr fields, _) -> undefined
    (TVarMatch s, _) -> undefined
    (TIntMatchExpr n, _) -> undefined
    (TStringMatchExpr s, _) -> undefined
    (TBoolMatchExpr b, _) -> undefined
build env [] = undefined