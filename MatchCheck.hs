{-# LANGUAGE LambdaCase #-}
module MatchCheck where

import Prelude hiding (and)
import TypedAst
import TypeUtils
import Control.Monad.State.Lazy
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Maybe
import Control.Monad.Loops
import Control.Monad.Writer.Lazy

data CoverResult
  = NonExhaustive [TypedMatchExpr]
  | Redundant [TypedMatchExpr]
  | NonExhaustiveAndRedundant [TypedMatchExpr] [TypedMatchExpr]
  | Perfect
  deriving (Show, Eq)

matchCheck :: [TypedDecl] -> Writer String Bool
matchCheck = allM check

check :: TypedDecl -> Writer String Bool
check (TTypeDecl name args ty) = return True
check (TFunDecl name tyargs tmexprs retTy stmt) =
  ands (checkStmt stmt : List.map checkMatchExpr tmexprs)

and :: Monad m => m Bool -> m Bool -> m Bool
and = liftM2 (&&)

ands = List.foldr and (return True)

format pp mexprs = List.intercalate ", " (List.map pp mexprs)

ppMatchExpr :: TypedMatchExpr -> String
ppMatchExpr (TTupleMatchExpr mexprs, _) = "(" ++ format ppMatchExpr mexprs ++ ")"
ppMatchExpr (TListMatchExpr mexprs, _) = "[" ++ format ppMatchExpr mexprs ++ "]"
ppMatchExpr (TRecordMatchExpr fields, _) = "{" ++ format ppField fields ++ "}"
  where ppField (name, mexpr) = name ++ " = " ++ ppMatchExpr mexpr
ppMatchExpr (TVarMatch s, ty) = s ++ ":" ++ show ty
ppMatchExpr (TIntMatchExpr n, ty) = show n ++ ":" ++ show ty
ppMatchExpr (TStringMatchExpr s, ty) = s ++ ":" ++ show ty
ppMatchExpr (TBoolMatchExpr b, ty) = show b ++ ":" ++ show ty

formatMatches :: Int -> [TypedMatchExpr] -> String
formatMatches _ [] = ""
formatMatches n (mexpr:tl)
  | n > 0 = "\t" ++ ppMatchExpr mexpr ++ " => ...\n" ++ formatMatches (n-1) tl
  | otherwise = "\t..."

checkStmt :: TypedStatement -> Writer String Bool
checkStmt (TIfStatement expr stmtThen Nothing) =
  ands [checkExpr expr, checkStmt stmtThen]
checkStmt (TIfStatement expr stmtThen (Just stmtElse)) =
  ands [checkExpr expr, checkStmt stmtThen, checkStmt stmtElse]
checkStmt (TWhileStatement expr stmt) =
  ands [checkExpr expr, checkStmt stmt]
checkStmt (TForStatement mexpr expr stmt) =
  ands [checkMatchExpr mexpr, checkExpr expr, checkStmt stmt]
checkStmt (TCompoundStatement stmts) =
  ands (List.map checkStmt stmts)
checkStmt (TAssignStatement (Left mexpr) expr) =
  ands [checkMatchExpr mexpr, checkExpr expr]
checkStmt (TAssignStatement (Right lvexpr) expr) =
  ands [checkLvalExpr lvexpr, checkExpr expr]
checkStmt (TMatchStatement (expr, ty) actions) =
  case covered ty (List.map fst actions) of
    NonExhaustive nonex -> do
      tell (unlines ["Warning: match nonexhaustive",
                     formatMatches 5 nonex])
      withResult True
    Redundant red -> do
      tell (unlines ["Warning: match redundant",
                     formatMatches 5 red])
      withResult True
    NonExhaustiveAndRedundant nonex red -> do
      tell (unlines ["Warning: match nonexhaustive",
                     formatMatches 5 nonex])
      tell (unlines ["Warning: match redundant",
                     formatMatches 5 red])
      withResult True
    Perfect -> withResult True
    where withResult res = ands ([checkExpr (expr, ty), return res] ++ List.map (checkStmt . snd) actions)
checkStmt (TReturnStatement expr) = checkExpr expr
checkStmt TBreakStatement = return True
checkStmt TContinueStatement = return True
checkStmt (TDeclStatement decl) = check decl

checkExpr :: TypedExpr -> Writer String Bool
checkExpr (TIntExpr n, t) = return True
checkExpr (TRealExpr d, t) = return True
checkExpr (TBoolExpr b, t) = return True
checkExpr (TStringExpr s, t) = return True
checkExpr (TOrExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TAndExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TEqExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TNeqExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TLtExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TGtExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TLeExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TGeExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TAddExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TSubExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TMultExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TDivExpr expr1 expr2, t) =
  ands [checkExpr expr1, checkExpr expr2]
checkExpr (TUnaryMinusExpr expr, t) =
  checkExpr expr
checkExpr (TBangExpr expr, t) = checkExpr expr
checkExpr (TCallExpr funexpr argexpr, t) =
  ands [checkExpr funexpr, checkExpr argexpr]
checkExpr (TListExpr exprs, t) =
  ands (List.map checkExpr exprs)
checkExpr (TTupleExpr exprs, t) =
  ands (List.map checkExpr exprs)
checkExpr (TRecordExpr fields, t) =
  ands (List.map (checkExpr . snd) fields)
checkExpr (TLValue lvexpr, t) =
  checkLvalExpr lvexpr
checkExpr (TLambdaExpr mexprs stmt, t) =
  ands (checkStmt stmt : (List.map checkMatchExpr mexprs))

checkMatchExpr :: TypedMatchExpr -> Writer String Bool
checkMatchExpr (mexpr, ty) = do
  case covered ty [(mexpr, ty)] of
    NonExhaustive nonex -> do
      tell (unlines ["Warning: match nonexhaustive",
                     formatMatches 5 nonex])
    Redundant red -> do
      tell (unlines ["Warning: match redundant",
                     formatMatches 5 red])
    NonExhaustiveAndRedundant nonex red -> do
      tell (unlines ["Warning: match nonexhaustive",
                     formatMatches 5 nonex])
      tell (unlines ["Warning: match redundant",
                     formatMatches 5 red])
    Perfect -> return ()
  return True

checkLvalExpr :: TypedLValueExpr -> Writer String Bool
checkLvalExpr lvexpr = return True

combine :: CoverResult -> CoverResult -> CoverResult
combine (NonExhaustive nonex1) (NonExhaustive nonex2) =
  NonExhaustive (List.intersect nonex1 nonex2)
combine (NonExhaustive nonex) (Redundant red) =
  NonExhaustiveAndRedundant nonex red
combine (NonExhaustive nonex1) (NonExhaustiveAndRedundant nonex2 red) =
  NonExhaustiveAndRedundant (List.intersect nonex1 nonex2) red
combine (NonExhaustive nonex) Perfect =
  NonExhaustive nonex

combine (Redundant red) (NonExhaustive nonex) =
  NonExhaustiveAndRedundant nonex red
combine (Redundant red1) (Redundant red2) =
  Redundant (List.union red1 red2)
combine (Redundant red1) (NonExhaustiveAndRedundant nonex red2) =
  NonExhaustiveAndRedundant nonex (List.union red1 red2)
combine (Redundant red) Perfect = Redundant red
  
combine (NonExhaustiveAndRedundant nonex1 red) (NonExhaustive nonex2) =
  NonExhaustiveAndRedundant (List.intersect nonex1 nonex2) red
combine (NonExhaustiveAndRedundant nonex red1) (Redundant red2) =
  NonExhaustiveAndRedundant nonex (List.union red1 red2)
combine (NonExhaustiveAndRedundant nonex1 red1) (NonExhaustiveAndRedundant nonex2 red2) =
  NonExhaustiveAndRedundant (List.intersect nonex1 nonex2) (List.union red1 red2)
combine (NonExhaustiveAndRedundant nonex red) Perfect =
  NonExhaustiveAndRedundant nonex red

combine Perfect res = res
  
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM p = foldr f (return [])
    where
      f x xs = p x >>= \case
        Nothing -> xs
        Just y -> xs >>= return . (:) y
                
covered :: Type -> [TypedMatchExpr] -> CoverResult
covered t tmexpr = evalState (covered' t tmexpr) Set.empty
  where
    strings = [c:s | s <- "":strings, c <- ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z']]
    
    covered' :: Type -> [TypedMatchExpr] -> State (Set TypedMatchExpr) CoverResult
    covered' IntType [] = do
      nonexs <- mapMaybeM f [0..]
      return $ NonExhaustive nonexs
      where f n = gets (Set.member (TIntMatchExpr n, IntType)) >>= \case
                    True -> return Nothing
                    False -> return $ Just (TIntMatchExpr n, IntType)
    covered' IntType [(TVarMatch _, IntType)] = return Perfect
    covered' IntType ((TVarMatch _, IntType):ps) = return $ Redundant ps
    covered' IntType (m@(TIntMatchExpr n, t):ps) =
      gets (Set.member m) >>= \case
        True -> do
          modify (Set.insert m)
          r <- covered' IntType ps
          return $ combine (Redundant [m]) r
        False -> do
          modify (Set.insert m)
          covered' IntType ps
    covered' StringType [] = do
      nonexs <- mapMaybeM f strings
      return $ NonExhaustive nonexs
      where f s = gets (Set.member (TStringMatchExpr s, StringType)) >>= \case
                    True -> return Nothing
                    False -> return $ Just (TStringMatchExpr s, StringType)
    covered' StringType [(TVarMatch _, StringType)] = return Perfect
    covered' StringType ((TVarMatch _, StringType):ps) = return $ Redundant ps
    covered' StringType (m@(TStringMatchExpr s, t):ps) =
      gets (Set.member m) >>= \case
        True -> do
          modify (Set.insert m)
          r <- covered' StringType ps
          return $ combine (Redundant [m]) r
        False -> do
          modify (Set.insert m)
          covered' StringType ps
    covered' BoolType [] = do
      b1 <- has False
      b2 <- has True
      case (b1, b2) of
        (False, False) ->
          return $ NonExhaustive [(TBoolMatchExpr False, BoolType),
                                  (TBoolMatchExpr True, BoolType)]
        (False, True) ->
          return $ NonExhaustive [(TBoolMatchExpr False, BoolType)]
        (True, False) ->
          return $ NonExhaustive [(TBoolMatchExpr True, BoolType)]
        (True, True) -> return Perfect
      where has b = gets (Set.member (TBoolMatchExpr b, BoolType))
    covered' BoolType [(TVarMatch _, BoolType)] = return Perfect
    covered' BoolType ((TVarMatch _, BoolType):ps) = return $ Redundant ps
    covered' BoolType (m@(TBoolMatchExpr b, t):ps) =
      gets (Set.member m) >>= \case
        True -> do
          modify (Set.insert m)
          r <- covered' BoolType ps
          return $ combine (Redundant [m]) r
        False -> do
          modify (Set.insert m)
          covered' BoolType ps
    covered' (Tuple ts) [(TTupleMatchExpr tmexprs, Tuple _)] = do
      liftM List.head $ mapM cover (List.zip ts tmexprs)
      where
        cover (t, tmexpr) = do
          s <- get
          r <- covered' t [tmexpr]
          put s
          modify (Set.insert tmexpr)
          return r