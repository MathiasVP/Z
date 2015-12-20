{-# LANGUAGE RankNTypes #-} --Required for type checking instanceOf
module MatchCheck where

import Prelude hiding (and)
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
  
data Pattern = BottomPattern Type --Match nothing of given type
             | TopPattern Type --Match anything of given type
             | IntPattern Int
             | StringPattern String
             | BoolPattern Bool
             | ArrayPattern [Pattern]
             | TuplePattern [Pattern]
             | RecordPattern [(String, Pattern)]
             | UnionPattern Pattern Pattern
             | DifferencePattern Pattern Pattern
  deriving Eq

instance Show Pattern where
  show (BottomPattern _) = "_"
  show (TopPattern _) = "_"
  show (IntPattern n) = show n
  show (StringPattern s) = "\"" ++ s ++ "\""
  show (BoolPattern b) = show b
  show (ArrayPattern ps) = "[" ++ List.intercalate ", " (List.map show ps) ++ "]"
  show (TuplePattern ps) = "(" ++ List.intercalate ", " (List.map show ps) ++ ")"
  show (RecordPattern ps) = "{" ++ List.intercalate ", " (List.map f ps) ++ "}"
    where f (s, p) = s ++ " = " ++ show p
  show (UnionPattern p@(DifferencePattern p1 p2) p3) = "(" ++ show p ++ ") | " ++ show p3
  show (UnionPattern p1 p@(DifferencePattern p2 p3)) = show p1 ++ " | (" ++ show p ++ ")"
  show (UnionPattern p1 p2) = show p1 ++ " | " ++ show p2
  show (DifferencePattern p@(UnionPattern p1 p2) p3) = "(" ++ show p ++ ")" ++ " - " ++ show p3
  show (DifferencePattern p1 p@(UnionPattern p2 p3)) = show p1 ++ " - (" ++ show p ++ ")"
  show (DifferencePattern p1 p2) = show p1 ++ " - " ++ show p2

formatMatchWarning :: CoveringResult -> String
formatMatchWarning Covered = ""
formatMatchWarning (Nonexhaustive p) =
  unlines ["Warning: Match is not exhaustive.",
           "\tMissing pattern: " ++ show p]
formatMatchWarning (Redundant tmexpr) =
  unlines ["Warning: Match has redundant pattern.",
           "\tRedundant pattern: " ++ ppTypedMatchExpr tmexpr]

matchCheck :: [TypedDecl] -> Writer [CoveringResult] Bool
matchCheck = allM check

check :: TypedDecl -> Writer [CoveringResult] Bool
check (TTypeDecl name args ty) = return True
check (TFunDecl name tyargs tmexprs retTy stmt) =
  ands (checkStmt stmt : List.map checkMatchExpr tmexprs)

and :: Monad m => m Bool -> m Bool -> m Bool
and = liftM2 (&&)

ands = List.foldr and (return True)

checkStmt :: TypedStatement -> Writer [CoveringResult] Bool
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
checkStmt (TMatchStatement (expr, ty) actions) = do
  tell (covering (ideal ty) (List.map fst actions))
  return True
checkStmt (TReturnStatement expr) = checkExpr expr
checkStmt TBreakStatement = return True
checkStmt TContinueStatement = return True
checkStmt (TDeclStatement decl) = check decl

checkExpr :: TypedExpr -> Writer [CoveringResult] Bool
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

checkMatchExpr :: TypedMatchExpr -> Writer [CoveringResult] Bool
checkMatchExpr (mexpr, ty) = do
  tell (covering (ideal ty) [(mexpr, ty)])
  return True

checkLvalExpr :: TypedLValueExpr -> Writer [CoveringResult] Bool
checkLvalExpr (TVarExpr s, t) = return True
checkLvalExpr (TFieldAccessExpr lvalue s, t) = return True
checkLvalExpr (TArrayAccessExpr lvalue expr, t) = checkExpr expr

ideal :: Type -> Pattern
ideal IntType = TopPattern IntType
ideal BoolType = TopPattern BoolType
ideal StringType = TopPattern StringType
ideal (Name s tys) = error "NYI"
ideal (Array ty) = TopPattern (Array ty)
ideal (Tuple tys) = TuplePattern (List.map ideal tys)
ideal (Record _ fields) = RecordPattern (List.map (\(s, ty) -> (s, ideal ty)) fields)
ideal (Forall _ ty) = error "NYI"
ideal (Union ty1 ty2) = unionPattern p1 p2
  where p1 = ideal ty1
        p2 = ideal ty2
ideal (Intersect ty1 ty2) = error "NYI"

unionPattern :: Pattern -> Pattern -> Pattern
unionPattern (BottomPattern IntType) p@(IntPattern n) = p
unionPattern (BottomPattern StringType) p@(StringPattern s) = p
unionPattern (BottomPattern BoolType) p@(BoolPattern b) = p
unionPattern (BottomPattern (Array ty)) p@(ArrayPattern ps) =
  ArrayPattern (List.map (unionPattern (BottomPattern ty)) ps)
unionPattern (BottomPattern (Tuple tys)) p@(TuplePattern ps)
  | List.length tys == List.length ps =
    TuplePattern (List.zipWith unionPattern (List.map BottomPattern tys) ps)
unionPattern (BottomPattern (Record _ fieldst)) (RecordPattern fieldsp)
  | subdomain mapt mapp =
    RecordPattern (List.map unionIfPresent fieldsp)
  where subdomain = Map.isSubmapOfBy (const (const True))
        mapt = Map.fromList fieldst
        mapp = Map.fromList fieldsp
        
        unionIfPresent (s, p) =
          case Map.lookup s mapt of
            Just t -> (s, unionPattern (BottomPattern t) p)
            Nothing -> (s, p)
unionPattern (BottomPattern ty1) p@(TopPattern ty2)
  | ty1 == ty2 = p
unionPattern (IntPattern n) p@(TopPattern IntType) = p
unionPattern (StringPattern s) p@(TopPattern StringType) = p
unionPattern (BoolPattern b) p@(TopPattern BoolType) = p
unionPattern (ArrayPattern ps) p@(TopPattern (Array ty))
  | List.all (isTop . unionPattern (TopPattern ty)) ps = p
unionPattern (TuplePattern ps) p@(TopPattern (Tuple tys))
  | List.length tys == List.length ps &&
    List.all isTop (List.zipWith unionPattern (List.map TopPattern tys) ps) = p
unionPattern (RecordPattern fieldsp) p@(TopPattern (Record _ fieldst))
  | subdomain mapt mapp &&
    List.all isTop (List.map (snd . unionIfPresent) fieldsp) = p
  where subdomain = Map.isSubmapOfBy (const (const True))
        mapt = Map.fromList fieldst
        mapp = Map.fromList fieldsp
        
        unionIfPresent (s, p) =
          case Map.lookup s mapt of
            Just t -> (s, unionPattern (TopPattern t) p)
            Nothing -> (s, p)
unionPattern p@(IntPattern n1) (IntPattern n2)
  | n1 == n2 = p
unionPattern p@(StringPattern s1) (StringPattern s2)
  | s1 == s2 = p
unionPattern p@(BoolPattern b1) (BoolPattern b2)
  | b1 == b2 = p
unionPattern (ArrayPattern ps1) (ArrayPattern ps2)
  | List.length ps1 == List.length ps2 =
    ArrayPattern (List.zipWith unionPattern ps1 ps2)
unionPattern (TuplePattern ps1) (TuplePattern ps2)
  | List.length ps1 == List.length ps2 =
    TuplePattern (List.zipWith unionPattern ps1 ps2)
unionPattern (RecordPattern fields1) (RecordPattern fields2)
  | Map.keysSet map1 == Map.keysSet map2 =
    RecordPattern (Map.toList $ Map.unionWith unionPattern map1 map2)
  where map1 = Map.fromList fields1
        map2 = Map.fromList fields2
unionPattern (UnionPattern p1 p2) (UnionPattern p3 p4) =
  UnionPattern (UnionPattern (UnionPattern p1 p2) p3) p4
unionPattern p1 (UnionPattern p2 p3) = UnionPattern (UnionPattern p1 p2) p3
unionPattern p1 p2 = UnionPattern p1 p2

isBottom :: Pattern -> Bool
isBottom (BottomPattern _) = True
isBottom (ArrayPattern ps) = List.all isBottom ps
isBottom (TuplePattern ps) = List.all isBottom ps
isBottom (UnionPattern p1 p2) = isBottom p1 && isBottom p2
isBottom (DifferencePattern p1 p2) = instanceOf List.all p1 p2
isBottom _ = False

isTop :: Pattern -> Bool
isTop (TopPattern _) = True
isTop (ArrayPattern ps) = List.all isTop ps
isTop (TuplePattern ps) = List.all isTop ps
isTop (UnionPattern p1 p2) = isTop p1 && isTop p2
isTop (DifferencePattern p1 p2) = instanceOf List.all p1 p2
isTop _ = False

refine :: Pattern -> Pattern -> Pattern
refine p q = ref p q
  where
    ref :: Pattern -> Pattern -> Pattern
    ref p (BottomPattern _) = p
    ref (BottomPattern ty) _ = BottomPattern ty
    ref (TopPattern ty1) (TopPattern ty2)
      | ty1 == ty2 = BottomPattern ty1
      | otherwise  = DifferencePattern (TopPattern ty1) (TopPattern ty2)
    ref p1 (UnionPattern p2 p3) = ref (ref p1 p2) p3
    ref p1 (DifferencePattern p2 p3) = ref p1 (ref p2 p3)
    ref (IntPattern _) (TopPattern IntType) = BottomPattern IntType
    ref (IntPattern n1) (IntPattern n2)
      | n1 == n2  = BottomPattern IntType
      | otherwise = IntPattern n1
    ref (StringPattern _) (TopPattern StringType) = BottomPattern StringType
    ref (StringPattern s1) (StringPattern s2)
      | s1 == s2  = BottomPattern StringType
      | otherwise = StringPattern s1
    ref (BoolPattern _) (TopPattern BoolType) = BottomPattern BoolType
    ref (BoolPattern b1) (BoolPattern b2)
      | b1 == b2  = BottomPattern BoolType
      | otherwise = BoolPattern b1
    ref (ArrayPattern ps1) (ArrayPattern ps2)
      | n1 > n2   = ArrayPattern (zipWith ref ps1 ps2 ++ List.drop n2 ps1)
      | n1 < n2   = ArrayPattern (zipWith ref ps1 ps2 ++ List.drop n1 ps2)
      | otherwise = ArrayPattern (zipWith ref ps1 ps2)
      where n1 = List.length ps1
            n2 = List.length ps2
    ref (ArrayPattern ps) (TopPattern (Tuple tys))
      | List.length ps == List.length tys =
        ArrayPattern (zipWith ref ps (List.map TopPattern tys))
    ref (TuplePattern ps1) (TuplePattern ps2)
      | n1 > n2   = TuplePattern (zipWith ref ps1 ps2 ++ List.drop n2 ps1)
      | n1 < n2   = TuplePattern (zipWith ref ps1 ps2 ++ List.drop n1 ps2)
      | otherwise = TuplePattern (zipWith ref ps1 ps2)
      where n1 = List.length ps1
            n2 = List.length ps2
    ref (RecordPattern fields1) (RecordPattern fields2) =
      DifferencePattern (RecordPattern include) (RecordPattern exclude)
      where (include, exclude) = foldr f ([], []) fields1
            f (s, p) (include, exclude) =
              case Map.lookup s map2 of
                Just p' -> ((s, ref p p'):include, exclude)
                Nothing -> (include, (s, p):exclude)
            map2 = Map.fromList fields2
    ref (DifferencePattern p1 p2) p3 =
      case ref p1 p3 of
        DifferencePattern q1 q2 -> DifferencePattern q1 (unionPattern p2 q2)
        q -> ref q p2
    ref p1 p2 = DifferencePattern p1 p2

create :: TypedMatchExpr -> Pattern
create (TTupleMatchExpr mexprs, _) = TuplePattern (List.map create mexprs)
create (TListMatchExpr mexprs, _) = ArrayPattern (List.map create mexprs)
create (TRecordMatchExpr fields, _) = RecordPattern (List.map f fields)
  where f (s, tmexpr) = (s, create tmexpr)
create (TVarMatch _, t) = ideal t
create (TIntMatchExpr n, _) = IntPattern n
create (TStringMatchExpr s, _) = StringPattern s
create (TBoolMatchExpr b, _) = BoolPattern b

{- pred = List.all => [p1, p2, ..., pN] is an instance of [q1, q2, ..., qN] iff
                      for all i. pi is an instance of qi
   pred = List.any => [p1, p2, ..., pN] is an instance of [q1, q2, ..., qN] iff
                      for some i. pi is an instance of qi -}
instanceOf :: (forall a . (a -> Bool) -> [a] -> Bool) -> Pattern -> Pattern -> Bool
instanceOf pred _ (BottomPattern _) = False
instanceOf pred (BottomPattern IntType) (IntPattern _) = True
instanceOf pred (BottomPattern StringType) (StringPattern _) = True
instanceOf pred (BottomPattern BoolType) (BoolPattern _) = True
instanceOf pred (BottomPattern (Array ty)) (ArrayPattern ps) =
  List.all (instanceOf pred (BottomPattern ty)) ps
instanceOf pred (BottomPattern (Tuple tys)) (TuplePattern ps)
  | List.length tys == List.length ps =
    List.all (uncurry (instanceOf pred)) (List.zip (List.map BottomPattern tys) ps)
instanceOf pred (BottomPattern (Record _ fieldst)) (RecordPattern fieldsp) =
  Map.isSubmapOfBy (instanceOf pred) mapt mapp
  where mapp = Map.fromList fieldsp
        mapt = Map.fromList (List.map (\(s, ty) -> (s, BottomPattern ty)) fieldst)
instanceOf pred (TopPattern ty1) (TopPattern ty2)
  | ty1 == ty2 = True
  | otherwise  = False
instanceOf pred (TopPattern (Array ty)) (ArrayPattern ps) =
  List.all (instanceOf pred (TopPattern ty)) ps
instanceOf pred (TopPattern (Tuple tys)) (TuplePattern ps)
  | List.length tys == List.length ps =
    List.all (uncurry (instanceOf pred)) (List.zip (List.map TopPattern tys) ps)
instanceOf pred (TopPattern (Record _ fieldst)) (RecordPattern fieldsp)
  | List.map fst mapt == List.map fst mapp =
    List.all (uncurry (instanceOf pred)) (List.zip (List.map snd mapt) (List.map snd mapp))
  where mapt = sort (List.map (\(s, ty) -> (s, TopPattern ty)) fieldst)
        mapp = sort fieldsp
        sort = List.sortBy (comparing fst)
instanceOf pred (IntPattern _) (TopPattern IntType) = True
instanceOf pred (StringPattern _) (TopPattern StringType) = True
instanceOf pred (BoolPattern _) (TopPattern BoolType) = True
instanceOf pred (ArrayPattern ps) (TopPattern (Array ty)) =
  List.all (flip (instanceOf pred) (TopPattern ty)) ps
instanceOf pred (TuplePattern ps) (TopPattern (Tuple tys))
  | List.length ps == List.length tys =
    List.all (uncurry (instanceOf pred)) (List.zip ps (List.map TopPattern tys))
instanceOf pred (RecordPattern fieldsp) (TopPattern (Record _ fieldst)) =
  Map.isSubmapOfBy (instanceOf pred) mapp mapt
  where mapp = Map.fromList fieldsp
        mapt = Map.fromList (List.map (\(s, ty) -> (s, TopPattern ty)) fieldst)
instanceOf pred (IntPattern n1) (IntPattern n2)
  | n1 == n2 = True
  | otherwise = False
instanceOf pred (StringPattern s1) (StringPattern s2)
  | s1 == s2  = True
  | otherwise = False
instanceOf pred (BoolPattern b1) (BoolPattern b2)
  | b1 == b2  = True
  | otherwise = False
instanceOf pred (ArrayPattern ps1) (ArrayPattern ps2)
  | n1 == n2 = pred (uncurry (instanceOf pred)) (List.zip ps1 ps2)
  | otherwise = False
  where n1 = List.length ps1
        n2 = List.length ps2
instanceOf pred (TuplePattern ps1) (TuplePattern ps2)
  | n1 == n2 = pred (uncurry (instanceOf pred)) (List.zip ps1 ps2)
  | otherwise = False
  where n1 = List.length ps1
        n2 = List.length ps2
instanceOf pred (RecordPattern fields1) (RecordPattern fields2)
  = Map.isSubmapOfBy (instanceOf pred) map1 map2
  where map1 = Map.fromList (List.filter (\(s, p) -> not (isBottom p)) fields1)
        map2 = Map.fromList fields2
instanceOf pred p1 (DifferencePattern p2 p3)
  | instanceOf pred p1 p2 = not (instanceOf List.all p1 p3)
  | otherwise        = False
instanceOf pred (UnionPattern p1 p2) p3 =
  instanceOf pred p1 p3 && instanceOf pred p2 p3
instanceOf pred p1 (UnionPattern p2 p3) =
  instanceOf pred p1 p2 || instanceOf pred p1 p3
instanceOf pred p1 p2 = False

covering :: Pattern -> [TypedMatchExpr] -> [CoveringResult]
covering p []
  | isBottom p = [Covered]
  | otherwise  = [Nonexhaustive p]
covering p (mexpr:mexprs)
  | instanceOf List.any q p = covering (refine p q) mexprs
  | otherwise      =
    Redundant mexpr : covering (refine p q) mexprs
  where q = create mexpr