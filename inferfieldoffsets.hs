{-# LANGUAGE TupleSections, LambdaCase #-}

module InferFieldOffsets(construct) where

import Prelude hiding (lookup)
import Types
import TypedAst
import TypeUtils
import Control.Arrow
import qualified Data.List as List
import Data.Map(Map)
import Data.Set(Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State.Lazy
import Data.Traversable hiding (mapM)
import Control.Applicative hiding (empty)

newtype Var = Var Int
  deriving (Show, Ord, Eq)

type FieldMapEntry = Map String Var
newtype FieldMap = FieldMap (Map Type FieldMapEntry)
  deriving Show

newtype Equalities = Equalities (Set (Var, Var))
  deriving Show
  
type ST = (Var, FieldMap, Equalities)

lookup :: Type -> FieldMap -> Maybe FieldMapEntry
lookup ty (FieldMap fm) = Map.lookup ty fm

insertEntry :: (Var -> State ST ()) ->
               Type -> String -> State ST ()
insertEntry hit ty s =
  gets fieldmap >>= return . lookup ty >>= \case
       Just entry ->
         case Map.lookup s entry of
           Just var -> hit var
  where fieldmap (_, fm, _)= fm
           
insert :: Type -> FieldMapEntry -> FieldMap -> FieldMap
insert t e (FieldMap fm) = FieldMap (Map.insert t e fm)

add :: Type -> String -> Var -> State ST ()
add ty s e =
  modify . second $ \fm ->
    case lookup ty fm of
     Just fields ->
      case Map.lookup s fields of
        Just e' -> fm
        Nothing -> insert ty (Map.insert s e fields) fm
     Nothing -> insert ty (Map.singleton s e) fm
  where second f (a, b, c) = (a, f b, c) 

construct :: Env -> [TypedDecl] -> (FieldMap, Equalities)
construct env decls = (fm, eqs)
  where (_, fm, eqs) = execState (mapM visitDecl decls)
                     (Var 0, FieldMap Map.empty, Equalities Set.empty)

visitDecl :: TypedDecl -> State ST ()
visitDecl (TFunDecl _ _ args ty stmt) =
  mapM visitMatchExpr args >> visitStmt stmt >> visitType ty
visitDecl (TTypeDecl _ _ ty) = visitType ty

visitStmt :: TypedStatement -> State ST ()
visitStmt (TIfStatement e stmt Nothing) =
  visitExpr e >> visitStmt stmt
visitStmt (TIfStatement e stmt1 (Just stmt2)) =
  visitExpr e >> visitStmt stmt1 >> visitStmt stmt2
visitStmt (TWhileStatement e stmt) =
  visitExpr e >> visitStmt stmt
visitStmt (TForStatement me e stmt) =
  visitMatchExpr me >> visitExpr e >> visitStmt stmt
visitStmt (TCompoundStatement stmts) =
  mapM_ visitStmt stmts
visitStmt (TAssignStatement lhs e) =
  either visitMatchExpr visitLValueExpr lhs >> visitExpr e
visitStmt (TMatchStatement e matches) =
  visitExpr e >> mapM_ visit matches
  where visit (me, stmt) = visitMatchExpr me >> visitStmt stmt
visitStmt (TReturnStatement e) = visitExpr e
visitStmt TBreakStatement = return ()
visitStmt TContinueStatement = return ()
visitStmt (TDeclStatement decl) = visitDecl decl

visitExprs :: [TypedExpr] -> State ST ()
visitExprs = mapM_ visitExpr

visitExpr :: TypedExpr -> State ST ()
visitExpr (e, ty) = visitType ty >> visitExpr' e

visitExpr' :: TExpr -> State ST ()
visitExpr' (TIntExpr _) = return ()
visitExpr' (TRealExpr _) = return ()
visitExpr' (TBoolExpr _) = return ()
visitExpr' (TStringExpr _) = return ()
visitExpr' (TOrExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TAndExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TEqExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TNeqExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TLtExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TGtExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TLeExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TGeExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TAddExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TSubExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TMultExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TDivExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TUnaryMinusExpr e) = visitExpr e
visitExpr' (TBangExpr e) = visitExpr e
visitExpr' (TCallExpr e1 e2) = visitExprs [e1, e2]
visitExpr' (TListExpr es) = visitExprs es
visitExpr' (TRecordExpr fields) = mapM_ (visitExpr . snd) fields
visitExpr' (TTupleExpr es) = visitExprs es
visitExpr' (TLValue lve) = visitLValueExpr lve
visitExpr' (TLambdaExpr mes stmt) = mapM_ visitMatchExpr mes

visitMatchExpr :: TypedMatchExpr -> State ST ()
visitMatchExpr (me, ty) = visitType ty >> visitMatchExpr' me

visitMatchExprs :: [TypedMatchExpr] -> State ST ()
visitMatchExprs = mapM_ visitMatchExpr

visitMatchExpr' :: TMatchExpr -> State ST ()
visitMatchExpr' (TTupleMatchExpr mes) = visitMatchExprs mes
visitMatchExpr' (TListMatchExpr mes) = visitMatchExprs mes
visitMatchExpr' (TRecordMatchExpr fields) = mapM_ (visitMatchExpr . snd) fields
visitMatchExpr' (TVarMatch _) = return ()
visitMatchExpr' (TIntMatchExpr _) = return ()
visitMatchExpr' (TStringMatchExpr _) = return ()
visitMatchExpr' (TBoolMatchExpr _) = return ()

visitLValueExpr :: TypedLValueExpr -> State ST ()
visitLValueExpr (lve, ty) = visitType ty >> visitLValueExpr' lve

visitLValueExpr' :: TLValueExpr -> State ST ()
visitLValueExpr' (TVarExpr _) = return ()
visitLValueExpr' (TFieldAccessExpr lve _) = visitLValueExpr lve
visitLValueExpr' (TArrayAccessExpr lve e) = visitLValueExpr lve >> visitExpr e

freshVar :: State ST Var
freshVar =
  do var <- gets (\(vars, _, _) -> vars)
     modify (\(Var n, fm, eqs) -> (Var $ n+1, fm, eqs))
     return var

equality :: Var -> Var -> Equalities -> Equalities
equality v1 v2 (Equalities eqs) = Equalities $ Set.insert (v1, v2) eqs
     
addEquality :: Var -> Var -> State ST ()
addEquality v1 v2 = modify (\(vars, fm, eqs) -> (vars, fm, equality v1 v2 eqs))

unify :: Type -> Type -> State ST ()
unify r1@(Record _ fields1) r2@(Record _ fields2) =
  forM_ fields1 $ \(k, _) ->
    case List.lookup k fields2 of
      Just _ ->
        freshVar >>= \var ->
        insertEntry (addEquality var) r1 k >>
        insertEntry (addEquality var) r2 k
      Nothing ->
        insertEntry (const $ return ()) r1 k

records :: Type -> [Type]
records ty@(Record _ _) = [ty]
records (Union ty1 ty2) = records ty1 ++ records ty2
records (Forall _ ty) = records ty
records _ = []

fields :: Type -> [(String, Type)]
fields (Record _ fields) = fields
fields _ = []

visitType :: Type -> State ST ()
visitType IntType = return ()
visitType BoolType = return ()
visitType StringType = return ()
visitType RealType = return ()
visitType Error = return ()
visitType (Name s tys) = visitTypes tys
visitType (Array ty) = visitType ty
visitType (Tuple tys) = visitTypes tys
visitType ty@(Record _ fields) =
  replicateM n freshVar >>= \vars ->
    mapM_ (uncurry $ add ty) (List.zip names vars) >> mapM_ visitType tys
  where n = List.length fields
        (names, tys) = List.unzip fields
visitType (Forall uint ty) = visitType ty
visitType (Arrow tyDom tyCod) = visitType tyDom >> visitType tyCod
visitType (Union ty1 ty2) =
  visitType ty1 >> visitType ty2 >>
    let recs = [(r1, r2) | r1 <- records ty1, r2 <- records ty2]
    in mapM_ (uncurry unify) recs
visitType (Intersect ty1 ty2) = visitType ty1 >> visitType ty2
visitType (TypeVar uint) = return ()

visitTypes :: [Type] -> State ST ()
visitTypes = mapM_ visitType