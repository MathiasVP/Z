{-# LANGUAGE TupleSections, LambdaCase #-}

module InferFieldOffsets where

import Prelude hiding (lookup)
import Types
import TypedAst
import TypeUtils
import Control.Arrow
import qualified Data.List as List
import Data.Map(Map)
import qualified Data.Map as Map
import Control.Monad.State.Lazy
import Data.Traversable hiding(mapM)
import Control.Applicative hiding(empty)

newtype Var = Var Int
  deriving Show

type FieldMapEntry = Map String Var
newtype FieldMap = FieldMap (Map Type FieldMapEntry)
  deriving Show

type ST = (Var, FieldMap)

lookup :: Type -> FieldMap -> Maybe FieldMapEntry
lookup ty (FieldMap fm) = Map.lookup ty fm

insertEntry :: Type -> String -> State ST ()
insertEntry ty s =
  fieldMap >>= return . lookup ty >>= \case
       Nothing -> freshVar >>= add ty s
       Just entry ->
         case Map.lookup s entry of
           Nothing -> freshVar >>= add ty s
           Just var -> return ()

insert :: Type -> FieldMapEntry -> FieldMap -> FieldMap
insert t e (FieldMap fm) = FieldMap (Map.insert t e fm)

putFieldMap :: FieldMap -> State ST ()
putFieldMap fm =
  gets fst >>= put . (, fm) >> return ()

add :: Type -> String -> Var -> State ST ()
add ty s e =
  do fm <- fieldMap
     let fm' = case lookup ty fm of
                 Just fields -> insert ty (Map.insert s e fields) fm
                 Nothing -> insert ty (Map.singleton s e) fm
     putFieldMap fm'

fieldMap :: State ST FieldMap
fieldMap = gets snd

construct :: Env -> [TypedDecl] -> FieldMap
construct env decls = snd $ execState (mapM visitDecl decls)
                                      (Var 0, FieldMap Map.empty)

visitDecl :: TypedDecl -> State ST ()
visitDecl (TFunDecl _ _ args ty stmt) =
  mapM visitMatchExpr args >> visitStmt stmt >> visitType ty

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

visitTypes = mapM_ visitType

freshVar :: State ST Var
freshVar =
  do var <- gets fst
     modify (\(Var n, fm) -> (Var $ n+1, fm))
     return var
  
unionMapWithM_ :: (Monad m, Ord k) =>
                  (k -> m ()) -> (k -> m ()) ->
                    Map k a -> Map k a -> m ()
unionMapWithM_ f g m1 m2 =
  forM_ (Map.toList m1) $ \(k, _) ->
    case Map.lookup k m2 of
      Just y -> f k
      Nothing -> g k

unify :: Type -> Type -> State ST ()
unify r1@(Record _ fields1) r2@(Record _ fields2) =
  unionMapWithM_
    (\s -> insertEntry r1 s >> insertEntry r2 s)
    (\s -> insertEntry r1 s)
    (Map.fromList fields1) (Map.fromList fields2)


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