{-# LANGUAGE LambdaCase #-}

module TypeInfer where
import Control.Monad
import Control.Monad.State.Lazy
import Data.Ord
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Maybe as Maybe
import Data.Unique
import Data.Set (Set)
import Data.Map (Map)
import TypedAst
import Unification
import Subtype
import Utils
import TypeUtils

extendRecord :: String -> Type -> Type -> Substitution -> Substitution
extendRecord name ty (TypeVar u) subst =
  case follow subst (TypeVar u) of
    Record b fields
      | Maybe.isNothing (List.lookup name fields) ->
        Map.insert u (Record b ((name, ty):fields)) subst
      | otherwise -> Map.insert u (Record b (List.map f fields)) subst
        where f (name', ty')
                | name' == name = (name', ty)
                | otherwise     = (name', ty')
    TypeVar u' -> Map.insert u' (Record True [(name, ty)]) subst

normaliseFields :: Ord a => [(a, b)] -> [(a, b)]
normaliseFields = List.sortBy (comparing fst)

equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2

mergeSubstitution :: Env -> ArgOrd -> Substitution -> Substitution -> IO Substitution
mergeSubstitution env argOrd subst1 subst2 = foldlWithKeyM f subst1 subst2
  where f subst u ty =
          case Map.lookup u subst of
            Nothing -> return $ Map.insert u ty subst
            Just ty' -> do
              (_, subst') <- unify ty ty' env argOrd subst
              return subst'

mergeEnv :: Env -> Env -> ArgOrd -> Substitution -> IO (Env, Substitution)
mergeEnv env1 env2 argOrd subst = foldlWithKeyM f (env1, subst) env2
  where f (env, subst) name ty =
          case Map.lookup name env of
            Nothing -> return (Map.insert name ty env, subst)
            Just ty' -> do
              (ty'', subst') <- unify ty ty' env argOrd subst
              return (Map.insert name ty'' env, subst')

infer :: [Decl] -> IO ([TypedDecl], Env, Substitution)
infer decls = do
  (typeddecls, env, _, subst) <- inferList inferDecl Map.empty Map.empty Map.empty decls
  return (List.map (replaceDecl subst) typeddecls, Map.map (replaceType subst) env, subst)
  where
    inferList :: (a -> Env -> ArgOrd -> Substitution -> IO (b, Env, ArgOrd, Substitution)) ->
                  Env -> ArgOrd -> Substitution -> [a] -> IO ([b], Env, ArgOrd, Substitution)
    inferList inferer env argOrd subst list =
      do (list', env', argOrd', subst') <- foldM f ([], env, argOrd, subst) list
         return (List.reverse list', env', argOrd', subst')
      where f (list', env, argOrd, subst) elem = do
            (elem', env', argOrd', subst') <- inferer elem env argOrd subst
            return (elem' : list', env', argOrd', subst')

    extendArgOrd :: String -> [String] -> ArgOrd -> ArgOrd
    extendArgOrd name targs = Map.insert name (Map.fromList (List.zip [0..] targs))

    inferDecl :: Decl -> Env -> ArgOrd -> Substitution -> IO (TypedDecl, Env, ArgOrd, Substitution)
    inferDecl (TypeDecl name targs ty) env argOrd subst =
      return (TTypeDecl name targs ty, Map.insert name ty env, extendArgOrd name targs argOrd, subst)

    inferDecl (FunDecl name tyArgs args retTy statement) env argOrd subst = do
      (args', env', argOrd', subst') <- inferList (inferMatchExpr Nothing) env argOrd subst args
      retTy' <- Maybe.fromMaybe mkTypeVar (liftM return retTy)
      let types = List.map snd args'
          functionTy = List.foldr (makeForall subst') (makeArrow types retTy') types
          env'' = Map.insert name functionTy env'
      (statement', env''', argOrd'', subst'') <- inferStatement statement env'' argOrd' subst'
      (infRetTy, subst''') <- mergeReturns statement' env''' argOrd subst''
      (b, subst'''') <- subtype infRetTy retTy' env'' argOrd'' subst'''
      case b of
        True ->
          let functionTy' = List.foldr (makeForall subst'''') (makeArrow types retTy') types
              globEnv = Map.insert name functionTy' env
          in return (TFunDecl name tyArgs args' retTy' statement', globEnv, argOrd, subst'''')
        False -> do
          let globEnv = Map.insert name Error env
          putStrLn $ "Error: Couldn't match expected return type '" ++ show retTy' ++
                     "' with actual type '" ++ show infRetTy ++ "'."
          return (TFunDecl name tyArgs args' retTy' statement', globEnv, argOrd, subst)

    commMaybeIO :: Maybe (IO (Maybe t)) -> IO (Maybe (Maybe t))
    commMaybeIO Nothing = return Nothing
    commMaybeIO (Just iom) = iom >>= return . Just

    inferMatchExpr :: Maybe Type -> MatchExpr -> Env -> ArgOrd -> Substitution ->
                      IO (TypedMatchExpr, Env, ArgOrd, Substitution)
    inferMatchExpr tm (TupleMatchExpr mes) env argOrd subst = do
      let uni' env argOrd subst t1 t2 = unify' t1 t2 env argOrd subst
      (mes', env', argOrd', subst') <- do
        types <- replicateM (List.length mes) mkTypeVar
        commMaybeIO (liftM (uni' env argOrd subst (Tuple types)) tm) >>= \case
          Just (Just (Tuple ts, subst')) ->
            inferList (\(me, t) -> inferMatchExpr (Just t) me) env argOrd subst'
                                     (List.zip mes ts)
          Just Nothing -> do
            putStrLn $ "Match error: Couldn't unify expression '" ++
                         show (TupleMatchExpr mes) ++ "' with type '" ++
                         show (Tuple types) ++ "'."
            return ([], env, argOrd, subst)
          Nothing ->
            inferList (inferMatchExpr Nothing) env argOrd subst mes
      return ((TTupleMatchExpr mes', Tuple (List.map typeOf mes')), env', argOrd', subst')

    inferMatchExpr tm (ListMatchExpr mes) env argOrd subst = do
      let uni' env argOrd subst t1 t2 = unify' t1 t2 env argOrd subst
      t <- mkTypeVar
      (mes', env', argOrd', subst') <- do
        commMaybeIO (liftM (uni' env argOrd subst (Array t)) tm) >>= \case
          Just (Just (Array t, subst')) -> inferList (inferMatchExpr (Just t))
                                             env argOrd subst' mes
          Just Nothing -> do
            putStrLn $ "Match error: Couldn't unify expression '" ++
                         show (ListMatchExpr mes) ++ "' with type '" ++
                         show (Array t) ++ "'."
            return ([], env, argOrd, subst)
          Nothing -> inferList (inferMatchExpr Nothing) env argOrd subst mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') env' argOrd' subst'
      return ((TListMatchExpr mes', Array ty), env', argOrd', subst'')

    inferMatchExpr tm (RecordMatchExpr fields) env argOrd subst = do
      let uni' env argOrd subst t1 t2 = unify' t1 t2 env argOrd subst
      (fields', env', argOrd', subst') <- do
        fields' <- forever mkTypeVar >>=
                     return . List.zip (normaliseFields fields)
        let record = Record False (List.map (\((s, _), ty) -> (s, ty)) fields')
        commMaybeIO (liftM (uni' env argOrd subst record) tm) >>= \case
          Just (Just (Record _ fields', subst')) ->
            inferList (\(entry, ty) -> f (Just ty) entry) env argOrd
              subst' (List.zip (normaliseFields fields) typesm)
            where typesm = List.map typeOf (normaliseFields fields')
                  f tm (name, me) env argOrd subst = do
                    (me', env', argOrd', subst') <-
                      inferMatchExpr tm me env argOrd subst
                    return ((name, me'), env', argOrd', subst')
          Just Nothing -> do
            putStrLn $ "Match error: Couldn't unify expression '" ++
                         show (RecordMatchExpr fields) ++ "' with type '" ++
                         show record ++ "'."
            return ([], env, argOrd, subst)
          Nothing -> inferList f env argOrd subst fields
            where f (name, me) env argOrd subst = do
                    (me', env, argOrd', subst') <- inferMatchExpr Nothing me
                                                     env argOrd subst
                    let env' = Map.insert name (typeOf me') env
                    return ((name, me'), env', argOrd', subst')
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      (recordTy, subst'') <- makeRecord env' argOrd' subst' False recordTypes
      return ((TRecordMatchExpr fields', recordTy), env', argOrd', subst'')

    inferMatchExpr tm (TypedMatchExpr me ty) env argOrd subst = do
      (me', env', argOrd', subst') <- inferMatchExpr tm me env argOrd subst
      unify' ty (typeOf me') env' argOrd' subst' >>= \case
        Just (ty'', subst'') -> return (me', env', argOrd', subst'')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected type '" ++ show ty ++
                     "' with actual type '" ++ show (typeOf me') ++ "'."
          return (me', env, argOrd', subst)

    inferMatchExpr tm (VarMatch name) env argOrd subst =
      case tm of
        Just t ->
          return ((TVarMatch name, t), Map.insert name t env, argOrd, subst)
        Nothing -> do
          t <- mkTypeVar
          return ((TVarMatch name, t), Map.insert name t env, argOrd, subst)

    inferMatchExpr tm (IntMatchExpr n) env argOrd subst =
      return ((TIntMatchExpr n, IntType), env, argOrd, subst)

    inferMatchExpr tm (StringMatchExpr s) env argOrd subst =
      return ((TStringMatchExpr s, StringType), env, argOrd, subst)

    inferMatchExpr tm (BoolMatchExpr b) env argOrd subst =
      return ((TBoolMatchExpr b, BoolType), env, argOrd, subst)

    inferStatement :: Statement -> Env -> ArgOrd -> Substitution -> IO (TypedStatement, Env, ArgOrd, Substitution)
    inferStatement (IfStatement e s Nothing) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst
      (s', envBody, _, substBody) <- inferStatement s envExpr argOrd' substExpr
      subst' <- mergeSubstitution env argOrd substExpr substBody
      (env', subst'') <- mergeEnv envExpr (Map.intersection envBody envExpr) argOrd subst'
      return (TIfStatement e' s' Nothing, env', argOrd', subst'')

    inferStatement (IfStatement e sThen (Just sElse)) env argOrd subst = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst
      (sThen', envThen, _, substThen) <- inferStatement sThen env' argOrd' subst'
      (sElse', envElse, _, substElse) <- inferStatement sElse env' argOrd' subst'
      subst' <- mergeSubstitution env argOrd substThen substElse
      (env'', subst'') <- mergeEnv (Map.intersection envThen env') (Map.intersection envElse env') argOrd subst'
      return (TIfStatement e' sThen' (Just sElse'), env'', argOrd', subst'')

    inferStatement (WhileStatement e s) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst
      (s', envBody, _, substBody) <- inferStatement s envExpr argOrd' substExpr
      subst' <- mergeSubstitution env argOrd substExpr substBody
      (env', subst'') <- mergeEnv envExpr (Map.intersection envBody envExpr) argOrd subst'
      return (TWhileStatement e' s', env', argOrd', subst'')

    inferStatement (ForStatement me e s) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst
      t <- mkTypeVar
      (t', subst') <- do
        unify' (typeOf e') (Array t) envExpr argOrd' substExpr >>= \case
          Just (_, subst') -> return (t, subst')
          Nothing -> do
            putStrLn $ "Error: Cannot iterate over expression of type '" ++
                       show (typeOf e') ++ "'."
            return (Error, substExpr)
      (me', envMatchExpr, argOrd'', substMatchExpr) <- inferMatchExpr (Just t') me envExpr argOrd' subst'
      (s', envBody, _, substBody) <- inferStatement s envMatchExpr argOrd'' substMatchExpr
      subst'' <- mergeSubstitution env argOrd substMatchExpr substBody
      (env', subst''') <- mergeEnv envMatchExpr (Map.intersection envBody envMatchExpr) argOrd subst''
      return (TForStatement me' e' s', env', argOrd'', subst''')

    inferStatement (CompoundStatement ss) env argOrd subst = do
      (ss', env', argOrd', subst') <- inferList inferStatement env argOrd subst ss
      return (TCompoundStatement ss', env', argOrd', subst')

    inferStatement (AssignStatement (Left me) e) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst
      (me', envMatchExpr, argOrd'', substMatchExpr) <-
        inferMatchExpr (Just $ typeOf e') me envExpr argOrd' substExpr
      return (TAssignStatement (Left me') e', envMatchExpr, argOrd'', substMatchExpr)

    inferStatement (AssignStatement (Right lve) e) env argOrd subst = do
      (e', env', argOrd', substExpr) <- inferExpr e env argOrd subst
      (lve', env'', substLValueExpr) <- inferLValueExpr (Just $ typeOf e') lve
                                         env' argOrd' substExpr
      return (TAssignStatement (Right lve') e', env'', argOrd', substLValueExpr)

    -- TODO: Implement pattern matching type checking.
    inferStatement (MatchStatement e mes) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst
      t <- mkTypeVar
      (_, subst') <- unify (typeOf e') t envExpr argOrd' substExpr
      (mes', _, _, subst'') <- inferList (f t) envExpr argOrd' subst' mes
      return (TMatchStatement e' mes', env, argOrd, subst'')
      where f (TypeVar u) (me, s) env argOrd subst = do
              (me', env', argOrd', subst') <- inferMatchExpr Nothing me env argOrd subst
              (ty, subst') <- unify (TypeVar u) (typeOf me') env argOrd subst'
              let subst'' = Map.insert u ty subst'
              (s', _, _, subst''') <- inferStatement s env' argOrd' subst''
              return ((me', s'), env, argOrd, subst''')

    inferStatement (ReturnStatement e) env argOrd subst = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst
      return (TReturnStatement e', env', argOrd', subst')

    inferStatement BreakStatement env argOrd subst =
      return (TBreakStatement, env, argOrd, subst)

    inferStatement ContinueStatement env argOrd subst =
      return (TContinueStatement, env, argOrd, subst)

    inferStatement (DeclStatement decl) env argOrd subst = do
      (decl', env', argOrd', subst') <- inferDecl decl env argOrd subst
      return (TDeclStatement decl', env', argOrd', subst')

    inferBinopExpr mkeExpr mkType env argOrd subst e1 e2 = do
      (e1', env1, argOrd1, subst1) <- inferExpr e1 env argOrd subst
      (e2', env2, argOrd2, subst2) <- inferExpr e2 env1 argOrd1 subst1
      (t, subst') <- mkType e1' e2' env2 argOrd2 subst2
      return ((mkeExpr e1' e2', t), env2, argOrd2, subst')

    mkMathOpType e1 e2 env argOrd subst = do
      (expectedType, subst') <- makeIntersect env argOrd subst IntType RealType
      unify' (typeOf e1) expectedType env argOrd subst' >>= \case
        Just (t1, subst1) ->
          unify' (typeOf e2) expectedType env argOrd subst1 >>= \case
            Just (t2, subst2) -> do
              unify' t1 t2 env argOrd subst2 >>= \case
                Just (t, subst') -> return (t, subst')
                Nothing -> do
                  putStrLn $ "Cannot unify type '" ++ show t1 ++
                             "' with type '" ++ show t2 ++ "'."
                  return (Error, subst)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++
                         "' with type '" ++ show expectedType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show expectedType ++ "'."
          return (Error, subst)

    mkLogicalOpType e1 e2 env argOrd subst = do
      unify' (typeOf e1) BoolType env argOrd subst >>= \case
        Just (t1, subst1) -> do
          unify' (typeOf e2) BoolType env argOrd subst1 >>= \case
            Just (t2, subst2) ->
              unify' t1 t2 env argOrd subst2 >>= \case
                Just (_, subst') ->
                  return (BoolType, subst')
                Nothing -> do
                  putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                             "' with type '" ++ show (typeOf e2) ++ "'."
                  return (Error, subst)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++
                         "' with type '" ++ show BoolType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show BoolType ++ "'."
          return (Error, subst)

    mkEqOpType e1 e2 env argOrd subst =
      unify' (typeOf e1) (typeOf e2) env argOrd subst >>= \case
        Just (_, subst') ->
          return (BoolType, subst')
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show (typeOf e2) ++ "'."
          return (Error, subst)

    mkRelOpType e1 e2 env argOrd subst = do
      (expectedType, subst') <- makeIntersect env argOrd subst IntType RealType
      unify' (typeOf e1) expectedType env argOrd subst >>= \case
        Just (_, subst1) -> do
          unify' (typeOf e2) expectedType env argOrd subst1 >>= \case
            Just (_, subst2) -> do
              return (BoolType, subst2)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++
                         "' with type '" ++ show expectedType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Can not unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show expectedType ++ "'."
          return (Error, subst)

    inferExpr (IntExpr n) env argOrd subst =
      return ((TIntExpr n, IntType), env, argOrd, subst)

    inferExpr (RealExpr n) env argOrd subst =
      return ((TRealExpr n, RealType), env, argOrd, subst)

    inferExpr (BoolExpr b) env argOrd subst =
      return ((TBoolExpr b, BoolType), env, argOrd, subst)

    inferExpr (StringExpr s) env argOrd subst =
      return ((TStringExpr s, StringType), env, argOrd, subst)

    inferExpr (OrExpr e1 e2) env argOrd subst =
      inferBinopExpr TOrExpr mkLogicalOpType env argOrd subst e1 e2

    inferExpr (AndExpr e1 e2) env argOrd subst =
      inferBinopExpr TAndExpr mkLogicalOpType env argOrd subst  e1 e2

    inferExpr (EqExpr e1 e2) env argOrd subst =
      inferBinopExpr TEqExpr mkEqOpType env argOrd subst  e1 e2

    inferExpr (NeqExpr e1 e2) env argOrd subst =
      inferBinopExpr TNeqExpr mkEqOpType env argOrd subst  e1 e2

    inferExpr (LtExpr e1 e2) env argOrd subst =
      inferBinopExpr TLtExpr mkRelOpType env argOrd subst  e1 e2

    inferExpr (GtExpr e1 e2) env argOrd subst =
      inferBinopExpr TGtExpr mkRelOpType env argOrd subst  e1 e2

    inferExpr (LeExpr e1 e2) env argOrd subst =
      inferBinopExpr TLeExpr mkRelOpType env argOrd subst  e1 e2

    inferExpr (GeExpr e1 e2) env argOrd subst =
      inferBinopExpr TGeExpr mkRelOpType env argOrd subst  e1 e2

    inferExpr (AddExpr e1 e2) env argOrd subst =
      inferBinopExpr TAddExpr mkMathOpType env argOrd subst  e1 e2

    inferExpr (SubExpr e1 e2) env argOrd subst =
      inferBinopExpr TSubExpr mkMathOpType env argOrd subst  e1 e2

    inferExpr (MultExpr e1 e2) env argOrd subst =
      inferBinopExpr TMultExpr mkMathOpType env argOrd subst  e1 e2

    inferExpr (DivExpr e1 e2) env argOrd subst =
      inferBinopExpr TDivExpr mkMathOpType env argOrd subst  e1 e2

    inferExpr (UnaryMinusExpr e) env argOrd subst = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst
      unify' (typeOf e') (intersect IntType RealType) env' argOrd' subst' >>= \case
        Just (t, subst'') -> return ((TUnaryMinusExpr e', t), env', argOrd', subst'')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Int' or 'Real' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TUnaryMinusExpr e', Error), env, argOrd', subst)

    inferExpr (BangExpr e) env argOrd subst = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst
      unify' (typeOf e') BoolType env' argOrd' subst' >>= \case
        Just (t, subst'') -> return ((TBangExpr e', BoolType), env', argOrd', subst'')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Bool' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TBangExpr e', BoolType), env', argOrd', subst')

    inferExpr (CallExpr f arg) env argOrd subst = do
      (f', env', argOrd', subst') <- inferExpr f env argOrd subst
      (arg', env'', argOrd'', subst'') <- inferExpr arg env' argOrd' subst'
      tCod <- mkTypeVar
      subtype (typeOf f') (Arrow (typeOf arg') tCod) env'' argOrd'' subst'' >>= \case
        (True, subst''') -> do
          return ((TCallExpr f' arg', tCod), env'', argOrd'', subst''')
        (False, _) -> do
          putStrLn $ "Couldn't match expected type '" ++ show (Arrow (typeOf arg') tCod) ++
                     "' with actual type '" ++ show (typeOf f') ++ "'."
          return ((TCallExpr f' arg', Error), env, argOrd'', subst)

    inferExpr (TypeConstrainedExpr e ty) env argOrd subst = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst
      (b, subst'') <- subtype (typeOf e') ty env' argOrd' subst'
      case b of
        True -> return (e', env', argOrd', subst'')
        False -> do
          putStrLn $ "Couldn't match expected type '" ++ show ty ++
                     "' with actual type '" ++ show (typeOf e') ++ "'."
          return (e', env', argOrd', subst')

    inferExpr (ListExpr es) env argOrd subst = do
      (es', env', argOrd', subst') <- inferList inferExpr env argOrd subst es
      (ty, subst'') <- unifyTypes (List.map snd es') env argOrd subst'
      return ((TListExpr es', Array ty), env', argOrd', subst'')

    inferExpr (TupleExpr es) env argOrd subst = do
      (es', env', argOrd', subst') <- inferList inferExpr env argOrd subst es
      return ((TTupleExpr es', Tuple (List.map snd es')), env', argOrd', subst')

    inferExpr (RecordExpr fields) env argOrd subst = do
      let f (name, e) env argOrd subst = do
            (e', env', argOrd', subst') <- inferExpr e env argOrd subst
            return ((name, e'), env', argOrd', subst')
      (fields', env', argOrd', subst') <- inferList f env argOrd subst fields
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      (recordTy, subst'') <- makeRecord env' argOrd' subst' False recordTypes
      return ((TRecordExpr fields', recordTy), env', argOrd', subst'')

    inferExpr (LValue lve) env argOrd subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst
      return ((TLValue lve', typeOf lve'), env', argOrd, subst')

    inferExpr (LambdaExpr mes s) env argOrd subst = do
      (mes', env', argOrd', subst') <- inferList (inferMatchExpr Nothing) env argOrd subst mes
      (s', env'', argOrd'', subst'') <- inferStatement s env' argOrd' subst'
      (ty, subst''') <- mergeReturns s' env'' argOrd'' subst''
      return ((TLambdaExpr mes' s', makeArrow (List.map snd mes') ty), env'', argOrd', subst''')

    mergeReturns :: TypedStatement -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
    mergeReturns s env argOrd subst =
      let types = returns s
      in unifyTypes types env argOrd subst
      where
        returns :: TypedStatement -> [Type]
        returns (TIfStatement _ sThen (Just sElse)) =
          returns sThen ++ returns sElse
        returns (TIfStatement _ sThen Nothing) =
          returns sThen
        returns (TWhileStatement _ s) =
          returns s
        returns (TForStatement _ _ s) =
          returns s
        returns (TCompoundStatement ss) =
          List.concatMap returns ss
        returns (TMatchStatement _ actions) =
          List.concatMap (returns . snd) actions
        returns (TReturnStatement te) = [typeOf te]
        returns _ = []

    inferLValueExpr tm (VarExpr name) env argOrd subst =
      case tm of
        Just t -> -- Writing to variable
          return ((TVarExpr name, t), Map.insert name t env, subst)
        Nothing -> -- Reading from variable
          case Map.lookup name env of
            Just ty ->
              return ((TVarExpr name, ty), env, subst)
            Nothing -> do
              putStrLn $ "Not in scope: " ++ name
              return ((TVarExpr name, Error), env, subst)

    inferLValueExpr tm (FieldAccessExpr lve field) env argOrd subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst
      case tm of
        Just t -> do -- Writing to variable
          (_, subst'') <- unify (typeOf lve') (Record False [(field, t)]) env argOrd subst'
          return ((TFieldAccessExpr lve' field, t), env', subst'')
        Nothing -> do -- Reading from variable
          u <- mkTypeVar
          (b, subst'') <- subtype (Record True [(field, u)]) (typeOf lve') env' argOrd subst'
          case b of
            True ->
              let subst''' = extendRecord field u (typeOf lve') subst''
              in return ((TFieldAccessExpr lve' field, u), env', subst''')
            False -> do
              putStrLn $ "'" ++ field ++ "' is not a field of type '" ++ show (typeOf lve') ++ "'"
              return ((TFieldAccessExpr lve' field, Error), env, subst)

    inferLValueExpr _ (ArrayAccessExpr lve e) env argOrd subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst
      (e', env'', argOrd', subst'') <- inferExpr e env' argOrd subst'
      arrayTy <- mkTypeVar
      unify' (typeOf lve') (Array arrayTy) env'' argOrd' subst'' >>= \case
        Just (_, subst''') -> do
          unify' (typeOf e') IntType env'' argOrd' subst''' >>= \case
            Just (_, subst'''') ->
              return ((TArrayAccessExpr lve' e', arrayTy), env'', subst'''')
            Nothing -> do
              putStrLn $ "Couldn't match expected type '" ++ (show IntType) ++
                         "' with actual type '" ++ show (typeOf e') ++ "'."
              return ((TArrayAccessExpr lve' e', Error), env'', subst)
        Nothing -> do
          putStrLn $ "Couldn't match expected array type with with actual type '" ++
                     show (typeOf lve') ++ "'."
          return ((TArrayAccessExpr lve' e', Error), env'', subst)

    replaceType :: Substitution -> Type -> Type
    replaceType subst ty =
      let replace :: Set Unique -> Type -> State (Set Unique) Type
          replace trace IntType = return IntType
          replace trace BoolType = return BoolType
          replace trace StringType = return StringType
          replace trace RealType = return RealType
          replace trace (Name s types) =
            mapM (replace trace) types >>= return . Name s 
          replace trace (Array ty) = replace trace ty >>= return . Array
          replace trace (Tuple [ty]) = replace trace ty
          replace trace (Tuple types) =
            mapM (replace trace) types >>= return . Tuple
          replace trace (Record b fields) =
            mapM field fields >>= return . Record b
            where field (s, ty) = replace trace ty >>= \ty -> return (s, ty)
          replace trace (Arrow tDom tCod) = do
            tDom' <- replace trace tDom
            tCod' <- replace trace tCod
            return $ Arrow tDom' tCod'
          replace trace (Union t1 t2) = do
            t1' <- replace trace t1
            t2' <- replace trace t2
            return $ union t1' t2'
          replace trace (Intersect t1 t2) = do
            t1' <- replace trace t1
            t2' <- replace trace t2
            return $ intersect t1 t2
          replace trace (Forall u ty) = do
            free <- get
            put (Set.insert u free)
            ty' <- replace trace ty
            return $ Forall u ty'
          replace trace (TypeVar u)
            | Set.member u trace = return $ TypeVar u
            | otherwise = do
              gets (Set.member (nearestUnique u subst)) >>=
                \case
                  True -> return $ TypeVar (nearestUnique u subst)
                  False -> case follow subst (TypeVar u) of
                             TypeVar u'
                               | u == u' -> return $ TypeVar u
                               | otherwise -> replace (Set.insert u trace)
                                                      (TypeVar u')
                             t -> replace (Set.insert u trace) t
          replace trace Error = return Error
      in evalState (replace Set.empty ty) Set.empty

    replaceDecl subst td =
      case td of
        TTypeDecl s targs t ->
          TTypeDecl s targs (replaceType subst t)
        TFunDecl name targs args retTy s ->
          TFunDecl name targs (List.map (replaceMatchExpr subst) args)
                              (replaceType subst retTy) (replaceStatement subst s)

    replaceMatchExpr subst (tme, ty) =
      let replace (TTupleMatchExpr tmes, ty) =
            (TTupleMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
          replace (TListMatchExpr tmes, ty) =
            (TListMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
          replace (TSetMatchExpr tmes, ty) =
            (TSetMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
          replace (TRecordMatchExpr fields, ty) =
            (TRecordMatchExpr (List.map f fields), ty')
            where f (s, tme) = (s, replaceMatchExpr subst tme)
          replace (tme, ty) = (tme, ty')
      in replace (tme, ty)
      where ty' = replaceType subst ty

    replaceStatement subst ts =
      let replace (TIfStatement te ts tsm) =
            TIfStatement (replaceExpr subst te) (replace ts)
                         (liftM replace tsm)
          replace (TWhileStatement te ts) =
            TWhileStatement (replaceExpr subst te) (replace ts)
          replace (TForStatement tme te ts) =
            TForStatement (replaceMatchExpr subst tme)
                          (replaceExpr subst te) (replace ts)
          replace (TCompoundStatement tss) =
            TCompoundStatement (List.map replace tss)
          replace (TAssignStatement tme_tlve te) =
            TAssignStatement (either (Left . replaceMatchExpr subst)
                                     (Right . replaceLValueExpr subst) tme_tlve)
                             (replaceExpr subst te)
          replace (TMatchStatement te actions) =
            let f (tme, ts) = (replaceMatchExpr subst tme, replace ts)
            in TMatchStatement (replaceExpr subst te) (List.map f actions)
          replace (TReturnStatement tem) =
            TReturnStatement (replaceExpr subst tem)
          replace TBreakStatement = TBreakStatement
          replace TContinueStatement = TContinueStatement
          replace (TDeclStatement td) = TDeclStatement (replaceDecl subst td)
      in replace ts

    replaceExpr subst (te, ty) =
      let replace (TIntExpr n, ty) = (TIntExpr n, ty')
          replace (TRealExpr d, ty) = (TRealExpr d, ty')
          replace (TBoolExpr b, ty) = (TBoolExpr b, ty')
          replace (TStringExpr s, ty) = (TStringExpr s, ty')
          replace (TOrExpr te1 te2, ty) =
            (TOrExpr (replace te1) (replace te2), ty')
          replace (TAndExpr te1 te2, ty) =
            (TAndExpr (replace te1) (replace te2), ty')
          replace (TEqExpr te1 te2, ty) =
            (TEqExpr (replace te1) (replace te2), ty')
          replace (TNeqExpr te1 te2, ty) =
            (TNeqExpr (replace te1) (replace te2), ty')
          replace (TLtExpr te1 te2, ty) =
            (TLtExpr (replace te1) (replace te2), ty')
          replace (TGtExpr te1 te2, ty) =
            (TGtExpr (replace te1) (replace te2), ty')
          replace (TLeExpr te1 te2, ty) =
            (TLeExpr (replace te1) (replace te2), ty')
          replace (TGeExpr te1 te2, ty) =
            (TGeExpr (replace te1) (replace te2), ty')
          replace (TAddExpr te1 te2, ty) =
            (TAddExpr (replace te1) (replace te2), ty')
          replace (TSubExpr te1 te2, ty) =
            (TSubExpr (replace te1) (replace te2), ty')
          replace (TMultExpr te1 te2, ty) =
            (TMultExpr (replace te1) (replace te2), ty')
          replace (TDivExpr te1 te2, ty) =
            (TDivExpr (replace te1) (replace te2), ty')
          replace (TUnaryMinusExpr te, ty) =
            (TUnaryMinusExpr (replace te), ty')
          replace (TBangExpr te, ty) =
            (TBangExpr (replace te), ty')
          replace (TCallExpr teFun teArg, ty) =
            (TCallExpr (replace teFun) (replace teArg), ty')
          replace (TListExpr tes, ty) =
            (TListExpr (List.map replace tes), ty')
          replace (TTupleExpr tes, ty) =
            (TTupleExpr (List.map replace tes), ty')
          replace (TSetExpr tes, ty) =
            (TSetExpr (List.map replace tes), ty')
          replace (TRecordExpr fields, ty) =
            (TRecordExpr (List.map f fields), ty')
            where f (s, te) = (s, replace te)
                  ty' = replaceType subst ty
          replace (TLValue tlve, ty) =
            (TLValue (replaceLValueExpr subst tlve), ty')
            
          replace (TLambdaExpr tmes ts, ty) =
            (TLambdaExpr (List.map (replaceMatchExpr subst) tmes)
                        (replaceStatement subst ts), ty')
      in replace (te, ty)
      where ty' = replaceType subst ty

    replaceLValueExpr subst (tlve, ty) =
      let replace (TVarExpr s, ty) = (TVarExpr s, ty')
          replace (TFieldAccessExpr tlve s, ty) =
            (TFieldAccessExpr (replace tlve) s, ty')
          replace (TArrayAccessExpr tlve te, ty) =
            (TArrayAccessExpr (replace tlve) (replaceExpr subst te), ty')
      in replace (tlve, ty)
      where ty' = replaceType subst ty

nearestUnique :: Unique -> Substitution -> Unique
nearestUnique u subst =
  case Map.lookup u subst of
    Just (TypeVar u')
      | u == u' -> u
      | otherwise -> nearestUnique u' subst
    Just _ -> u
    Nothing -> u