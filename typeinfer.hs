{-# LANGUAGE LambdaCase, TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module TypeInfer where
import Data.Foldable hiding (mapM_)
import Control.Arrow
import Control.Monad
import Control.Monad.State.Lazy
import qualified Data.List as List
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Hashable
import Data.Bool
import Hash
import Unique

import Types
import TTypes
import TypedAst
import Unification
import Subtype
import TypeUtils
import Replace

formatType :: TType -> Infer String
formatType ty = do
  env <- environment
  subst <- substitution
  return . show $ replaceType subst env ty

errorCannotMatchExpectedWithActual :: TType -> TType -> Infer String
errorCannotMatchExpectedWithActual expected actual = do
  expected' <- formatType expected
  actual' <- formatType actual
  return $ "Error: Cannot match expected type '" ++ expected' ++
           "' with actual type '" ++ actual' ++ "'."

errorCannotUnifyMatchExprWithType :: MatchExpr -> TType -> Infer String
errorCannotUnifyMatchExprWithType expr ty = do
  ty' <- formatType ty
  return $ "Error: Cannot unify expression '" ++
           show expr ++ "' with type '" ++
           show ty' ++ "'."

errorCannotUnifyTypeWithType :: TType -> TType -> Infer String
errorCannotUnifyTypeWithType ty1 ty2 = do
  [ty1', ty2'] <- mapM formatType [ty1, ty2]
  return $ "Error: Cannot unify type '" ++
           show ty1' ++ "' with type '" ++
           show ty2' ++ "'."

extendRecord :: String -> TType -> TType -> Infer ()
extendRecord name ty (TTypeVar u) =
  follow (TTypeVar u) >>= \case
    TRecord b fields
      | isNothing (List.lookup name fields) ->
        modifySubst $ Map.insert u (TRecord b ((name, ty):fields))
      | otherwise -> modifySubst $ Map.insert u (TRecord b (List.map f fields))
        where f (name', ty')
                | name' == name = (name', ty)
                | otherwise     = (name', ty')
    TTypeVar u' -> modifySubst $ Map.insert u' (TRecord True [(name, ty)])

mergeSubstitution :: Substitution -> Substitution -> Infer ()
mergeSubstitution subst1 subst2 = do
  modifySubst (const subst1)
  mapM_ f (Map.toList subst2)
  where f (u, ty) = do subst <- substitution
                       case Map.lookup u subst of
                         Nothing -> modifySubst (Map.insert u ty)
                         Just ty' -> void (unify ty ty')

mergeSubstWith :: Substitution -> Infer ()
mergeSubstWith subst = substitution >>= flip mergeSubstitution subst

mergeEnv :: Env -> Env -> Infer ()
mergeEnv env1 env2 = do
  modifyEnv (const env1)
  mapM_ f (Map.toList env2)
  where f (name, (uniq, ty)) =
          do env <- environment
             case Map.lookup name env of
               Nothing -> modifyEnv (Map.insert name (uniq, ty))
               Just (uniq, ty') -> do
                argord <- argumentOrder
                let m = argord ! Identifier (name, uniq)
                case ty of
                  TName ident [] ->
                    let isTypeArg = ident `List.elem` List.map snd (Map.toList m)
                    in unless isTypeArg $
                        unify ty ty' >>= \ty -> modifyEnv (Map.insert name (uniq, ty))
                  _ -> unify ty ty' >>= \ty -> modifyEnv (Map.insert name (uniq, ty))

mergeEnvWith :: Env -> Infer ()
mergeEnvWith env = environment >>= flip mergeEnv env

isTypeDecl :: Decl -> Bool
isTypeDecl TypeDecl{} = True
isTypeDecl _ = False

isFunDecl :: Decl -> Bool
isFunDecl FunDecl{} = True
isFunDecl _ = False

infer :: [Decl] -> IO ([TypedDecl], Env, Map Identifier FunctionInfo)
infer decls = do
  let typedecls = List.filter isTypeDecl decls
  let fundecls = List.filter isFunDecl decls

  (typedecls', st) <- runStateT (mapM inferDecl typedecls) emptySt

  let typedecls'' = List.map (replaceDecl (subst st) (env st)) typedecls'
  let env'' = Map.mapWithKey (\ident (uniq, ty) ->
                case List.find ((== ident) . stringOf . fst) typedecls'' of
                  Just (ident', TTypeDecl ty') -> (idOf ident', ty')
                  Nothing -> (uniq, ty)
              ) $ Map.map (second (replaceType (subst st) (env st))) (env st)

  (fundecls', st') <- runStateT (mapM inferDecl fundecls) (st {env = env''})
  let fundecls'' = List.map (replaceDecl (subst st') (env st')) fundecls'
  let env''' = Map.map (second (replaceType (subst st') (env st'))) (env st')

  return (typedecls'' ++ fundecls'', env''', allFuncs st')

insertArgOrd :: Identifier -> [Identifier] -> Infer ()
insertArgOrd name targs =
  modifyArgOrd $ Map.insert name (Map.fromList (List.zip [0..] targs))

addFuncs :: Map Identifier FunctionInfo -> Infer ()
addFuncs fs = do
  funcs <- gets allFuncs
  modify $ \st -> st {allFuncs = fs `Map.union` funcs}

transTy :: Type -> Infer TType
transTy IntType = return TIntType
transTy BoolType = return TBoolType
transTy StringType = return TStringType
transTy RealType = return TRealType
transTy (Name name tys) =
  Map.lookup name <$> environment >>= \case
    Just (uniq, ty') -> do
      tys' <- mapM transTy tys
      argord <- argumentOrder
      arglist <- case Map.lookup (Identifier (name, uniq)) argord of
                   Just a -> return $ Map.toList a
                   Nothing -> return []
      let args = List.zip (List.map snd arglist) tys'
      return $ foldr (uncurry instansiate) ty' args
    Nothing -> error $ "Error: " ++ name ++ " is not defined."
transTy (Array ty) = TArray <$> transTy ty
transTy (Tuple tys) = TTuple <$> mapM transTy tys
transTy (Record b fields) = TRecord b <$> mapM (\(name, ty) ->
                                            fmap (name,) (transTy ty)) fields
transTy (Arrow ty1 ty2) = liftM2 TArrow (transTy ty1) (transTy ty2)
transTy (Union ty1 ty2) = liftM2 TUnion (transTy ty1) (transTy ty2)

transTy' :: Map String UniqueInt -> Type -> Infer TType
transTy' _ IntType = return TIntType
transTy' _ BoolType = return TBoolType
transTy' _ StringType = return TStringType
transTy' _ RealType = return TRealType
transTy' idents (Name name tys) = do
  tys' <- mapM (transTy' idents) tys
  case Map.lookup name idents of
    Just uniq ->
      return $ TName (Identifier (name, uniq)) tys'
    Nothing -> do
      env <- environment
      case Map.lookup name env of
        Just (uniq, _) ->
          return $ TName (Identifier (name, uniq)) tys'
        Nothing -> return $ TRef name tys'
transTy' idents (Array ty) = TArray <$> transTy' idents ty
transTy' idents (Tuple tys) = TTuple <$> mapM (transTy' idents) tys
transTy' idents (Record b fields) =
    TRecord b <$> mapM (\(name, ty) -> fmap (name,) (transTy' idents ty)) fields
transTy' idents (Arrow ty1 ty2) =
    liftM2 TArrow (transTy' idents ty1) (transTy' idents ty2)
transTy' idents (Union ty1 ty2) =
    liftM2 TUnion (transTy' idents ty1) (transTy' idents ty2)

inferDecl :: Decl -> Infer TypedDecl
inferDecl (TypeDecl name targs ty) = do
  targs' <- lift $ mapM fromString targs
  ty' <- transTy' (Map.fromList $ List.map unIdentifier targs') ty
  name' <- lift $ fromString name
  modifyEnv (Map.insert name (idOf name', ty'))
  insertArgOrd name' targs'
  return (name', TTypeDecl (List.foldr TForall ty' targs'))

inferDecl (FunDecl name tyArgs args retTy statement) = do
  tyArgs' <- lift $ mapM fromString tyArgs
  mapM_ (\ident -> do
          t <- lift mkTypeVar
          modifyEnv (Map.insert (stringOf ident) (idOf ident, t))) tyArgs'
  args' <- mapM (inferMatchExpr Nothing) args
  retTy' <- maybe (lift mkTypeVar) transTy retTy
  let types = List.map snd args'
  funTy <- foldrM makeForall (makeArrow types retTy') types
  funId <- lift $ fromString name
  modifyEnv (Map.insert name (idOf funId, funTy))
  (statement', st) <- local $ inferStatement statement
  modifySubst (const $ subst st)
  addFuncs (allFuncs st)
  infRetTy <- mergeReturns statement'

  subtype retTy' infRetTy >>= \case
    Just retTy -> do
      funTy' <- foldrM makeForall (makeArrow types retTy) types
      modifyEnv (Map.insert name (idOf funId, funTy'))
      addFunc funId tyArgs' args' funTy' statement'
      return (funId, TFunDecl tyArgs' args' retTy statement')
    Nothing -> do
      errorCannotMatchExpectedWithActual retTy' infRetTy >>= liftIO . putStrLn
      modifyEnv (Map.insert name (idOf funId, TError))
      addFunc funId tyArgs' args' TError statement'
      return (funId, TFunDecl tyArgs' args' retTy' statement')

commMaybeInfer :: Maybe (Infer a) -> Infer (Maybe a)
commMaybeInfer (Just i) = fmap Just i
commMaybeInfer Nothing = return Nothing

inferMatchExpr :: Maybe TType -> MatchExpr -> Infer TypedMatchExpr
inferMatchExpr tm (TupleMatchExpr mes) = do
  mes' <- do
    types <- lift $ replicateM (List.length mes) mkTypeVar
    commMaybeInfer (fmap (unify' (TTuple types)) tm) >>= \case
      Just (Just (TTuple ts)) ->
        mapM (\(me, t) -> inferMatchExpr (Just t) me) (List.zip mes ts)
      Nothing -> mapM (inferMatchExpr Nothing) mes
      _ -> do
        errorCannotUnifyMatchExprWithType (TupleMatchExpr mes)
          (TTuple types) >>= liftIO . putStrLn
        return []
  return (TTupleMatchExpr mes', TTuple (List.map typeOf mes'))

inferMatchExpr tm (ListMatchExpr mes) = do
  t <- lift mkTypeVar
  mes' <-
    commMaybeInfer (fmap (unify' (TArray t)) tm) >>= \case
      Just (Just (TArray t)) -> mapM (inferMatchExpr (Just t)) mes
      Nothing -> mapM (inferMatchExpr Nothing) mes
      _ -> do
        errorCannotUnifyMatchExprWithType (ListMatchExpr mes)
          (TArray t) >>= liftIO . putStrLn
        return []
  ty <- unifyTypes (List.map typeOf mes')
  return (TListMatchExpr mes', TArray ty)

inferMatchExpr tm (RecordMatchExpr fields) = do
  fields' <- do
    fields' <- fmap (List.zip (normaliseFields fields))
                    (replicateM (List.length fields) (lift mkTypeVar))
    let record = TRecord False (List.map (\((s, _), ty) -> (s, ty)) fields')
    commMaybeInfer (fmap (unify' record) tm) >>= \case
      Just (Just (TRecord _ fields')) ->
        mapM (\(entry, ty) -> f (Just ty) entry)
             (List.zip (normaliseFields fields) typesm)
        where typesm = List.map typeOf (normaliseFields fields')
              f tm (name, me) = do
                me' <- inferMatchExpr tm me
                return (name, me')
      Nothing -> mapM f fields
        where f (name, me) = do
                me' <- inferMatchExpr Nothing me
                lift (fromString name) >>= \field -> modifyEnv (Map.insert name (idOf field, typeOf me'))
                return (name, me')
      _ -> do
        errorCannotUnifyMatchExprWithType (RecordMatchExpr fields)
          record >>= liftIO . putStrLn
        return []
  recordTy <- makeRecord False (List.map (\(name, (_, t)) -> (name, t)) fields')
  return (TRecordMatchExpr fields', recordTy)

inferMatchExpr tm (TypedMatchExpr me ty) = do
  me' <- inferMatchExpr tm me
  ty' <- transTy ty
  subtype ty' (typeOf me') >>= \case
    Just _ -> return me'
    Nothing -> do
      errorCannotMatchExpectedWithActual ty' (typeOf me') >>= liftIO . putStrLn
      return me'

inferMatchExpr tm (VarMatch name) =
  do env <- environment
     var <- case Map.lookup name env of
              Just (u, _) -> return (identifier name u)
              Nothing -> lift $ fromString name
     case tm of
       Just t -> do
         modifyEnv (Map.insert name (idOf var, t))
         return (TVarMatch var, t)
       Nothing -> do
         t <- lift mkTypeVar
         modifyEnv (Map.insert name (idOf var, t))
         return (TVarMatch var, t)

inferMatchExpr _ (IntMatchExpr n) = return (TIntMatchExpr n, TIntType)
inferMatchExpr _ (StringMatchExpr s) = return (TStringMatchExpr s, TStringType)
inferMatchExpr _ (BoolMatchExpr b) = return (TBoolMatchExpr b, TBoolType)

inferStatement :: Statement -> Infer TypedStatement
inferStatement (IfStatement e s Nothing) = do
  e' <- inferExpr e
  (s', st) <- local $ inferStatement s
  mergeSubstWith (subst st)
  mergeEnvWith (env st)
  addFuncs (allFuncs st)
  return $ TIfStatement e' s' Nothing

inferStatement (IfStatement e sThen (Just sElse)) = do
  e' <- inferExpr e
  (sThen', stThen) <- local $ inferStatement sThen
  (sElse', stElse) <- local $ inferStatement sElse
  mergeSubstitution (subst stThen) (subst stElse)
  mergeEnv (env stThen) (env stElse)
  addFuncs (allFuncs stThen `Map.union` allFuncs stElse)
  return $ TIfStatement e' sThen' (Just sElse')

inferStatement (WhileStatement e s) = do
  e' <- inferExpr e
  (s', st) <- local $ inferStatement s
  mergeSubstWith (subst st)
  mergeEnvWith (env st)
  addFuncs (allFuncs st)
  return $ TWhileStatement e' s'

inferStatement (ForStatement me e s) = do
  e' <- inferExpr e
  t <- lift mkTypeVar
  t' <- unify' (typeOf e') (TArray t) >>= \case
          Just _ -> return t
          Nothing -> do
            lift (putStrLn $ "Error: Cannot iterate over expression of type '" ++
                                show (typeOf e') ++ "'.")
            return TError
  me' <- inferMatchExpr (Just t') me
  (s', st) <- local $ inferStatement s
  mergeSubstWith (subst st)
  mergeEnvWith (env st)
  addFuncs (allFuncs st)
  return $ TForStatement me' e' s'

inferStatement (CompoundStatement ss) = do
  ss' <- mapM inferStatement ss
  return $ TCompoundStatement ss'

inferStatement (AssignStatement (Left me) e) = do
  e' <- inferExpr e
  me' <- inferMatchExpr (Just $ typeOf e') me
  return $ TAssignStatement (Left me') e'

inferStatement (AssignStatement (Right lve) e) = do
  e' <- inferExpr e
  lve' <- inferLValueExpr (Just $ typeOf e') lve
  return $ TAssignStatement (Right lve') e'

inferStatement (MatchStatement e mes) = do
  e' <- inferExpr e
  strategy <- fmap (bool unifyStrict unifyPermissive) (free (typeOf e'))
  mes' <- mapM (strategy (typeOf e')) mes
  return $ TMatchStatement e' mes'
  where unifyPermissive (TTypeVar u) (me, s) = do
          me' <- inferMatchExpr Nothing me
          ty <- unify (TTypeVar u) (typeOf me')
          modifySubst (Map.insert u ty)
          s' <- inferStatement s
          return (me', s')

        unifyStrict ty (me, s) = do
          me' <- inferMatchExpr Nothing me
          subtype ty (typeOf me') >>= \case
            Just _ -> do
              s' <- inferStatement s
              return (me', s')
            Nothing -> do
              errorCannotUnifyTypeWithType ty (typeOf me') >>= liftIO . putStrLn
              s' <- inferStatement s
              return (me', s')

inferStatement (ReturnStatement e) = do
  e' <- inferExpr e
  return $ TReturnStatement e'

inferStatement BreakStatement = return TBreakStatement
inferStatement ContinueStatement = return TContinueStatement

inferStatement (DeclStatement decl) = do
  decl' <- inferDecl decl
  return $ TDeclStatement decl'

inferBinopExpr :: (TypedExpr -> TypedExpr -> TExpr)
                    -> ((TExpr, TType) -> (TExpr, TType) -> StateT InferSt IO TType)
                    -> Expr -> Expr -> Infer TypedExpr
inferBinopExpr mkeExpr mkType e1 e2 = do
  e1' <- inferExpr e1
  e2' <- inferExpr e2
  t <- mkType e1' e2'
  return (mkeExpr e1' e2', t)

mkMathOpType :: TypedExpr -> TypedExpr -> Infer TType
mkMathOpType e1 e2 = do
  expType <- makeIntersect TIntType TRealType
  subtype (typeOf e1) expType >>= \case
    Just t1 ->
      subtype (typeOf e2) expType >>= \case
        Just t2 ->
          unify' t1 t2 >>= \case
            Just t -> return t
            Nothing -> do
              liftIO $ print t1
              liftIO $ print t2
              liftIO $ print "1"
              errorCannotUnifyTypeWithType t1 t2 >>= liftIO . putStrLn
              return TError
        Nothing -> do
          liftIO $ print "2"
          errorCannotUnifyTypeWithType (typeOf e2) expType >>= liftIO . putStrLn
          return TError
    Nothing -> do
      liftIO $ print "3"
      errorCannotUnifyTypeWithType (typeOf e1) expType >>= liftIO . putStrLn
      return TError

mkLogicalOpType :: TypedExpr -> TypedExpr -> Infer TType
mkLogicalOpType e1 e2 =
  unify' (typeOf e1) TBoolType >>= \case
    Just t1 ->
      unify' (typeOf e2) TBoolType >>= \case
        Just t2 ->
          unify' t1 t2 >>= \case
            Just _ -> return TBoolType
            Nothing -> do
              errorCannotUnifyTypeWithType (typeOf e1) (typeOf e2) >>=
                liftIO . putStrLn
              return TError
        Nothing -> do
          errorCannotUnifyTypeWithType (typeOf e2) TBoolType >>=
            liftIO . putStrLn
          return TError
    Nothing -> do
      errorCannotUnifyTypeWithType (typeOf e1) TBoolType >>=
        liftIO . putStrLn
      return TError

mkEqOpType :: TypedExpr -> TypedExpr -> Infer TType
mkEqOpType e1 e2 =
  unify' (typeOf e1) (typeOf e2) >>= \case
    Just _ -> return TBoolType
    Nothing -> do
      errorCannotUnifyTypeWithType (typeOf e1) (typeOf e2) >>=
        liftIO . putStrLn
      return TError

mkRelOpType :: TypedExpr -> TypedExpr -> Infer TType
mkRelOpType e1 e2 = do
  expectedType <- makeIntersect TIntType TRealType
  unify' (typeOf e1) expectedType >>= \case
    Just _ ->
      unify' (typeOf e2) expectedType >>= \case
        Just _ -> return TBoolType
        Nothing -> do
          errorCannotUnifyTypeWithType (typeOf e2) expectedType >>=
            liftIO . putStrLn
          return TError
    Nothing -> do
      errorCannotUnifyTypeWithType (typeOf e1) expectedType >>=
        liftIO . putStrLn
      return TError

inferExpr :: Expr -> Infer TypedExpr
inferExpr (IntExpr n) =
  return (TIntExpr n, TIntType)

inferExpr (RealExpr n) =
  return (TRealExpr n, TRealType)

inferExpr (BoolExpr b) =
  return (TBoolExpr b, TBoolType)

inferExpr (StringExpr s) =
  return (TStringExpr s, TStringType)

inferExpr (OrExpr e1 e2) =
  inferBinopExpr TOrExpr mkLogicalOpType e1 e2

inferExpr (AndExpr e1 e2) =
  inferBinopExpr TAndExpr mkLogicalOpType e1 e2

inferExpr (EqExpr e1 e2) =
  inferBinopExpr TEqExpr mkEqOpType e1 e2

inferExpr (NeqExpr e1 e2) =
  inferBinopExpr TNeqExpr mkEqOpType e1 e2

inferExpr (LtExpr e1 e2) =
  inferBinopExpr TLtExpr mkRelOpType e1 e2

inferExpr (GtExpr e1 e2) =
  inferBinopExpr TGtExpr mkRelOpType e1 e2

inferExpr (LeExpr e1 e2) =
  inferBinopExpr TLeExpr mkRelOpType e1 e2

inferExpr (GeExpr e1 e2) =
  inferBinopExpr TGeExpr mkRelOpType e1 e2

inferExpr (AddExpr e1 e2) =
  inferBinopExpr TAddExpr mkMathOpType e1 e2

inferExpr (SubExpr e1 e2) =
  inferBinopExpr TSubExpr mkMathOpType e1 e2

inferExpr (MultExpr e1 e2) =
  inferBinopExpr TMultExpr mkMathOpType e1 e2

inferExpr (DivExpr e1 e2) =
  inferBinopExpr TDivExpr mkMathOpType e1 e2

inferExpr (UnaryMinusExpr e) = do
  e' <- inferExpr e
  unify' (typeOf e') (tintersect TIntType TRealType) >>= \case
    Just t ->
      return (TUnaryMinusExpr e', t)
    Nothing -> do
      errorCannotMatchExpectedWithActual (TIntersect TIntType TRealType)
        (typeOf e') >>= liftIO . putStrLn
      return (TUnaryMinusExpr e', TError)

inferExpr (BangExpr e) = do
  e' <- inferExpr e
  unify' (typeOf e') TBoolType >>= \case
    Just _ -> return (TBangExpr e', TBoolType)
    Nothing -> do
      errorCannotMatchExpectedWithActual TBoolType
        (typeOf e') >>= liftIO . putStrLn
      return (TBangExpr e', TBoolType)

inferExpr (CallExpr f arg) = do
  f' <- inferExpr f
  arg' <- inferExpr arg
  tCod <- lift mkTypeVar
  subtype (typeOf f') (TArrow (typeOf arg') tCod) >>= \case
    Just _ -> return (TCallExpr f' arg', tCod)
    Nothing -> do
      errorCannotMatchExpectedWithActual (typeOf f')
        (TArrow (typeOf arg') tCod) >>= liftIO . putStrLn
      return (TCallExpr f' arg', TError)

inferExpr (TypeConstrainedExpr e ty) = do
  e' <- inferExpr e
  ty' <- transTy ty
  subtype (typeOf e') ty' >>= \case
    Just _ -> return e'
    Nothing -> do
      errorCannotMatchExpectedWithActual ty' (typeOf e') >>= liftIO . putStrLn
      return e'

inferExpr (ListExpr es) = do
  es' <- mapM inferExpr es
  ty <- unifyTypes (List.map snd es')
  return (TListExpr es', TArray ty)

inferExpr (TupleExpr es) = do
  es' <- mapM inferExpr es
  return (TTupleExpr es', TTuple (List.map snd es'))

inferExpr (RecordExpr fields) = do
  let f (name, e) = do
        e' <- inferExpr e
        return (name, e')
  fields' <- mapM f fields
  let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
  recordTy <- makeRecord False recordTypes
  return (TRecordExpr fields', recordTy)

inferExpr (LValue lve) = do
  lve' <- inferLValueExpr Nothing lve
  return (TLValue lve', typeOf lve')

inferExpr (LambdaExpr mes s) = do
  mes' <- mapM (inferMatchExpr Nothing) mes
  s' <- inferStatement s
  ty <- mergeReturns s'
  let funTy = makeArrow (List.map snd mes') ty
  name <- genFunId funTy s'
  addFunc name [] mes' funTy s'
  return (TLambdaExpr mes' s', funTy)

genFunId :: TType -> TypedStatement -> Infer Identifier
genFunId ty stmt =
  lift . fromString $ "t" ++ show (hash ty `combine` hash stmt)

mergeReturns :: TypedStatement -> Infer TType
mergeReturns s =
  let types = returns s
  in unifyTypes types
  where
    returns :: TypedStatement -> [TType]
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

inferLValueExpr :: Maybe TType -> LValueExpr -> Infer TypedLValueExpr
inferLValueExpr tm (VarExpr name) = do
  env <- environment
  case tm of
    Just t -> -- Writing to variable
      case Map.lookup name env of
        Just (id, _) -> do
          modifyEnv (Map.insert name (id, t))
          return (TVarExpr (identifier name id), t)
        Nothing -> do
          var <- lift $ fromString name
          modifyEnv (Map.insert name (idOf var, t))
          return (TVarExpr var, t)
    Nothing -> -- Reading from variable
      case Map.lookup name env of
        Just (u, ty) -> return (TVarExpr (identifier name u), ty)
        Nothing -> do
          lift $ putStrLn $ "Not in scope: " ++ name
          var <- lift $ fromString name
          return (TVarExpr var, TError)

inferLValueExpr tm (FieldAccessExpr lve field) = do
  lve' <- inferLValueExpr Nothing lve
  case tm of
    Just t -> do --Writing to variable
      extendRecord field t (typeOf lve')
      return (TFieldAccessExpr lve' field, t)
    Nothing -> do -- Reading from variable
      u <- lift mkTypeVar
      subtype (typeOf lve') (TRecord True [(field, u)]) >>= \case
        Just _ -> return (TFieldAccessExpr lve' field, u)
        Nothing -> do
          lift $ putStrLn $ "'" ++ field ++ "' is not a field of type '"
                            ++ show (typeOf lve') ++ "'"
          return (TFieldAccessExpr lve' field, TError)

inferLValueExpr _ (ArrayAccessExpr lve e) = do
  lve' <- inferLValueExpr Nothing lve
  e' <- inferExpr e
  arrayTy <- lift mkTypeVar
  unify' (typeOf lve') (TArray arrayTy) >>= \case
    Just _ ->
      unify' (typeOf e') TIntType >>= \case
        Just _ -> return (TArrayAccessExpr lve' e', arrayTy)
        Nothing -> do
          errorCannotMatchExpectedWithActual TIntType
            (typeOf e') >>= liftIO . putStrLn
          return (TArrayAccessExpr lve' e', TError)
    Nothing -> do
      errorCannotMatchExpectedWithActual (TArray arrayTy)
        (typeOf lve') >>= liftIO . putStrLn
      return (TArrayAccessExpr lve' e', TError)
