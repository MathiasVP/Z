module TypeInfer where
import qualified Data.List as List
import qualified Data.Map as Map
import Control.Monad
import TypedAst
import Unification

intType, realType, boolType, stringType :: Type
intType = Name "Int" []
realType = Name "Real" []
boolType = Name "Bool" []
stringType = Name "String" []
voidType = Name "Void" []
  
mkIntType :: Substitution -> IO (Type, Substitution)
mkIntType subst = do
  u <- mkTypeVar
  (_, subst') <- unify u intType subst
  return (u, subst')
  
mkRealType :: Substitution -> IO (Type, Substitution)
mkRealType subst = do
  u <- mkTypeVar
  (_, subst') <- unify u realType subst
  return (u, subst')
  
mkArrowType :: [Type] -> Type -> Type
mkArrowType types retTy = List.foldr Arrow retTy types

mkAllOfType :: Substitution -> [Type] -> IO (Type, Substitution)
mkAllOfType subst types = do
  u <- mkTypeVar
  (_, subst') <- unify u (AllOf types) subst
  return (u, subst')

normaliseFields fields =
  let cmp (name1, _) (name2, _) = compare name1 name2
  in List.sortBy cmp fields
  
equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2
  
exprOf = fst
typeOf = snd

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map.Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc) 
  where f' ma k b = ma >>= \a -> f a k b

mergeSubstitution :: Substitution -> Substitution -> IO Substitution
mergeSubstitution subst1 subst2 = foldlWithKeyM f subst1 subst2
  where f subst u ty =
          case Map.lookup u subst of
            Nothing -> return $ Map.insert u ty subst
            Just ty' -> do
              (_, subst') <- unify ty ty' subst
              return subst'

mergeEnv :: Env -> Env -> Substitution -> IO (Env, Substitution)
mergeEnv env1 env2 subst = foldlWithKeyM f (env1, subst) env2
  where f (env, subst) name ty =
          case Map.lookup name env of
            Nothing -> return $ (Map.insert name ty env, subst)
            Just ty' -> do
              (ty'', subst') <- unify ty ty' subst
              return (Map.insert name ty'' env, subst')

infer :: [Decl] -> IO ([TypedDecl], Env, Substitution)
infer decls = do
  (typeddecls, env, subst) <- inferList inferDecl (Map.fromList []) (Map.fromList []) decls
  -- TODO Run through the entire program and replace type variables with actual types
  return (typeddecls, env, subst)
  where
    inferList :: (a -> Env -> Substitution -> IO (b, Env, Substitution)) -> Env -> Substitution -> [a] -> IO ([b], Env, Substitution)
    inferList inferer env subst list = 
      do (list', env', subst') <- foldM f ([], env, subst) list
         return (List.reverse list', env', subst')
      where f (list', env, subst) elem = do
            (elem', env', subst') <- inferer elem env subst
            return (elem' : list', env', subst')

    inferDecl :: Decl -> Env -> Substitution -> IO (TypedDecl, Env, Substitution)
    inferDecl (TypeDecl name ty) env subst =
      return (TTypeDecl name ty, env, subst)

    inferDecl (FunDecl name tyArgs args Nothing statement) env subst = do
      (args', env', subst') <- inferList (inferMatchExpr Nothing) env subst args
      let (_, types) = List.unzip args'
      retTy <- mkTypeVar
      let env'' = Map.insert name (mkArrowType types retTy) env'
      (statement', env'', subst'') <- inferStatement statement env'' subst'
      (retTy', subst''') <- mergeReturns statement' subst''
      let globEnv = Map.insert name (mkArrowType types retTy') env
      return (TFunDecl name tyArgs args' retTy' statement', globEnv, subst''')

    inferDecl (FunDecl name tyArgs args (Just retTy) statement) env subst = do
      (args', _, subst') <- inferList (inferMatchExpr Nothing) env subst args
      let (_, types) = List.unzip args'
      let env' = Map.insert name (mkArrowType types retTy) env
      (statement', env'', subst'') <- inferStatement statement env' subst'
      (retTy', subst''') <- mergeReturns statement' subst''
      case unify' retTy retTy' subst'' of
        Just (retTy'', subst''') ->
          return (TFunDecl name tyArgs args' retTy'' statement', env', subst''')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected return type '" ++ show retTy ++ "' with actual type '" ++ show retTy' ++ "'."
          return (TFunDecl name tyArgs args' retTy statement', env', subst'')

    inferMatchExpr :: Maybe Type -> MatchExpr -> Env -> Substitution -> IO (TypedMatchExpr, Env, Substitution)
    inferMatchExpr tm (TupleMatchExpr mes) env subst = do
      (mes', env', subst') <-
        case tm of
          Just (Tuple ts) ->
            if List.length ts == List.length mes then
              let mesWithTypes =
                    case tm of
                      Just (Tuple ts) ->
                        List.map inferMatchExpr (List.map Just ts)
                      Nothing -> []
                  f (me, n) env subst = (mesWithTypes !! n) me env subst
              in inferList f env subst (List.zip mes [0..List.length mes - 1])
            else do putStrLn $ "Match error: Couldn't unify expression '" ++
                               show (TupleMatchExpr mes) ++ "' with type '" ++
                               show (Tuple ts) ++ "'."
                    return ([], env, subst)
          Nothing ->
            inferList (inferMatchExpr Nothing) env subst mes
      return ((TTupleMatchExpr mes', Tuple (List.map typeOf mes')), env', subst')

    inferMatchExpr tm (ListMatchExpr mes) env subst = do
      (mes', env', subst') <-
        case tm of
          Just (Array t) -> inferList (inferMatchExpr (Just t)) env subst mes
          Nothing -> inferList (inferMatchExpr Nothing) env subst mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') subst'
      return ((TListMatchExpr mes', Array ty), env', subst'')
      
    inferMatchExpr tm (SetMatchExpr mes) env subst = do
      (mes', env', subst') <-
        case tm of
          Just (Set t) -> inferList (inferMatchExpr (Just t)) env subst mes
          Nothing -> inferList (inferMatchExpr Nothing) env subst mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') subst'
      return ((TSetMatchExpr mes', Set ty), env', subst'')
      
    inferMatchExpr tm (RecordMatchExpr fields) env subst = do
      (fields', env', subst') <- case tm of
        Just (Record fields') ->
          if equalRecordFields fields fields' then
            let typesm = List.map (Just . typeOf) (normaliseFields fields')
                f tm (name, me) env subst = do
                  (me', env', subst') <- inferMatchExpr tm me env subst
                  return ((name, me'), env', subst')
                fs = List.map f typesm
                inferField (entry, n) = (fs !! n) entry
            in inferList inferField env subst (List.zip (normaliseFields fields) [0..List.length fields - 1])
          else
            return ([], env, subst)
        Nothing ->
          let f (name, me) env subst = do
                (me', env, subst') <- inferMatchExpr Nothing me env subst
                return ((name, me'), Map.insert name (typeOf me') env, subst')
          in inferList f env subst fields
      let mkStringTypePair (name, (_, t)) = (name, t)
      let recordTypes = List.map mkStringTypePair fields'
      return ((TRecordMatchExpr fields', Record recordTypes), env', subst')

    inferMatchExpr tm (TypedMatchExpr me ty) env subst = do
      (me', env', subst') <- inferMatchExpr tm me env subst
      case unify' ty (typeOf me') subst' of
        Just (ty'', subst'') ->
          return (me', env', subst'')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected type '" ++ show ty ++ "' with actual type '" ++ show (typeOf me') ++ "'."
          return (me', env, subst')
        
    inferMatchExpr tm (VarMatch name) env subst =
      case tm of
        Just t ->
          return ((TVarMatch name, t), Map.insert name t env, subst)
        Nothing -> do
          t <- mkTypeVar
          return ((TVarMatch name, t), Map.insert name t env, subst)

    inferMatchExpr tm (IntMatchExpr n) env subst =
      return ((TIntMatchExpr n, intType), env, subst)
      
    inferMatchExpr tm (StringMatchExpr s) env subst =
      return ((TStringMatchExpr s, stringType), env, subst)
      
    inferMatchExpr tm (BoolMatchExpr b) env subst =
      return ((TBoolMatchExpr b, boolType), env, subst)
    
    inferStatement :: Statement -> Env -> Substitution -> IO (TypedStatement, Env, Substitution)
    inferStatement (IfStatement e s Nothing) env subst = do
      (e', envExpr, substExpr) <- inferExpr e env subst
      (s', envBody, substBody) <- inferStatement s envExpr substExpr
      subst' <- mergeSubstitution substExpr substBody
      (env', subst'') <- mergeEnv envExpr envBody subst'
      return (TIfStatement e' s' Nothing, env', subst'')
      
    inferStatement (IfStatement e sThen (Just sElse)) env subst = do
      (e', env', subst') <- inferExpr e env subst
      (sThen', envThen, substThen) <- inferStatement sThen env' subst'
      (sElse', envElse, substElse) <- inferStatement sElse env' subst'
      subst' <- mergeSubstitution substThen substElse
      (env'', subst'') <- mergeEnv envThen envElse subst'
      return (TIfStatement e' sThen' (Just sElse'), env'', subst'')
      
    inferStatement (WhileStatement e s) env subst = do
      (e', envExpr, substExpr) <- inferExpr e env subst
      (s', envBody, substBody) <- inferStatement s envExpr substExpr
      subst' <- mergeSubstitution substExpr substBody
      (env', subst'') <- mergeEnv envExpr envBody subst'
      return (TWhileStatement e' s', env', subst'')

    inferStatement (ForStatement me e s) env subst = do
      (e', envExpr, substExpr) <- inferExpr e env subst
      (me', envMatchExpr, substMatchExpr) <- inferMatchExpr (Just $ typeOf e') me envExpr substExpr
      (s', envBody, substBody) <- inferStatement s envMatchExpr substMatchExpr
      subst' <- mergeSubstitution substMatchExpr substBody
      (env', subst'') <- mergeEnv envMatchExpr envBody subst'
      return (TForStatement me' e' s', env', subst'')
      
    inferStatement (CompoundStatement ss) env subst = do
      (ss', env', subst') <- inferList inferStatement env subst ss
      return (TCompoundStatement ss', env', subst')
      
    inferStatement (AssignStatement (Left me) e) env subst = do
      (e', envExpr, substExpr) <- inferExpr e env subst
      (me', envMatchExpr, substMatchExpr) <- inferMatchExpr (Just $ typeOf e') me envExpr substExpr
      return (TAssignStatement (Left me') e', envMatchExpr, substMatchExpr)
      
    inferStatement (AssignStatement (Right lve) e) env subst = do
      (e', env, substExpr) <- inferExpr e env subst
      (lve', env', substLValueExpr) <- inferLValueExpr (Just $ typeOf e') lve env substExpr
      return (TAssignStatement (Right lve') e', env', substLValueExpr)
      
    inferStatement (MatchStatement e mes) env subst = do
      (e', envExpr, substExpr) <- inferExpr e env subst
      (mes', env', subst') <- inferList f envExpr substExpr mes
      return (TMatchStatement e' mes', env', subst')
      where f (me, s) env subst = do
                (me', env', subst') <- inferMatchExpr Nothing me env subst
                (s', env'', subst'') <- inferStatement s env' subst'
                return ((me', s'), env'', subst'')
                
    inferStatement (ReturnStatement (Just e)) env subst = do
      (e', env', subst') <- inferExpr e env subst
      return (TReturnStatement (Just e'), env', subst')
      
    inferStatement (ReturnStatement Nothing) env subst =
      return (TReturnStatement Nothing, env, subst)
      
    inferStatement BreakStatement env subst =
      return (TBreakStatement, env, subst)
      
    inferStatement ContinueStatement env subst =
      return (TContinueStatement, env, subst)
      
    inferStatement (DeclStatement decl) env subst = do
      (decl', env', subst') <- inferDecl decl env subst
      return (TDeclStatement decl', env', subst')

    inferBinopExpr mkeExpr mkType env subst e1 e2 = do
      (e1', env1, subst1) <- inferExpr e1 env subst
      (e2', env2, subst2) <- inferExpr e2 env1 subst1
      (t, subst') <- mkType e1' e2' subst2
      return ((mkeExpr e1' e2', t), env2, subst')
    
    mkMathOpType e1 e2 subst = do
      (expectedType, subst') <- mkAllOfType subst [intType, realType]
      case unify' (typeOf e1) expectedType subst' of
        Just (t1, subst1) ->
          case unify' (typeOf e2) expectedType subst1 of
            Just (t2, subst2) ->
              case unify' t1 t2 subst2 of
                Just (t, subst') -> return (t, subst')
                Nothing -> do
                  putStrLn $ "Cannot unify type '" ++ show t1 ++ "' with type '" ++ show t2 ++ "'."
                  return (Error, subst)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++ "' with type '" ++ show expectedType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++ "' with type '" ++ show expectedType ++ "'."
          return (Error, subst)
          
    mkLogicalOpType e1 e2 subst =
      case unify' (typeOf e1) boolType subst of
        Just (t1, subst1) ->
          case unify' (typeOf e2) boolType subst1 of
            Just (t2, subst2) ->
              case unify' t1 t2 subst2 of
                Just (_, subst') ->
                  return (boolType, subst')
                Nothing -> do
                  putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++ "' with type '" ++ show (typeOf e2) ++ "'."
                  return (Error, subst)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++ "' with type '" ++ show boolType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++ "' with type '" ++ show boolType ++ "'."
          return (Error, subst)
      
    mkEqOpType e1 e2 subst =
      case unify' (typeOf e1) (typeOf e2) subst of
        Just (_, subst') ->
          return (boolType, subst')
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++ "' with type '" ++ show (typeOf e2) ++ "'."
          return (Error, subst)

    mkRelOpType e1 e2 subst = do
      (expectedType, subst') <- mkAllOfType subst [intType, realType]
      case unify' (typeOf e1) expectedType subst of
        Just (_, subst1) -> do
          case unify' (typeOf e2) expectedType subst1 of
            Just (_, subst2) -> do
              return (boolType, subst2)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++ "' with type '" ++ show expectedType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Can not unify type '" ++ show (typeOf e1) ++ "' with type '" ++ show expectedType ++ "'."
          return (Error, subst)
      
    inferExpr :: Expr -> Env -> Substitution -> IO (TypedExpr, Env, Substitution)
    inferExpr (IntExpr n) env subst =
      return ((TIntExpr n, intType), env, subst)

    inferExpr (RealExpr n) env subst =
      return ((TRealExpr n, realType), env, subst)
      
    inferExpr (BoolExpr b) env subst =
      return ((TBoolExpr b, boolType), env, subst)
      
    inferExpr (StringExpr s) env subst =
      return ((TStringExpr s, stringType), env, subst)

    inferExpr (OrExpr e1 e2) env subst =
      inferBinopExpr TOrExpr mkLogicalOpType env subst e1 e2

    inferExpr (AndExpr e1 e2) env subst =
      inferBinopExpr TAndExpr mkLogicalOpType env subst e1 e2

    inferExpr (EqExpr e1 e2) env subst =
      inferBinopExpr TEqExpr mkEqOpType env subst e1 e2
      
    inferExpr (NeqExpr e1 e2) env subst =
      inferBinopExpr TNeqExpr mkEqOpType env subst e1 e2
      
    inferExpr (LtExpr e1 e2) env subst =
      inferBinopExpr TLtExpr mkRelOpType env subst e1 e2
      
    inferExpr (GtExpr e1 e2) env subst =
      inferBinopExpr TGtExpr mkRelOpType env subst e1 e2
      
    inferExpr (LeExpr e1 e2) env subst =
      inferBinopExpr TLeExpr mkRelOpType env subst e1 e2

    inferExpr (GeExpr e1 e2) env subst =
      inferBinopExpr TGeExpr mkRelOpType env subst e1 e2
      
    inferExpr (AddExpr e1 e2) env subst =
      inferBinopExpr TAddExpr mkMathOpType env subst e1 e2
      
    inferExpr (SubExpr e1 e2) env subst =
      inferBinopExpr TSubExpr mkMathOpType env subst e1 e2
      
    inferExpr (MultExpr e1 e2) env subst =
      inferBinopExpr TMultExpr mkMathOpType env subst e1 e2
      
    inferExpr (DivExpr e1 e2) env subst =
      inferBinopExpr TDivExpr mkMathOpType env subst e1 e2

    inferExpr (UnaryMinusExpr e) env subst = do
      (e', env', subst') <- inferExpr e env subst
      case typeOf e' of
        Name "Int" [] -> return ((TUnaryMinusExpr e', intType), env', subst')
        Name "Real" [] -> return ((TUnaryMinusExpr e', realType), env', subst')
        _ -> do putStrLn $ "Couldn't match expected type 'Int' or 'Real' with actual type '" ++ show (typeOf e') ++ "'."
                return ((TUnaryMinusExpr e', Error), env, subst)

    inferExpr (BangExpr e) env subst = do
      (e', env', subst') <- inferExpr e env subst
      case typeOf e' of
        Name "Bool" [] -> return ((TBangExpr e', boolType), env, subst')
        _ -> do putStrLn $ "Couldn't match expected type 'Bool' with actual type '" ++ show (typeOf e') ++ "'."
                return ((TBangExpr e', boolType), env', subst')

    inferExpr (CallExpr f arg) env subst = do
      (f', env', subst') <- inferExpr f env subst
      (arg', env'', subst'') <- inferExpr arg env' subst'
      case typeOf f' of
        Arrow tDom tCod -> do
          case unify' tDom (typeOf arg') subst'' of
            Just (t, _) ->
              return ((TCallExpr f' arg', tCod), env'', subst'')
            Nothing -> do
              putStrLn $ "Couldn't match expected type '" ++ show tDom ++ "' with actual type '" ++ show (typeOf arg') ++ "'."
              return ((TCallExpr f' arg', Error), env, subst)
        TypeVar u -> do
          tCod <- mkTypeVar
          let ty = Arrow (typeOf arg') tCod
          let subst''' = Map.insert u ty subst'' 
          return ((TCallExpr f' arg', tCod), env'', subst''')
        _ -> do
          putStrLn $ "Couldn't match expected type '" ++ show (typeOf arg') ++
            " -> ???' with actual type '" ++ show (typeOf f') ++ "'."
          return ((TCallExpr f' arg', Error), env, subst)

    inferExpr (TypeConstrainedExpr e ty) env subst = do
      (e', env', subst') <- inferExpr e env subst
      if ty /= typeOf e' then do
        putStrLn $ "Couldn't match expected type '" ++ show ty ++ "' with actual type '" ++ show (typeOf e') ++ "'."
        return (e', env', subst')
      else return (e', env, subst)
      
    inferExpr (ListExpr es) env subst = do
      (es', env', subst') <- inferList inferExpr env subst es
      let (_, types) = List.unzip es'
      (ty, subst'') <- unifyTypes types subst'
      return ((TListExpr es', Array ty), env', subst'')
      where f (ty, subst) ty' = unify ty ty' subst
      
    inferExpr (TupleExpr es) env subst = do
      (es', env', subst') <- inferList inferExpr env subst es
      let (_, types) = List.unzip es'
      return ((TTupleExpr es', Tuple types), env', subst')
      
    inferExpr (SetExpr es) env subst = do
      (es', env', subst') <- inferList inferExpr env subst es
      let (_, types) = List.unzip es'
      (ty, subst'') <- unifyTypes types subst'
      return ((TSetExpr es', Set ty), env', subst'')
      where f (ty, subst) ty' = unify ty ty' subst

    inferExpr (RecordExpr fields) env subst = do
      let f (name, e) env subst = do
              (e', env', subst') <- inferExpr e env subst
              return ((name, e'), env', subst')
      (fields', env', subst') <- inferList f env subst fields
      let recordTypes = List.map mkStringTypePair fields'
      return ((TRecordExpr fields', Record recordTypes), env', subst')
      where mkStringTypePair (name, (_, t)) = (name, t)

    inferExpr (LValue lve) env subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env subst
      return ((TLValue lve', typeOf lve'), env', subst')

    inferExpr (LambdaExpr mes s) env subst = do
      (mes', env', subst') <- inferList (inferMatchExpr Nothing) env subst mes
      (s', env'', subst'') <- inferStatement s env' subst'
      let (_, types) = List.unzip mes'
      (ty, subst''') <- mergeReturns s' subst''
      return ((TLambdaExpr mes' s', mkArrowType types ty), env'', subst''')

    mergeReturns :: TypedStatement -> Substitution -> IO (Type, Substitution)
    mergeReturns s subst =
      let types = returns s
      in unifyTypes types subst
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
        returns (TReturnStatement (Just (_, ty))) = [ty]
        returns (TReturnStatement Nothing) = [voidType]
        returns _ = []

    inferLValueExpr :: Maybe Type -> LValueExpr -> Env -> Substitution -> IO (TypedLValueExpr, Env, Substitution)
    inferLValueExpr tm (VarExpr name) env subst =
      case tm of
        Just t -> -- Writing to variable
          return ((TVarExpr name, t), Map.insert name t env, subst)
        Nothing -> -- Reading from variable
          case Map.lookup name env of
            Just ty -> do
              return ((TVarExpr name, find subst ty), env, subst)
            Nothing -> do
              putStrLn $ "Not in scope: " ++ name
              return ((TVarExpr name, Error), env, subst)
      where find subst (TypeVar u) =
              case Map.lookup u subst of
                Just ty -> find subst ty
                Nothing -> (TypeVar u)
            find subst ty = ty
        
    inferLValueExpr _ (FieldAccessExpr lve field) env subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env subst
      case typeOf lve' of
        Record fields ->
          case List.find ((field ==) . fst) fields of
            Just (_, t) ->
              return ((TFieldAccessExpr lve' field, t), env', subst')
            Nothing -> do
              putStrLn $ field ++ " is not a field of type '" ++ show (typeOf lve') ++ "'"
              return ((TFieldAccessExpr lve' field, Error), env, subst)
        t -> do
          putStrLn $ "Couldn't match expected record type with actual type '" ++ show t ++ "'"
          return ((TFieldAccessExpr lve' field, Error), env, subst)

    inferLValueExpr _ (ArrayAccessExpr lve e) env subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env subst
      (e', env'', subst'') <- inferExpr e env' subst'
      case (typeOf lve', typeOf e') of
        (Array arrayTy, Name "Int" []) ->
          return ((TArrayAccessExpr lve' e', arrayTy), env'', subst'')
        (Array _, t) -> do
          putStrLn $ "Couldn't match expected array type 'int' with actual type '" ++ show t ++ "'."
          return ((TArrayAccessExpr lve' e', t), env'', subst'')
        (t, _) -> do
          putStrLn $ "Couldn't match expected array type with with actual type '" ++ show t ++ "'."
          return ((TArrayAccessExpr lve' e', t), env'', subst)