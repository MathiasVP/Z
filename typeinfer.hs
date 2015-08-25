module TypeInfer where
import qualified Data.List as List
import qualified Data.Map as Map
import Control.Monad
import TypedAst
import Unification
import Data.Maybe as Maybe
import Data.Ord

mkArrowType :: [Type] -> Type -> Type
mkArrowType types retTy = List.foldr Arrow retTy types

mkAllOfType :: Env -> ArgOrd -> Substitution -> [Type] -> IO (Type, Substitution)
mkAllOfType env argOrd subst types = do
  u <- mkTypeVar
  (_, subst') <- unify u (AllOf types) env argOrd subst
  return (u, subst')

normaliseFields :: Ord a => [(a, b)] -> [(a, b)]
normaliseFields = List.sortBy (comparing fst)

equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2

exprOf = fst
typeOf = snd

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
      let env'' = Map.insert name (mkArrowType types retTy') env'
      (statement', env''', argOrd'', subst'') <- inferStatement statement env'' argOrd' subst'
      (retTy'', subst''') <- mergeReturns statement' env''' argOrd subst''
      let globEnv = Map.insert name (mkArrowType types retTy'') env
      case unify' retTy' retTy'' env'' argOrd'' subst''' of
        Just (retTy, subst) ->
          return (TFunDecl name tyArgs args' retTy statement', globEnv, argOrd, subst)
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected return type '" ++ show retTy ++
                     "' with actual type '" ++ show retTy' ++ "'."
          return (TFunDecl name tyArgs args' retTy' statement', globEnv, argOrd, subst)

    inferMatchExpr tm (TupleMatchExpr mes) env argOrd subst = do
      (mes', env', argOrd', subst') <-
        case tm of
          Just (Tuple ts) ->
            if List.length ts == List.length mes then
              let mesWithTypes = case tm of
                                  Just (Tuple ts) ->
                                    List.map inferMatchExpr (List.map Just ts)
                                  Nothing -> []
                  f (me, n) = (mesWithTypes !! n) me
              in inferList f env argOrd subst (List.zip mes [0..])
            else do putStrLn $ "Match error: Couldn't unify expression '" ++
                               show (TupleMatchExpr mes) ++ "' with type '" ++
                               show (Tuple ts) ++ "'."
                    return ([], env, argOrd, subst)
          Just (TypeVar u) -> do
            types <- replicateM (List.length mes) mkTypeVar
            (_, subst') <- unify (TypeVar u) (Tuple types) env argOrd subst 
            inferList (\(me, ty) -> inferMatchExpr (Just ty) me) env argOrd subst' (List.zip mes types)
          Nothing ->
            inferList (inferMatchExpr Nothing) env argOrd subst mes
      return ((TTupleMatchExpr mes', Tuple (List.map typeOf mes')), env', argOrd', subst')

    inferMatchExpr tm (ListMatchExpr mes) env argOrd subst  = do
      (mes', env', argOrd', subst') <-
        case tm of
          Just (Array t) -> inferList (inferMatchExpr (Just t)) env argOrd subst mes
          Just (TypeVar u) -> do
            base <- mkTypeVar
            (_, subst') <- unify (TypeVar u) (Array base) env argOrd subst
            inferList (inferMatchExpr (Just base)) env argOrd subst' mes
          Nothing -> inferList (inferMatchExpr Nothing) env argOrd subst mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') env argOrd subst'
      return ((TListMatchExpr mes', Array ty), env', argOrd', subst'')
      
    inferMatchExpr tm (SetMatchExpr mes) env argOrd subst  = do
      (mes', env', argOrd', subst') <-
        case tm of
          Just (Set t) -> inferList (inferMatchExpr (Just t)) env argOrd subst mes
          Just (TypeVar u) -> do
            base <- mkTypeVar
            (_, subst') <- unify (TypeVar u) (Set base) env argOrd subst 
            inferList (inferMatchExpr (Just base)) env argOrd subst'  mes
          Nothing -> inferList (inferMatchExpr Nothing) env argOrd subst mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') env argOrd subst' 
      return ((TSetMatchExpr mes', Set ty), env', argOrd', subst'')
      
    inferMatchExpr tm (RecordMatchExpr fields) env argOrd subst  = do
      (fields', env', argOrd', subst') <-
        case tm of
          Just (Record fields') ->
            if equalRecordFields fields fields' then
              let typesm = List.map (Just . typeOf) (normaliseFields fields')
                  f tm (name, me) env argOrd subst  = do
                    (me', env', argOrd', subst') <- inferMatchExpr tm me env argOrd subst 
                    return ((name, me'), env', argOrd', subst')
                  fs = List.map f typesm
                  inferField (entry, n) = (fs !! n) entry
              in inferList inferField env argOrd subst (List.zip (normaliseFields fields) [0..])
            else
              return ([], env, argOrd, subst)
          Just (TypeVar u) -> do
            types <- replicateM (List.length fields) mkTypeVar
            let fields' = List.zip (normaliseFields fields) types
            let mkField ((s, _), ty) = (s, ty)
            (_, subst') <- unify (TypeVar u) (Record (List.map mkField fields')) env argOrd subst 
            let f ((name, me), ty) env argOrd subst  = do
                (me', env', argOrd', subst') <- inferMatchExpr (Just ty) me env argOrd subst 
                return ((name, me'), env', argOrd', subst')
            inferList f env argOrd subst' fields'
          Nothing ->
            let f (name, me) env argOrd subst  = do
                  (me', env, argOrd', subst') <- inferMatchExpr Nothing me env argOrd subst 
                  return ((name, me'), Map.insert name (typeOf me') env, argOrd', subst')
            in inferList f env argOrd subst fields
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      return ((TRecordMatchExpr fields', Record recordTypes), env', argOrd', subst')

    inferMatchExpr tm (TypedMatchExpr me ty) env argOrd subst  = do
      (me', env', argOrd', subst') <- inferMatchExpr tm me env argOrd subst 
      case unify' ty (typeOf me') env' argOrd' subst'  of
        Just (ty'', subst'') -> return (me', env', argOrd', subst'')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected type '" ++ show ty ++
                     "' with actual type '" ++ show (typeOf me') ++ "'."
          return (me', env, argOrd', subst)

    inferMatchExpr tm (VarMatch name) env argOrd subst  =
      case tm of
        Just t ->
          return ((TVarMatch name, t), Map.insert name t env, argOrd, subst)
        Nothing -> do
          t <- mkTypeVar
          return ((TVarMatch name, t), Map.insert name t env, argOrd, subst)

    inferMatchExpr tm (IntMatchExpr n) env argOrd subst  =
      return ((TIntMatchExpr n, IntType), env, argOrd, subst)
      
    inferMatchExpr tm (StringMatchExpr s) env argOrd subst  =
      return ((TStringMatchExpr s, StringType), env, argOrd, subst)

    inferMatchExpr tm (BoolMatchExpr b) env argOrd subst  =
      return ((TBoolMatchExpr b, BoolType), env, argOrd, subst)
    
    inferStatement :: Statement -> Env -> ArgOrd -> Substitution -> IO (TypedStatement, Env, ArgOrd, Substitution)
    inferStatement (IfStatement e s Nothing) env argOrd subst  = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst 
      (s', envBody, _, substBody) <- inferStatement s envExpr argOrd' substExpr 
      subst' <- mergeSubstitution env argOrd substExpr substBody 
      (env', subst'') <- mergeEnv envExpr envBody argOrd subst' 
      return (TIfStatement e' s' Nothing, env', argOrd', subst'')
      
    inferStatement (IfStatement e sThen (Just sElse)) env argOrd subst  = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
      (sThen', envThen, _, substThen) <- inferStatement sThen env' argOrd' subst' 
      (sElse', envElse, _, substElse) <- inferStatement sElse env' argOrd' subst' 
      subst' <- mergeSubstitution env argOrd substThen substElse 
      (env'', subst'') <- mergeEnv envThen envElse argOrd subst' 
      return (TIfStatement e' sThen' (Just sElse'), env'', argOrd', subst'')
      
    inferStatement (WhileStatement e s) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst 
      (s', envBody, _, substBody) <- inferStatement s envExpr argOrd' substExpr 
      subst' <- mergeSubstitution env argOrd substExpr substBody 
      (env', subst'') <- mergeEnv envExpr envBody argOrd subst' 
      return (TWhileStatement e' s', env', argOrd', subst'')

    inferStatement (ForStatement me e s) env argOrd subst  = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst 
      t <- mkTypeVar
      (t', subst') <-
        case unify' (typeOf e') (AllOf [Array t, Set t]) envExpr argOrd' substExpr  of
          Just (_, subst') -> return (t, subst')
          Nothing -> do
            putStrLn $ "Error: Cannot iterate over expression of type '" ++
                       show (typeOf e') ++ "'."
            return (Error, substExpr)
      (me', envMatchExpr, argOrd'', substMatchExpr) <- inferMatchExpr (Just t') me envExpr argOrd' subst' 
      (s', envBody, _, substBody) <- inferStatement s envMatchExpr argOrd'' substMatchExpr 
      subst'' <- mergeSubstitution env argOrd substMatchExpr substBody 
      (env', subst''') <- mergeEnv envMatchExpr envBody argOrd subst'' 
      return (TForStatement me' e' s', env', argOrd'', subst''')

    inferStatement (CompoundStatement ss) env argOrd subst = do
      (ss', env', argOrd', subst') <- inferList inferStatement env argOrd subst ss
      return (TCompoundStatement ss', env', argOrd', subst')

    inferStatement (AssignStatement (Left me) e) env argOrd subst  = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst 
      (me', envMatchExpr, argOrd'', substMatchExpr) <-
        inferMatchExpr (Just $ typeOf e') me envExpr argOrd' substExpr 
      return (TAssignStatement (Left me') e', envMatchExpr, argOrd'', substMatchExpr)

    inferStatement (AssignStatement (Right lve) e) env argOrd subst  = do
      (e', env, argOrd', substExpr) <- inferExpr e env argOrd subst 
      (lve', env', substLValueExpr) <- inferLValueExpr (Just $ typeOf e') lve env argOrd' substExpr 
      return (TAssignStatement (Right lve') e', env', argOrd', substLValueExpr)

    inferStatement (MatchStatement e mes) env argOrd subst = do
      (e', envExpr, argOrd', substExpr) <- inferExpr e env argOrd subst 
      (mes', env', _, subst') <- inferList (f (typeOf e')) envExpr argOrd' substExpr mes
      return (TMatchStatement e' mes', env', argOrd', subst')
      where f matchType (me, s) env argOrd subst = do
              (me', env', argOrd', subst') <- inferMatchExpr Nothing me env argOrd subst 
              (ty, subst') <- unify matchType (typeOf me') env argOrd subst' 
              let subst'' = case matchType of
                              TypeVar u -> Map.insert u ty subst'
              (s', env'', argOrd'', subst''') <- inferStatement s env' argOrd' subst''
              return ((me', s'), env'', argOrd'', subst''')
                
    inferStatement (ReturnStatement e) env argOrd subst  = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
      return (TReturnStatement e', env', argOrd', subst')
      
    inferStatement BreakStatement env argOrd subst  =
      return (TBreakStatement, env, argOrd, subst)
      
    inferStatement ContinueStatement env argOrd subst  =
      return (TContinueStatement, env, argOrd, subst)
      
    inferStatement (DeclStatement decl) env argOrd subst  = do
      (decl', env', argOrd', subst') <- inferDecl decl env argOrd subst 
      return (TDeclStatement decl', env', argOrd', subst')

    inferBinopExpr mkeExpr mkType env argOrd subst e1 e2 = do
      (e1', env1, argOrd1, subst1) <- inferExpr e1 env argOrd subst 
      (e2', env2, argOrd2, subst2) <- inferExpr e2 env1 argOrd1 subst1
      (t, subst') <- mkType e1' e2' env2 argOrd2 subst2 
      return ((mkeExpr e1' e2', t), env2, argOrd2, subst')
    
    mkMathOpType e1 e2 env argOrd subst = do
      (expectedType, subst') <- mkAllOfType env argOrd subst [IntType, RealType] 
      case unify' (typeOf e1) expectedType env argOrd subst'  of
        Just (t1, subst1) ->
          case unify' (typeOf e2) expectedType env argOrd subst1  of
            Just (t2, subst2) ->
              case unify' t1 t2 env argOrd subst2  of
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
          
    mkLogicalOpType e1 e2 env argOrd subst  =
      case unify' (typeOf e1) BoolType env argOrd subst  of
        Just (t1, subst1) ->
          case unify' (typeOf e2) BoolType env argOrd subst1  of
            Just (t2, subst2) ->
              case unify' t1 t2 env argOrd subst2  of
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
      case unify' (typeOf e1) (typeOf e2) env argOrd subst  of
        Just (_, subst') ->
          return (BoolType, subst')
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show (typeOf e2) ++ "'."
          return (Error, subst)

    mkRelOpType e1 e2 env argOrd subst = do
      (expectedType, subst') <- mkAllOfType env argOrd subst [IntType, RealType] 
      case unify' (typeOf e1) expectedType env argOrd subst of
        Just (_, subst1) -> do
          case unify' (typeOf e2) expectedType env argOrd subst1 of
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
      
    inferExpr (IntExpr n) env argOrd subst  =
      return ((TIntExpr n, IntType), env, argOrd, subst)

    inferExpr (RealExpr n) env argOrd subst  =
      return ((TRealExpr n, RealType), env, argOrd, subst)
      
    inferExpr (BoolExpr b) env argOrd subst  =
      return ((TBoolExpr b, BoolType), env, argOrd, subst)
      
    inferExpr (StringExpr s) env argOrd subst  =
      return ((TStringExpr s, StringType), env, argOrd, subst)

    inferExpr (OrExpr e1 e2) env argOrd subst  =
      inferBinopExpr TOrExpr mkLogicalOpType env argOrd subst e1 e2

    inferExpr (AndExpr e1 e2) env argOrd subst  =
      inferBinopExpr TAndExpr mkLogicalOpType env argOrd subst  e1 e2

    inferExpr (EqExpr e1 e2) env argOrd subst  =
      inferBinopExpr TEqExpr mkEqOpType env argOrd subst  e1 e2
      
    inferExpr (NeqExpr e1 e2) env argOrd subst  =
      inferBinopExpr TNeqExpr mkEqOpType env argOrd subst  e1 e2
      
    inferExpr (LtExpr e1 e2) env argOrd subst  =
      inferBinopExpr TLtExpr mkRelOpType env argOrd subst  e1 e2
      
    inferExpr (GtExpr e1 e2) env argOrd subst  =
      inferBinopExpr TGtExpr mkRelOpType env argOrd subst  e1 e2
      
    inferExpr (LeExpr e1 e2) env argOrd subst  =
      inferBinopExpr TLeExpr mkRelOpType env argOrd subst  e1 e2

    inferExpr (GeExpr e1 e2) env argOrd subst  =
      inferBinopExpr TGeExpr mkRelOpType env argOrd subst  e1 e2
      
    inferExpr (AddExpr e1 e2) env argOrd subst  =
      inferBinopExpr TAddExpr mkMathOpType env argOrd subst  e1 e2
      
    inferExpr (SubExpr e1 e2) env argOrd subst  =
      inferBinopExpr TSubExpr mkMathOpType env argOrd subst  e1 e2
      
    inferExpr (MultExpr e1 e2) env argOrd subst  =
      inferBinopExpr TMultExpr mkMathOpType env argOrd subst  e1 e2
      
    inferExpr (DivExpr e1 e2) env argOrd subst  =
      inferBinopExpr TDivExpr mkMathOpType env argOrd subst  e1 e2

    inferExpr (UnaryMinusExpr e) env argOrd subst  = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
      case unify' (typeOf e') (AllOf [IntType, RealType]) env' argOrd' subst'  of
        Just (t, subst'') -> return ((TUnaryMinusExpr e', t), env', argOrd', subst'')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Int' or 'Real' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TUnaryMinusExpr e', Error), env, argOrd', subst)

    inferExpr (BangExpr e) env argOrd subst  = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
      case unify' (typeOf e') BoolType env' argOrd' subst'  of
        Just (t, subst'') -> return ((TBangExpr e', BoolType), env', argOrd', subst'')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Bool' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TBangExpr e', BoolType), env', argOrd', subst')

    inferExpr (CallExpr f arg) env argOrd subst  = do
      (f', env', argOrd', subst') <- inferExpr f env argOrd subst 
      (arg', env'', argOrd'', subst'') <- inferExpr arg env' argOrd' subst' 
      tDom <- mkTypeVar
      tCod <- mkTypeVar
      case unify' (typeOf f') (Arrow tDom tCod) env'' argOrd'' subst''  of
        Just(t, subst''') ->
          case unify' (typeOf arg') tDom env'' argOrd'' subst'''  of
            Just _ -> --- TODO: We *really* shouldn't ignore this substitution
              return ((TCallExpr f' arg', tCod), env'', argOrd'', subst''')
            Nothing -> do
              putStrLn $ "Couldn't match expected type '" ++ show tDom ++
                         "' with actual type '" ++ show (typeOf arg') ++ "'."
              return ((TCallExpr f' arg', Error), env, argOrd'', subst)
        Nothing -> do
            putStrLn $ "Couldn't match expected type '" ++ show (Arrow tDom tCod) ++
                       "' with actual type '" ++ show (typeOf f') ++ "'."
            return ((TCallExpr f' arg', Error), env, argOrd'', subst)

    inferExpr (TypeConstrainedExpr e ty) env argOrd subst  = do
      (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
      case unify' (typeOf e') ty env' argOrd' subst'  of
        Nothing -> do
          putStrLn $ "Couldn't match expected type '" ++ show ty ++
                     "' with actual type '" ++ show (typeOf e') ++ "'."
          return (e', env', argOrd', subst')
        Just (t, subst') -> return (e', env', argOrd', subst')

    inferExpr (ListExpr es) env argOrd subst  = do
      (es', env', argOrd', subst') <- inferList inferExpr env argOrd subst es
      (ty, subst'') <- unifyTypes (List.map snd es') env argOrd subst' 
      return ((TListExpr es', Array ty), env', argOrd', subst'')
      
    inferExpr (TupleExpr es) env argOrd subst  = do
      (es', env', argOrd', subst') <- inferList inferExpr env argOrd subst es
      return ((TTupleExpr es', Tuple (List.map snd es')), env', argOrd', subst')
      
    inferExpr (SetExpr es) env argOrd subst  = do
      (es', env', argOrd', subst') <- inferList inferExpr env argOrd subst es
      (ty, subst'') <- unifyTypes (List.map snd es') env argOrd subst' 
      return ((TSetExpr es', Set ty), env', argOrd', subst'')

    inferExpr (RecordExpr fields) env argOrd subst  = do
      let f (name, e) env argOrd subst  = do
            (e', env', argOrd', subst') <- inferExpr e env argOrd subst 
            return ((name, e'), env', argOrd', subst')
      (fields', env', argOrd', subst') <- inferList f env argOrd subst fields
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      return ((TRecordExpr fields', Record recordTypes), env', argOrd', subst')

    inferExpr (LValue lve) env argOrd subst = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst 
      return ((TLValue lve', typeOf lve'), env', argOrd, subst')

    inferExpr (LambdaExpr mes s) env argOrd subst = do
      (mes', env', argOrd', subst') <- inferList (inferMatchExpr Nothing) env argOrd subst mes
      (s', env'', argOrd'', subst'') <- inferStatement s env' argOrd' subst' 
      (ty, subst''') <- mergeReturns s' env'' argOrd'' subst'' 
      return ((TLambdaExpr mes' s', mkArrowType (List.map snd mes') ty), env'', argOrd', subst''')

    mergeReturns :: TypedStatement -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
    mergeReturns s env argOrd subst  =
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

    inferLValueExpr tm (VarExpr name) env argOrd subst  =
      case tm of
        Just t -> -- Writing to variable
          return ((TVarExpr name, t), Map.insert name t env, subst)
        Nothing -> -- Reading from variable
          case Map.lookup name env of
            Just ty ->
              return ((TVarExpr name, find subst ty), env, subst)
            Nothing -> do
              putStrLn $ "Not in scope: " ++ name
              return ((TVarExpr name, Error), env, subst)
      where find subst (TypeVar u) =
              case Map.lookup u subst of
                Just ty -> find subst ty
                Nothing -> (TypeVar u)
            find subst ty = ty

    -- TODO: Test this function
    inferLValueExpr tm (FieldAccessExpr lve field) env argOrd subst  = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst 
      case tm of
        Just t -> do -- Writing to variable
          (_, subst'') <- unify (typeOf lve') (Record [(field, t)]) env argOrd subst' 
          return ((TFieldAccessExpr lve' field, t), env', subst'')
        Nothing -> do -- Reading from variable
          u <- mkTypeVar
          case unify' (typeOf lve') (Record [(field, u)]) env' argOrd subst'  of
            Just (_, subst'') ->
              return ((TFieldAccessExpr lve' field, u), env', subst'')
            Nothing -> do
              putStrLn $ field ++ " is not a field of type '" ++ show (typeOf lve') ++ "'"
              return ((TFieldAccessExpr lve' field, Error), env, subst)

    -- TODO: Test this function
    inferLValueExpr tm (ArrayAccessExpr lve e) env argOrd subst  = do
      (lve', env', subst') <- inferLValueExpr Nothing lve env argOrd subst 
      (e', env'', argOrd', subst'') <- inferExpr e env' argOrd subst' 
      case tm of
        Just t -> do -- Writing to variable
          (_, subst''') <- unify (typeOf lve') (Array t) env argOrd subst'' 
          (_, subst'''') <- unify (typeOf e') IntType env argOrd subst''' 
          return ((TArrayAccessExpr lve' e', t), env'', subst'''')
        Nothing -> do -- Reading from variable
          arrayTy <- mkTypeVar
          case unify' (typeOf lve') (Array arrayTy) env'' argOrd' subst''  of
            Just (_, subst''') ->
              case unify' (typeOf e') IntType env'' argOrd' subst'''  of
                Just (_, subst'''') ->
                  return ((TArrayAccessExpr lve' e', arrayTy), env'', subst'''')
                Nothing -> do
                  putStrLn $ "Couldn't match expected type '" ++ (show IntType) ++
                             "' with actual type '" ++ show (typeOf e') ++ "'."
                  return ((TArrayAccessExpr lve' e', Error), env'', subst)
            Nothing -> do
              putStrLn $ "Couldn't match expected array type with with actual type '" ++
                         show (Array arrayTy) ++ "'."
              return ((TArrayAccessExpr lve' e', Error), env'', subst)
  
    replaceType subst ty =
      case ty of
        Name s types -> Name s (List.map (replaceType subst) types)
        Array ty -> Array (replaceType subst ty)
        Tuple [ty] -> replaceType subst ty
        Tuple types -> Tuple (List.map (replaceType subst) types)
        Set ty -> Set (replaceType subst ty)
        Record fields -> let f (s, ty) =
                              (s, replaceType subst ty)
                         in Record (List.map f fields)
        Arrow tDom tCod -> Arrow (replaceType subst tDom) (replaceType subst tCod)
        Union t1 t2 -> Union (replaceType subst t1) (replaceType subst t2)
        TypeVar u -> case Map.lookup u subst of
                      Just (TypeVar u') -> if u == u' then
                                            TypeVar u'
                                           else replaceType subst (TypeVar u')
                      Just t -> replaceType subst t
                      Nothing -> TypeVar u
        Error -> Error
        AllOf types -> AllOf (List.map (replaceType subst) types)

    replaceDecl subst td =
      case td of
        TTypeDecl s targs t ->
          TTypeDecl s targs (replaceType subst t)
        TFunDecl name targs args retTy s ->
          TFunDecl name targs (List.map (replaceMatchExpr subst) args)
                              (replaceType subst retTy) (replaceStatement subst s)

    replaceMatchExpr subst (tme, ty) =
      let tme' =
            case tme of
              TTupleMatchExpr tmes ->
                TTupleMatchExpr (List.map (replaceMatchExpr subst) tmes)
              TListMatchExpr tmes ->
                TListMatchExpr (List.map (replaceMatchExpr subst) tmes)
              TSetMatchExpr tmes ->
                TSetMatchExpr (List.map (replaceMatchExpr subst) tmes)
              TRecordMatchExpr fields ->
                let f (s, tme) = (s, replaceMatchExpr subst tme)
                in TRecordMatchExpr (List.map f fields)
              _ -> tme
      in (tme', replaceType subst ty)
        
    replaceStatement subst ts =
      case ts of
        TIfStatement te ts tsm ->
          TIfStatement (replaceExpr subst te) (replaceStatement subst ts)
                       (liftM (replaceStatement subst) tsm)
        TWhileStatement te ts ->
          TWhileStatement (replaceExpr subst te) (replaceStatement subst ts)
        TForStatement tme te ts ->
          TForStatement (replaceMatchExpr subst tme) (replaceExpr subst te)
                        (replaceStatement subst ts)
        TCompoundStatement tss ->
          TCompoundStatement (List.map (replaceStatement subst) tss)
        TAssignStatement tme_tlve te ->
          TAssignStatement (either (Left . replaceMatchExpr subst)
                                   (Right . replaceLValueExpr subst) tme_tlve)
                           (replaceExpr subst te)
        TMatchStatement te actions ->
          let f (tme, ts) = (replaceMatchExpr subst tme, replaceStatement subst ts)
          in TMatchStatement (replaceExpr subst te) (List.map f actions)
        TReturnStatement tem ->
          TReturnStatement (replaceExpr subst tem)
        TBreakStatement -> TBreakStatement
        TContinueStatement -> TContinueStatement
        TDeclStatement td -> TDeclStatement (replaceDecl subst td)

    replaceExpr subst (te, ty) =
      let te' =
            case te of
              TIntExpr n -> TIntExpr n
              TRealExpr d -> TRealExpr d
              TBoolExpr b -> TBoolExpr b
              TStringExpr s -> TStringExpr s
              TOrExpr te1 te2 ->
                TOrExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TAndExpr te1 te2 ->
                TAndExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TEqExpr te1 te2 ->
                TEqExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TNeqExpr te1 te2 ->
                TNeqExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TLtExpr te1 te2 ->
                TLtExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TGtExpr te1 te2 ->
                TGtExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TLeExpr te1 te2 ->
                TLeExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TGeExpr te1 te2 ->
                TGeExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TAddExpr te1 te2 ->
                TAddExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TSubExpr te1 te2 ->
                TSubExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TMultExpr te1 te2 ->
                TMultExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TDivExpr te1 te2 ->
                TDivExpr (replaceExpr subst te1) (replaceExpr subst te2)
              TUnaryMinusExpr te ->
                TUnaryMinusExpr (replaceExpr subst te)
              TBangExpr te ->
                TBangExpr (replaceExpr subst te)
              TCallExpr teFun teArg ->
                TCallExpr (replaceExpr subst teFun) (replaceExpr subst teArg)
              TListExpr tes ->
                TListExpr (List.map (replaceExpr subst) tes)
              TTupleExpr tes ->
                TTupleExpr (List.map (replaceExpr subst) tes)
              TSetExpr tes ->
                TSetExpr (List.map (replaceExpr subst) tes)
              TRecordExpr fields ->
                let f (s, te) = (s, replaceExpr subst te)
                in TRecordExpr (List.map f fields)
              TLValue tlve -> TLValue (replaceLValueExpr subst tlve)
              TLambdaExpr tmes ts ->
                TLambdaExpr (List.map (replaceMatchExpr subst) tmes)
                            (replaceStatement subst ts)
      in (te', replaceType subst ty)

    replaceLValueExpr subst (tlve, ty) =
      let tlve' =
            case tlve of
              TVarExpr s -> TVarExpr s
              TFieldAccessExpr tlve s ->
                TFieldAccessExpr (replaceLValueExpr subst tlve) s
              TArrayAccessExpr tlve te ->
                TArrayAccessExpr (replaceLValueExpr subst tlve)
                                 (replaceExpr subst te)
      in (tlve', replaceType subst ty)