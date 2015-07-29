module TypeInfer where
import qualified Data.List as List
import qualified Data.Map as Map
import Control.Monad
import TypedAst
import Unification
import Data.Maybe as Maybe

intType, realType, boolType, stringType :: Type
intType = Name "Int" []
realType = Name "Real" []
boolType = Name "Bool" []
stringType = Name "String" []

mkIntType :: Substitution -> TypeGraph -> IO (Type, Substitution)
mkIntType subst gr = do
  u <- mkTypeVar
  (_, subst') <- unify u intType subst gr
  return (u, subst')
  
mkRealType :: Substitution -> TypeGraph -> IO (Type, Substitution)
mkRealType subst gr = do
  u <- mkTypeVar
  (_, subst') <- unify u realType subst gr
  return (u, subst')
  
mkArrowType :: [Type] -> Type -> Type
mkArrowType types retTy = List.foldr Arrow retTy types

mkArrayType :: Substitution -> Type -> TypeGraph -> IO (Type, Substitution)
mkArrayType subst ty gr = do
  u <- mkTypeVar
  (_, subst') <- unify u (Array ty) subst gr
  return (u, subst')

mkAllOfType :: Substitution -> [Type] -> TypeGraph -> IO (Type, Substitution)
mkAllOfType subst types gr = do
  u <- mkTypeVar
  (_, subst') <- unify u (AllOf types) subst gr
  return (u, subst')

normaliseFields fields =
  let cmp (name1, _) (name2, _) = compare name1 name2
  in List.sortBy cmp fields

equalRecordFields fields1 fields2 =
  let f fields = List.map fst (normaliseFields fields)
  in f fields1 == f fields2

exprOf = fst
typeOf = snd

mergeSubstitution :: Substitution -> Substitution -> TypeGraph -> IO Substitution
mergeSubstitution subst1 subst2 gr = foldlWithKeyM f subst1 subst2
  where f subst u ty =
          case Map.lookup u subst of
            Nothing -> return $ Map.insert u ty subst
            Just ty' -> do
              (_, subst') <- unify ty ty' subst gr
              return subst'

mergeEnv :: Env -> Env -> Substitution -> TypeGraph -> IO (Env, Substitution)
mergeEnv env1 env2 subst gr = foldlWithKeyM f (env1, subst) env2
  where f (env, subst) name ty =
          case Map.lookup name env of
            Nothing -> return $ (Map.insert name ty env, subst)
            Just ty' -> do
              (ty'', subst') <- unify ty ty' subst gr
              return (Map.insert name ty'' env, subst')

infer :: [Decl] -> IO ([TypedDecl], Env, Substitution)
infer decls = do
  (typeddecls, env, subst, _) <- inferList inferDecl (Map.fromList []) (Map.fromList []) initialAssumptions decls
  return $ (List.map (replaceDecl subst) typeddecls, Map.map (replaceType subst) env, subst)
  where
    inferList :: (a -> Env -> Substitution -> TypeGraph -> IO (b, Env, Substitution, TypeGraph)) ->
                  Env -> Substitution -> TypeGraph -> [a] -> IO ([b], Env, Substitution, TypeGraph)
    inferList inferer env subst gr list = 
      do (list', env', subst', gr') <- foldM f ([], env, subst, gr) list
         return (List.reverse list', env', subst', gr')
      where f (list', env, subst, gr) elem = do
            (elem', env', subst', gr') <- inferer elem env subst gr
            return (elem' : list', env', subst', gr')

    inferDecl :: Decl -> Env -> Substitution -> TypeGraph -> IO (TypedDecl, Env, Substitution, TypeGraph)
    inferDecl (TypeDecl name targs ty) env subst gr =
      return (TTypeDecl name targs ty, env, subst, translateTypeDecl name ty targs gr)

    inferDecl (FunDecl name tyArgs args retTy statement) env subst gr = do
      (args', env', subst', gr') <- inferList (inferMatchExpr Nothing) env subst gr args
      retTy' <- Maybe.fromMaybe mkTypeVar (liftM return retTy)
      let (_, types) = List.unzip args'
      let env'' = Map.insert name (mkArrowType types retTy') env'
      (statement', _, subst'', gr'') <- inferStatement statement env'' subst' gr'
      (retTy'', subst''') <- mergeReturns statement' subst'' gr''
      let globEnv = Map.insert name (mkArrowType types retTy'') env
      case unify' retTy' retTy'' subst''' gr'' of
        Just (retTy, subst) ->
          return (TFunDecl name tyArgs args' retTy statement', globEnv, subst, gr'')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected return type '" ++ show retTy ++
                     "' with actual type '" ++ show retTy' ++ "'."
          return (TFunDecl name tyArgs args' retTy' statement', globEnv, subst, gr)

    inferMatchExpr tm (TupleMatchExpr mes) env subst gr = do
      (mes', env', subst', gr') <-
        case tm of
          Just (Tuple ts) ->
            if List.length ts == List.length mes then
              let mesWithTypes = case tm of
                                  Just (Tuple ts) ->
                                    List.map inferMatchExpr (List.map Just ts)
                                  Nothing -> []
                  f (me, n) = (mesWithTypes !! n) me
              in inferList f env subst gr (List.zip mes [0..])
            else do putStrLn $ "Match error: Couldn't unify expression '" ++
                               show (TupleMatchExpr mes) ++ "' with type '" ++
                               show (Tuple ts) ++ "'."
                    return ([], env, subst, gr)
          Just (TypeVar u) -> do
            types <- replicateM (List.length mes) mkTypeVar
            (_, subst') <- unify (TypeVar u) (Tuple types) subst gr
            inferList (\(me, ty) -> inferMatchExpr (Just ty) me) env subst' gr (List.zip mes types)
          Nothing ->
            inferList (inferMatchExpr Nothing) env subst gr mes
      return ((TTupleMatchExpr mes', Tuple (List.map typeOf mes')), env', subst', gr')

    inferMatchExpr tm (ListMatchExpr mes) env subst gr = do
      (mes', env', subst', gr') <-
        case tm of
          Just (Array t) -> inferList (inferMatchExpr (Just t)) env subst gr mes
          Just (TypeVar u) -> do
            base <- mkTypeVar
            (_, subst') <- unify (TypeVar u) (Array base) subst gr
            inferList (inferMatchExpr (Just base)) env subst' gr mes
          Nothing -> inferList (inferMatchExpr Nothing) env subst gr mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') subst' gr'
      return ((TListMatchExpr mes', Array ty), env', subst'', gr')
      
    inferMatchExpr tm (SetMatchExpr mes) env subst gr = do
      (mes', env', subst', gr') <-
        case tm of
          Just (Set t) -> inferList (inferMatchExpr (Just t)) env subst gr mes
          Just (TypeVar u) -> do
            base <- mkTypeVar
            (_, subst') <- unify (TypeVar u) (Set base) subst gr
            inferList (inferMatchExpr (Just base)) env subst' gr mes
          Nothing -> inferList (inferMatchExpr Nothing) env subst gr mes
      (ty, subst'') <- unifyTypes (List.map typeOf mes') subst' gr'
      return ((TSetMatchExpr mes', Set ty), env', subst'', gr')
      
    inferMatchExpr tm (RecordMatchExpr fields) env subst gr = do
      (fields', env', subst', gr') <-
        case tm of
          Just (Record fields') ->
            if equalRecordFields fields fields' then
              let typesm = List.map (Just . typeOf) (normaliseFields fields')
                  f tm (name, me) env subst gr = do
                    (me', env', subst', gr') <- inferMatchExpr tm me env subst gr
                    return ((name, me'), env', subst', gr')
                  fs = List.map f typesm
                  inferField (entry, n) = (fs !! n) entry
              in inferList inferField env subst gr (List.zip (normaliseFields fields) [0..])
            else
              return ([], env, subst, gr)
          Just (TypeVar u) -> do
            types <- replicateM (List.length fields) mkTypeVar
            let fields' = List.zip (normaliseFields fields) types
            let mkField ((s, _), ty) = (s, ty)
            (_, subst') <- unify (TypeVar u) (Record (List.map mkField fields')) subst gr
            let f ((name, me), ty) env subst gr = do
                (me', env', subst', gr') <- inferMatchExpr (Just ty) me env subst gr
                return ((name, me'), env', subst', gr')
            inferList f env subst' gr fields'
          Nothing ->
            let f (name, me) env subst gr = do
                  (me', env, subst', gr') <- inferMatchExpr Nothing me env subst gr
                  return ((name, me'), Map.insert name (typeOf me') env, subst', gr')
            in inferList f env subst gr fields
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      return ((TRecordMatchExpr fields', Record recordTypes), env', subst', gr')

    inferMatchExpr tm (TypedMatchExpr me ty) env subst gr = do
      (me', env', subst', gr') <- inferMatchExpr tm me env subst gr
      case unify' ty (typeOf me') subst' gr' of
        Just (ty'', subst'') -> return (me', env', subst'', gr')
        Nothing -> do
          putStrLn $ "Error: Couldn't match expected type '" ++ show ty ++
                     "' with actual type '" ++ show (typeOf me') ++ "'."
          return (me', env, subst, gr)

    inferMatchExpr tm (VarMatch name) env subst gr =
      case tm of
        Just t ->
          return ((TVarMatch name, t), Map.insert name t env, subst, gr)
        Nothing -> do
          t <- mkTypeVar
          return ((TVarMatch name, t), Map.insert name t env, subst, gr)

    inferMatchExpr tm (IntMatchExpr n) env subst gr =
      return ((TIntMatchExpr n, intType), env, subst, gr)
      
    inferMatchExpr tm (StringMatchExpr s) env subst gr =
      return ((TStringMatchExpr s, stringType), env, subst, gr)
      
    inferMatchExpr tm (BoolMatchExpr b) env subst gr =
      return ((TBoolMatchExpr b, boolType), env, subst, gr)
    
    inferStatement :: Statement -> Env -> Substitution -> TypeGraph -> IO (TypedStatement, Env, Substitution, TypeGraph)
    inferStatement (IfStatement e s Nothing) env subst gr = do
      (e', envExpr, substExpr, gr') <- inferExpr e env subst gr
      (s', envBody, substBody, gr'') <- inferStatement s envExpr substExpr gr'
      subst' <- mergeSubstitution substExpr substBody gr''
      (env', subst'') <- mergeEnv envExpr envBody subst' gr''
      return (TIfStatement e' s' Nothing, env', subst'', gr'')
      
    inferStatement (IfStatement e sThen (Just sElse)) env subst gr = do
      (e', env', subst', gr') <- inferExpr e env subst gr
      (sThen', envThen, substThen, gr'') <- inferStatement sThen env' subst' gr'
      (sElse', envElse, substElse, gr''') <- inferStatement sElse env' subst' gr''
      subst' <- mergeSubstitution substThen substElse gr'''
      (env'', subst'') <- mergeEnv envThen envElse subst' gr'''
      return (TIfStatement e' sThen' (Just sElse'), env'', subst'', gr''')
      
    inferStatement (WhileStatement e s) env subst gr = do
      (e', envExpr, substExpr, gr') <- inferExpr e env subst gr
      (s', envBody, substBody, gr'') <- inferStatement s envExpr substExpr gr'
      subst' <- mergeSubstitution substExpr substBody gr''
      (env', subst'') <- mergeEnv envExpr envBody subst' gr''
      return (TWhileStatement e' s', env', subst'', gr'')

    inferStatement (ForStatement me e s) env subst gr = do
      (e', envExpr, substExpr, gr') <- inferExpr e env subst gr
      t <- mkTypeVar
      (t, subst') <-
        case unify' (typeOf e') (AllOf [Array t, Set t]) substExpr gr' of
          Just (_, subst') ->
            return (t, subst')
          Nothing -> do
            putStrLn $ "Error: Cannot iterate over expression of type '" ++
                       show (typeOf e') ++ "'."
            return (Error, substExpr)
      (me', envMatchExpr, substMatchExpr, gr'') <- inferMatchExpr (Just t) me envExpr subst' gr'
      (s', envBody, substBody, gr''') <- inferStatement s envMatchExpr substMatchExpr gr''
      subst'' <- mergeSubstitution substMatchExpr substBody gr'''
      (env', subst''') <- mergeEnv envMatchExpr envBody subst'' gr'''
      return (TForStatement me' e' s', env', subst''', gr''')
      
    inferStatement (CompoundStatement ss) env subst gr = do
      (ss', env', subst', gr') <- inferList inferStatement env subst gr ss
      return (TCompoundStatement ss', env', subst', gr')

    inferStatement (AssignStatement (Left me) e) env subst gr = do
      (e', envExpr, substExpr, gr') <- inferExpr e env subst gr
      (me', envMatchExpr, substMatchExpr, gr'') <-
        inferMatchExpr (Just $ typeOf e') me envExpr substExpr gr'
      return (TAssignStatement (Left me') e', envMatchExpr, substMatchExpr, gr'')

    inferStatement (AssignStatement (Right lve) e) env subst gr = do
      (e', env, substExpr, gr') <- inferExpr e env subst gr
      (lve', env', substLValueExpr, gr'') <- inferLValueExpr (Just $ typeOf e') lve env substExpr gr'
      return (TAssignStatement (Right lve') e', env', substLValueExpr, gr'')

    inferStatement (MatchStatement e mes) env subst gr = do
      (e', envExpr, substExpr, gr') <- inferExpr e env subst gr
      (mes', env', subst', gr'') <- inferList (f (typeOf e')) envExpr substExpr gr' mes
      return (TMatchStatement e' mes', env', subst', gr'')
      where f matchType (me, s) env subst gr = do
              (me', env', subst', gr') <- inferMatchExpr Nothing me env subst gr
              (ty, subst') <- unify matchType (typeOf me') subst' gr'
              let subst'' = case matchType of
                              TypeVar u -> Map.insert u ty subst'
              (s', env'', subst''', gr'') <- inferStatement s env' subst'' gr'
              return ((me', s'), env'', subst''', gr'')
                
    inferStatement (ReturnStatement e) env subst gr = do
      (e', env', subst', gr') <- inferExpr e env subst gr
      return (TReturnStatement e', env', subst', gr')
      
    inferStatement BreakStatement env subst gr =
      return (TBreakStatement, env, subst, gr)
      
    inferStatement ContinueStatement env subst gr =
      return (TContinueStatement, env, subst, gr)
      
    inferStatement (DeclStatement decl) env subst gr = do
      (decl', env', subst', gr') <- inferDecl decl env subst gr
      return (TDeclStatement decl', env', subst', gr')

    inferBinopExpr mkeExpr mkType env subst gr e1 e2 = do
      (e1', env1, subst1, gr1) <- inferExpr e1 env subst gr
      (e2', env2, subst2, gr2) <- inferExpr e2 env1 subst1 gr1
      (t, subst') <- mkType e1' e2' subst2 gr
      return ((mkeExpr e1' e2', t), env2, subst', gr2)
    
    mkMathOpType e1 e2 subst gr = do
      (expectedType, subst') <- mkAllOfType subst [intType, realType] gr
      case unify' (typeOf e1) expectedType subst' gr of
        Just (t1, subst1) ->
          case unify' (typeOf e2) expectedType subst1 gr of
            Just (t2, subst2) ->
              case unify' t1 t2 subst2 gr of
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
          
    mkLogicalOpType e1 e2 subst gr =
      case unify' (typeOf e1) boolType subst gr of
        Just (t1, subst1) ->
          case unify' (typeOf e2) boolType subst1 gr of
            Just (t2, subst2) ->
              case unify' t1 t2 subst2 gr of
                Just (_, subst') ->
                  return (boolType, subst')
                Nothing -> do
                  putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                             "' with type '" ++ show (typeOf e2) ++ "'."
                  return (Error, subst)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++
                         "' with type '" ++ show boolType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show boolType ++ "'."
          return (Error, subst)

    mkEqOpType e1 e2 subst gr =
      case unify' (typeOf e1) (typeOf e2) subst gr of
        Just (_, subst') ->
          return (boolType, subst')
        Nothing -> do
          putStrLn $ "Cannot unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show (typeOf e2) ++ "'."
          return (Error, subst)

    mkRelOpType e1 e2 subst gr = do
      (expectedType, subst') <- mkAllOfType subst [intType, realType] gr
      case unify' (typeOf e1) expectedType subst gr of
        Just (_, subst1) -> do
          case unify' (typeOf e2) expectedType subst1 gr of
            Just (_, subst2) -> do
              return (boolType, subst2)
            Nothing -> do
              putStrLn $ "Cannot unify type '" ++ show (typeOf e2) ++
                         "' with type '" ++ show expectedType ++ "'."
              return (Error, subst)
        Nothing -> do
          putStrLn $ "Can not unify type '" ++ show (typeOf e1) ++
                     "' with type '" ++ show expectedType ++ "'."
          return (Error, subst)
      
    inferExpr (IntExpr n) env subst gr =
      return ((TIntExpr n, intType), env, subst, gr)

    inferExpr (RealExpr n) env subst gr =
      return ((TRealExpr n, realType), env, subst, gr)
      
    inferExpr (BoolExpr b) env subst gr =
      return ((TBoolExpr b, boolType), env, subst, gr)
      
    inferExpr (StringExpr s) env subst gr =
      return ((TStringExpr s, stringType), env, subst, gr)

    inferExpr (OrExpr e1 e2) env subst gr =
      inferBinopExpr TOrExpr mkLogicalOpType env subst gr e1 e2

    inferExpr (AndExpr e1 e2) env subst gr =
      inferBinopExpr TAndExpr mkLogicalOpType env subst gr e1 e2

    inferExpr (EqExpr e1 e2) env subst gr =
      inferBinopExpr TEqExpr mkEqOpType env subst gr e1 e2
      
    inferExpr (NeqExpr e1 e2) env subst gr =
      inferBinopExpr TNeqExpr mkEqOpType env subst gr e1 e2
      
    inferExpr (LtExpr e1 e2) env subst gr =
      inferBinopExpr TLtExpr mkRelOpType env subst gr e1 e2
      
    inferExpr (GtExpr e1 e2) env subst gr =
      inferBinopExpr TGtExpr mkRelOpType env subst gr e1 e2
      
    inferExpr (LeExpr e1 e2) env subst gr =
      inferBinopExpr TLeExpr mkRelOpType env subst gr e1 e2

    inferExpr (GeExpr e1 e2) env subst gr =
      inferBinopExpr TGeExpr mkRelOpType env subst gr e1 e2
      
    inferExpr (AddExpr e1 e2) env subst gr =
      inferBinopExpr TAddExpr mkMathOpType env subst gr e1 e2
      
    inferExpr (SubExpr e1 e2) env subst gr =
      inferBinopExpr TSubExpr mkMathOpType env subst gr e1 e2
      
    inferExpr (MultExpr e1 e2) env subst gr =
      inferBinopExpr TMultExpr mkMathOpType env subst gr e1 e2
      
    inferExpr (DivExpr e1 e2) env subst gr =
      inferBinopExpr TDivExpr mkMathOpType env subst gr e1 e2

    inferExpr (UnaryMinusExpr e) env subst gr = do
      (e', env', subst', gr') <- inferExpr e env subst gr
      case unify' (typeOf e') (AllOf [intType, realType]) subst' gr' of
        Just (t, subst'') -> return ((TUnaryMinusExpr e', t), env', subst'', gr')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Int' or 'Real' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TUnaryMinusExpr e', Error), env, subst, gr)

    inferExpr (BangExpr e) env subst gr = do
      (e', env', subst', gr') <- inferExpr e env subst gr
      case unify' (typeOf e') boolType subst' gr' of
        Just (t, subst'') -> return ((TBangExpr e', boolType), env', subst'', gr')
        Nothing -> do putStrLn $ "Couldn't match expected type 'Bool' with actual type '" ++
                                 show (typeOf e') ++ "'."
                      return ((TBangExpr e', boolType), env', subst', gr)

    inferExpr (CallExpr f arg) env subst gr = do
      (f', env', subst', gr') <- inferExpr f env subst gr
      (arg', env'', subst'', gr'') <- inferExpr arg env' subst' gr'
      tDom <- mkTypeVar
      tCod <- mkTypeVar
      case unify' (typeOf f') (Arrow tDom tCod) subst'' gr'' of
        Just(t, subst''') -> do
          case unify' (typeOf arg') tDom subst''' gr'' of
            Just _ -> --- TODO: We *really* shouldn't ignore this substitution
              return ((TCallExpr f' arg', tCod), env'', subst''', gr'')
            Nothing -> do
              putStrLn $ "Couldn't match expected type '" ++ show tDom ++
                         "' with actual type '" ++ show (typeOf arg') ++ "'."
              return ((TCallExpr f' arg', Error), env, subst, gr)
        Nothing -> do
            putStrLn $ "Couldn't match expected type '" ++ show (Arrow tDom tCod) ++
                       "' with actual type '" ++ show (typeOf f') ++ "'."
            return ((TCallExpr f' arg', Error), env, subst, gr)

    inferExpr (TypeConstrainedExpr e ty) env subst gr = do
      (e', env', subst', gr') <- inferExpr e env subst gr
      case unify' (typeOf e') ty subst' gr' of
        Nothing          -> do putStrLn $ "Couldn't match expected type '" ++ show ty ++
                                          "' with actual type '" ++ show (typeOf e') ++ "'."
                               return (e', env', subst', gr')
        Just (t, subst') -> return (e', env', subst', gr')
      
    inferExpr (ListExpr es) env subst gr = do
      (es', env', subst', gr') <- inferList inferExpr env subst gr es
      let (_, types) = List.unzip es'
      (ty, subst'') <- unifyTypes types subst' gr'
      return ((TListExpr es', Array ty), env', subst'', gr')
      
    inferExpr (TupleExpr es) env subst gr = do
      (es', env', subst', gr') <- inferList inferExpr env subst gr es
      let (_, types) = List.unzip es'
      return ((TTupleExpr es', Tuple types), env', subst', gr')
      
    inferExpr (SetExpr es) env subst gr = do
      (es', env', subst', gr') <- inferList inferExpr env subst gr es
      let (_, types) = List.unzip es'
      (ty, subst'') <- unifyTypes types subst' gr'
      return ((TSetExpr es', Set ty), env', subst'', gr')

    inferExpr (RecordExpr fields) env subst gr = do
      let f (name, e) env subst gr = do
            (e', env', subst', gr') <- inferExpr e env subst gr
            return ((name, e'), env', subst', gr')
      (fields', env', subst', gr') <- inferList f env subst gr fields
      let recordTypes = List.map (\(name, (_, t)) -> (name, t)) fields'
      return ((TRecordExpr fields', Record recordTypes), env', subst', gr')

    inferExpr (LValue lve) env subst gr = do
      (lve', env', subst', gr') <- inferLValueExpr Nothing lve env subst gr
      return ((TLValue lve', typeOf lve'), env', subst', gr')

    inferExpr (LambdaExpr mes s) env subst gr = do
      (mes', env', subst', gr') <- inferList (inferMatchExpr Nothing) env subst gr mes
      (s', env'', subst'', gr'') <- inferStatement s env' subst' gr'
      let (_, types) = List.unzip mes'
      (ty, subst''') <- mergeReturns s' subst'' gr''
      return ((TLambdaExpr mes' s', mkArrowType types ty), env'', subst''', gr'')

    mergeReturns :: TypedStatement -> Substitution -> TypeGraph -> IO (Type, Substitution)
    mergeReturns s subst gr =
      let types = returns s
      in unifyTypes types subst gr
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

    inferLValueExpr tm (VarExpr name) env subst gr =
      case tm of
        Just t -> -- Writing to variable
          return ((TVarExpr name, t), Map.insert name t env, subst, gr)
        Nothing -> -- Reading from variable
          case Map.lookup name env of
            Just ty -> do
              return ((TVarExpr name, find subst ty), env, subst, gr)
            Nothing -> do
              putStrLn $ "Not in scope: " ++ name
              return ((TVarExpr name, Error), env, subst, gr)
      where find subst (TypeVar u) =
              case Map.lookup u subst of
                Just ty -> find subst ty
                Nothing -> (TypeVar u)
            find subst ty = ty

    inferLValueExpr _ (FieldAccessExpr lve field) env subst gr = do
      (lve', env', subst', gr') <- inferLValueExpr Nothing lve env subst gr
      case typeOf lve' of -- TODO: Replace with a unification
        Record fields ->
          case List.find ((field ==) . fst) fields of
            Just (_, t) ->
              return ((TFieldAccessExpr lve' field, t), env', subst', gr')
            Nothing -> do
              putStrLn $ field ++ " is not a field of type '" ++ show (typeOf lve') ++ "'"
              return ((TFieldAccessExpr lve' field, Error), env, subst, gr)
        t -> do
          putStrLn $ "Couldn't match expected record type with actual type '" ++
                     show t ++ "'"
          return ((TFieldAccessExpr lve' field, Error), env, subst, gr)

    inferLValueExpr _ (ArrayAccessExpr lve e) env subst gr = do
      (lve', env', subst', gr') <- inferLValueExpr Nothing lve env subst gr
      (e', env'', subst'', gr'') <- inferExpr e env' subst' gr'
      case (typeOf lve', typeOf e') of --TODO: Replace with unification
        (Array arrayTy, Name "Int" []) ->
          return ((TArrayAccessExpr lve' e', arrayTy), env'', subst'', gr'')
        (Array _, t) -> do
          putStrLn $ "Couldn't match expected array type 'int' with actual type '" ++
                     show t ++ "'."
          return ((TArrayAccessExpr lve' e', t), env'', subst'', gr)
        (t, _) -> do
          putStrLn $ "Couldn't match expected array type with with actual type '" ++
                     show t ++ "'."
          return ((TArrayAccessExpr lve' e', t), env'', subst, gr)
  
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