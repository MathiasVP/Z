module TypeInfer where
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import TypedAst
import Unification
import Data.Maybe as Maybe
import Data.Ord

mkArrowType :: [Type] -> Type -> Type
mkArrowType types retTy = List.foldr Arrow retTy types

makeForall :: Substitution -> Type -> Type -> Type
makeForall subst (TypeVar u) ty =
  case follow subst (TypeVar u) of
    TypeVar _ -> Forall u ty
    _         -> ty
makeForall _ _ ty = ty

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

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc) 
    where
        f' ma k b = ma >>= \a -> f a k b

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
      let functionTy = List.foldr (makeForall subst') (mkArrowType types retTy') types
      let env'' = Map.insert name functionTy env'
      (statement', env''', argOrd'', subst'') <- inferStatement statement env'' argOrd' subst'
      (infRetTy, subst''') <- mergeReturns statement' env''' argOrd subst''
      let functionTy' = List.foldr (makeForall subst''') (mkArrowType types retTy') types
      let globEnv = Map.insert name functionTy' env
      case subtype infRetTy retTy' env'' argOrd'' subst''' of
        (True, subst) ->
          return (TFunDecl name tyArgs args' retTy' statement', globEnv, argOrd, subst)
        (False, _) -> do
          putStrLn $ "Error: Couldn't match expected return type '" ++ show retTy' ++
                     "' with actual type '" ++ show infRetTy ++ "'."
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
      (env', subst'') <- mergeEnv envExpr (Map.intersection envBody envExpr) argOrd subst'
      return (TIfStatement e' s' Nothing, env', argOrd', subst'')
      
    inferStatement (IfStatement e sThen (Just sElse)) env argOrd subst  = do
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
      (env', subst''') <- mergeEnv envMatchExpr (Map.intersection envBody envMatchExpr) argOrd subst'' 
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
          case subtype (typeOf arg') tDom env'' argOrd'' subst'''  of
            (True, subst'''') -> do
              return ((TCallExpr f' arg', tCod), env'', argOrd'', subst'''')
            (False, _) -> do
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
        Just (t, subst'') -> return (e', env', argOrd', subst'')

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
      let replace trace IntType = IntType
          replace trace BoolType = BoolType
          replace trace StringType = StringType
          replace trace RealType = RealType
          replace trace (Name s types) = Name s (List.map (replace trace) types)
          replace trace (Array ty) = Array ((replace trace) ty)
          replace trace (Tuple [ty]) = replace trace ty
          replace trace (Tuple types) = Tuple (List.map (replace trace) types)
          replace trace (Set ty) = Set (replace trace ty)
          replace trace (Record fields) =
            Record (List.map (\(s, ty) -> (s, replace trace ty)) fields)
          replace trace (Arrow tDom tCod) = Arrow (replace trace tDom) (replace trace tCod)
          replace trace (Union t1 t2) = Union (replace trace t1) (replace trace t2)
          replace trace (Forall u ty) =
            case replace trace (TypeVar u) of
              TypeVar u' -> Forall u' (replace trace ty)
              _ -> replace trace ty
          replace trace (TypeVar u)
            | Set.member u trace = TypeVar u
            | otherwise =
                case follow subst (TypeVar u) of
                  TypeVar u'
                    | u == u' -> TypeVar u
                    | otherwise -> replace (Set.insert u trace) (TypeVar u')
                  t -> replace (Set.insert u trace) t
          replace trace Error = Error
          replace trace (AllOf types) = AllOf (List.map (replace trace) types)
      in replace Set.empty ty

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
            where ty' = replaceType subst ty
          replace (TListMatchExpr tmes, ty) =
            (TListMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
            where ty' = replaceType subst ty
          replace (TSetMatchExpr tmes, ty) =
            (TSetMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
            where ty' = replaceType subst ty
          replace (TRecordMatchExpr fields, ty) =
            (TRecordMatchExpr (List.map f fields), ty')
            where f (s, tme) = (s, replaceMatchExpr subst tme)
                  ty' = replaceType subst ty
          replace (tme, ty) = (tme, ty')
            where ty' = replaceType subst ty
      in replace (tme, ty)
        
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
            where ty' = replaceType subst ty
          replace (TRealExpr d, ty) = (TRealExpr d, ty')
            where ty' = replaceType subst ty
          replace (TBoolExpr b, ty) = (TBoolExpr b, ty')
            where ty' = replaceType subst ty
          replace (TStringExpr s, ty) = (TStringExpr s, ty')
            where ty' = replaceType subst ty
          replace (TOrExpr te1 te2, ty) =
            (TOrExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TAndExpr te1 te2, ty) =
            (TAndExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TEqExpr te1 te2, ty) =
            (TEqExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TNeqExpr te1 te2, ty) =
            (TNeqExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TLtExpr te1 te2, ty) =
            (TLtExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TGtExpr te1 te2, ty) =
            (TGtExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TLeExpr te1 te2, ty) =
            (TLeExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TGeExpr te1 te2, ty) =
            (TGeExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TAddExpr te1 te2, ty) =
            (TAddExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TSubExpr te1 te2, ty) =
            (TSubExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TMultExpr te1 te2, ty) =
            (TMultExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TDivExpr te1 te2, ty) =
            (TDivExpr (replace te1) (replace te2), ty')
            where ty' = replaceType subst ty
          replace (TUnaryMinusExpr te, ty) =
            (TUnaryMinusExpr (replace te), ty')
            where ty' = replaceType subst ty
          replace (TBangExpr te, ty) =
            (TBangExpr (replace te), ty')
            where ty' = replaceType subst ty
          replace (TCallExpr teFun teArg, ty) =
            (TCallExpr (replace teFun) (replace teArg), ty')
            where ty' = replaceType subst ty
          replace (TListExpr tes, ty) =
            (TListExpr (List.map replace tes), ty')
            where ty' = replaceType subst ty
          replace (TTupleExpr tes, ty) =
            (TTupleExpr (List.map replace tes), ty')
            where ty' = replaceType subst ty
          replace (TSetExpr tes, ty) =
            (TSetExpr (List.map replace tes), ty')
            where ty' = replaceType subst ty
          replace (TRecordExpr fields, ty) =
            (TRecordExpr (List.map f fields), ty')
            where f (s, te) = (s, replace te)
                  ty' = replaceType subst ty
          replace (TLValue tlve, ty) =
            (TLValue (replaceLValueExpr subst tlve), ty')
            where ty' = replaceType subst ty
          replace (TLambdaExpr tmes ts, ty) =
            (TLambdaExpr (List.map (replaceMatchExpr subst) tmes)
                        (replaceStatement subst ts), ty')
            where ty' = replaceType subst ty
      in replace (te, ty)

    replaceLValueExpr subst (tlve, ty) =
      let replace (TVarExpr s, ty) = (TVarExpr s, ty')
            where ty' = replaceType subst ty
          replace (TFieldAccessExpr tlve s, ty) =
            (TFieldAccessExpr (replace tlve) s, ty')
            where ty' = replaceType subst ty
          replace (TArrayAccessExpr tlve te, ty) =
            (TArrayAccessExpr (replace tlve) (replaceExpr subst te), ty')
            where ty' = replaceType subst ty
      in replace (tlve, ty)