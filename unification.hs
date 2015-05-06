module Unification where
import qualified Data.Unique as U
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad
import TypedAst

type Substitution = Map.Map U.Unique Type
type Env = Map.Map String Type

mkTypeVar :: IO Type  
mkTypeVar = do
  u <- U.newUnique
  return (TypeVar u)

unify :: Type -> Type -> Substitution -> IO (Type, Substitution)
unify (Name s1 types1) (Name s2 types2) subst =
  if s1 == s2 && List.length types1 == List.length types2 then do
    (types, subst') <- unifyPairwise types1 types2 subst
    return (Name s1 types, subst')
  else return (Union (Name s1 types1) (Name s2 types2), subst) 
unify (Array t1) (Array t2) subst = do
  (t, subst') <- unify t1 t2 subst
  return (Array t, subst')
unify (Tuple [t1]) (Tuple [t2]) subst = do
  (t, subst') <- unify t1 t2 subst
  return (Tuple [t], subst')
unify (Tuple [t1]) t2 subst = do
  (t, subst') <- unify t1 t2 subst
  return (t, subst')
unify t1 (Tuple [t2]) subst = do
  (t, subst') <- unify t1 t2 subst
  return (t, subst')
unify (Tuple types1) (Tuple types2) subst =
  if List.length types1 == List.length types2 then do
    (types, subst') <- unifyPairwise types1 types2 subst
    return (Tuple types, subst')
  else return (Union (Tuple types1) (Tuple types2), subst)
unify (Set t1) (Set t2) subst = do
  (t, subst') <- unify t1 t2 subst
  return (Set t, subst')
unify (Record fields1) (Record fields2) subst = do
  (types, subst') <- unifyPairwise types1 types2 subst
  let fields = List.zip names1 types
  if names1 == names2 then
    return (Record fields, subst')
  else return (Union (Record fields1) (Record fields2), subst)
  where cmp (name1, _) (name2, _) = compare name1 name2
        fields1' = List.sortBy cmp fields1
        fields2' = List.sortBy cmp fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst = do
  (tyDom, subst') <- unify tyDom1 tyDom2 subst
  (tyCod, subst'') <- unify tyCod1 tyCod2 subst'
  return (Arrow tyDom tyCod, subst'')
unify (Union t1 t2) (Union t3 t4) subst = do
  (t13, subst') <- unify t1 t3 subst
  (t24, subst'') <- unify t2 t4 subst'
  return (Union t13 t24, subst'')
unify (TypeVar u) (TypeVar u') subst =
  if u == u' then
    return (TypeVar u, subst)
  else return (TypeVar u, Map.insert u (TypeVar u') subst)
unify (TypeVar u) t subst =
  case Map.lookup u subst of
    Nothing -> return (t, Map.insert u t subst)
    Just t' -> do
      (t'', subst') <- unify t t' subst
      return (t'', Map.insert u t'' subst')
unify t (TypeVar u) subst = unify (TypeVar u) t subst
unify (AllOf ts1) (AllOf ts2) subst =
  return (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify (AllOf ts) t subst =
  if Set.member t (Set.fromList ts) then
    return (t, subst)
  else
    return (Union (AllOf ts) t, subst)
unify t (AllOf ts) subst = unify (AllOf ts) t subst
unify t1 t2 subst = return (Union t1 t2, subst)

unifyTypes :: [Type] -> Substitution -> IO (Type, Substitution)
unifyTypes types subst = do
  t <- mkTypeVar
  (ty, subst') <- foldM f (t, subst) types
  return (ty, subst')
  where f (ty, subst) ty' = unify ty ty' subst
  
unifyPairwise :: [Type] -> [Type] -> Substitution -> IO ([Type], Substitution)
unifyPairwise types1 types2 subst = do
  let types = List.zip types1 types2
  let f (types, subst) (t1, t2) = do (t, subst') <- unify t1 t2 subst 
                                     return (t : types, subst')
  (types', subst') <- foldM f ([], subst) types
  return (List.reverse types', subst')

unify' :: Type -> Type -> Substitution -> Maybe (Type, Substitution)
unify' (Name s1 types1) (Name s2 types2) subst =
  if s1 == s2 then
    case unifyPairwise' types1 types2 subst of
      Just (types, subst') -> Just (Name s1 types, subst')
      Nothing -> Nothing
  else Nothing
unify' (Array t1) (Array t2) subst =
  case unify' t1 t2 subst of
    Just (t, subst') -> Just (Array t, subst')
    Nothing -> Nothing
unify' (Tuple [t1]) (Tuple [t2]) subst =
  unify' t1 t2 subst
unify' (Tuple [t1]) t2 subst =
  unify' t1 t2 subst
unify' t1 (Tuple [t2]) subst =
  unify' t1 t2 subst
unify' (Tuple types1) (Tuple types2) subst =
  case unifyPairwise' types1 types2 subst of
    Just (types, subst') -> Just (Tuple types, subst')
    Nothing -> Nothing
unify' (Set t1) (Set t2) subst =
  case unify' t1 t2 subst of
    Just (t, subst') -> Just (Set t, subst')
    Nothing -> Nothing
unify' (Record fields1) (Record fields2) subst =
  if names1 == names2 then
    case unifyPairwise' types1 types2 subst of
      Just (types, subst') ->
        let fields = List.zip names1 types
        in Just (Record fields, subst')
      Nothing -> Nothing
  else Nothing
  where cmp (name1, _) (name2, _) = compare name1 name2
        fields1' = List.sortBy cmp fields1
        fields2' = List.sortBy cmp fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify' (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst =
  case unify' tyDom1 tyDom2 subst of
    Just (tyDom, subst') ->
      case unify' tyCod1 tyCod2 subst' of
        Just (tyCod, subst'') -> Just (Arrow tyDom tyCod, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' (Union t1 t2) (Union t3 t4) subst =
  case unify' t1 t3 subst of
    Just (t13, subst') ->
      case unify' t2 t4 subst' of
        Just (t24, subst'') -> Just (Union t13 t24, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' (TypeVar u) (TypeVar u') subst =
  if u == u' then
    Just (TypeVar u, subst)
  else Just (TypeVar u, Map.insert u (TypeVar u') subst)
unify' (TypeVar u) t subst =
  case Map.lookup u subst of
    Nothing -> Just (t, Map.insert u t subst)
    Just t' ->
      case unify' t t' subst of
        Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
        Nothing -> Nothing
unify' t (TypeVar u) subst = unify' (TypeVar u) t subst
unify' (AllOf ts1) (AllOf ts2) subst =
  Just (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify' (AllOf ts) t subst =
  if Set.member t (Set.fromList ts) then
    Just (t, subst)
  else
    Nothing
unify' t (AllOf ts) subst = unify' (AllOf ts) t subst
unify' t1 t2 subst = Nothing

unifyPairwise' :: [Type] -> [Type] -> Substitution -> Maybe ([Type], Substitution)
unifyPairwise' types1 types2 subst =
  if List.length types1 /= List.length types2 then
    Nothing
  else List.foldr f (Just ([], subst)) (List.zip types1 types2)
  where f (t1, t2) (Just (types, subst)) =
            case unify' t1 t2 subst of
              Just (t, subst') -> (Just (t : types, subst'))
              Nothing -> Nothing
        f _ Nothing = Nothing