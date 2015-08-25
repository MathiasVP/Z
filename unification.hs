module Unification where
import qualified Data.Unique as U
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map ((!))
import Data.Map (Map)
import Data.Maybe as Maybe
import Control.Monad
import Data.Ord
import Ast
import TypedAst

type Substitution = Map U.Unique Type
type Env = Map String Type

mkTypeVar :: IO Type  
mkTypeVar = U.newUnique >>=
              return . TypeVar

unify :: Type -> Type -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
unify (TypeVar u) (TypeVar u') env argOrd subst =
  case (follow subst (TypeVar u), follow subst (TypeVar u')) of
    (TypeVar u, TypeVar u') -> return (TypeVar u, Map.insert u (TypeVar u') subst)
    (TypeVar u, t) -> return (t, Map.insert u t subst)
    (t, TypeVar u') -> return (t, Map.insert u' t subst)
    (t, t') -> unify t t' env argOrd subst 
unify (TypeVar u) t env argOrd subst =
  case follow subst (TypeVar u) of
    TypeVar u -> return (t, Map.insert u t subst)
    t'        -> do (t'', subst') <- unify t t' env argOrd subst 
                    return (t'', Map.insert u t'' subst')
unify t (TypeVar u) env argOrd subst = unify (TypeVar u) t env argOrd subst
unify t1@(Name s1 types1) t2@(Name s2 types2) env argOrd subst =
  case subtype' env subst argOrd (env ! s1, bind1) (env ! s2, bind2) of
    (True, subst') -> return (t1, subst') --TODO: Or t2?
    (False, _) -> return (Union t1 t2, subst)
  where bind1 = makeBindings argOrd s1 types1
        bind2 = makeBindings argOrd s2 types2
unify t1@(Name s types) t2 env argOrd subst =
  case subtype' env subst argOrd (env ! s, bind) (t2, Map.empty) of
    (True, subst') -> return (t1, subst') --TODO: Or t2?
    (False, _) -> return (Union t1 t2, subst)
  where bind = makeBindings argOrd s types
unify t1 t2@(Name s types) env argOrd subst =
  case subtype' env subst argOrd (t1, Map.empty) (env ! s, bind) of
    (True, subst') -> return (t1, subst') --TODO: Or t2?
    (False, _) -> return (Union t1 t2, subst)
  where bind = makeBindings argOrd s types
unify (Array t1) (Array t2) env argOrd subst = do
  (t, subst') <- unify t1 t2 env argOrd subst 
  return (Array t, subst')
unify (Tuple [t1]) (Tuple [t2]) env argOrd subst = do
  (t, subst') <- unify t1 t2 env argOrd subst 
  return (Tuple [t], subst')
unify (Tuple [t1]) t2 env argOrd subst = do
  (t, subst') <- unify t1 t2 env argOrd subst 
  return (t, subst')
unify t1 (Tuple [t2]) env argOrd subst = do
  (t, subst') <- unify t1 t2 env argOrd subst 
  return (t, subst')
unify (Tuple types1) (Tuple types2) env argOrd subst =
  if List.length types1 == List.length types2 then do
    (types, subst') <- unifyPairwise types1 types2 env argOrd subst 
    return (Tuple types, subst')
  else return (Union (Tuple types1) (Tuple types2), subst)
unify (Set t1) (Set t2) env argOrd subst = do
  (t, subst') <- unify t1 t2 env argOrd subst 
  return (Set t, subst')
unify (Record fields1) (Record fields2) env argOrd subst = do
  (types, subst') <- unifyPairwise types1 types2 env argOrd subst
  let fields = List.zip names1 types
  if names1 == names2 then
    return (Record fields, subst')
  else return (Union (Record fields1) (Record fields2), subst)
  where fields1' = List.sortBy (comparing fst) fields1
        fields2' = List.sortBy (comparing fst) fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) env argOrd subst = do
  (tyDom, subst') <- unify tyDom1 tyDom2 env argOrd subst 
  (tyCod, subst'') <- unify tyCod1 tyCod2 env argOrd subst' 
  return (Arrow tyDom tyCod, subst'')
unify (Union t1 t2) (Union t3 t4) env argOrd subst = do
  (t13, subst') <- unify t1 t3 env argOrd subst 
  (t24, subst'') <- unify t2 t4 env argOrd subst' 
  return (Union t13 t24, subst'')
unify (AllOf ts1) (AllOf ts2) env argOrd subst =
  return (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify (AllOf ts) t env argOrd subst =
  if Set.member t (Set.fromList ts) then
    return (t, subst)
  else
    return (Union (AllOf ts) t, subst)
unify t (AllOf ts) env argOrd subst = unify (AllOf ts) t env argOrd subst 
unify t1 t2 env argOrd subst = return (Union t1 t2, subst)

unifyTypes :: [Type] -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
unifyTypes types env argOrd subst = do
  t <- mkTypeVar
  foldM f (t, subst) types
  where f (ty, subst) ty' =
          unify ty ty' env argOrd subst 

unifyPairwise :: [Type] -> [Type] -> Env -> ArgOrd -> Substitution -> IO ([Type], Substitution)
unifyPairwise types1 types2 env argOrd subst = do
  let types = List.zip types1 types2
  let f (types, subst) (t1, t2) = do (t, subst') <- unify t1 t2 env argOrd subst 
                                     return (t : types, subst')
  (types', subst') <- foldM f ([], subst) types
  return (List.reverse types', subst')

follow :: Substitution -> Type -> Type
follow subst (TypeVar u) =
  case Map.lookup u subst of
    Nothing             -> TypeVar u
    Just (TypeVar u')   -> if u == u' then TypeVar u'
                           else follow subst (TypeVar u')
    Just (Name s types) -> Name s types
    Just (Array ty) -> Array (follow subst ty)
    Just (Tuple types) -> Tuple (List.map (follow subst) types)
    Just (Set ty) -> Set (follow subst ty)
    Just (Record fields) -> let f (s, ty) = (s, follow subst ty)
                            in Record (List.map f fields)
    Just (Arrow tDom tCod) -> Arrow (follow subst tDom) (follow subst tCod)
    Just (Union t1 t2) -> Union (follow subst t1) (follow subst t2)
    Just Error -> Error
    Just (AllOf types) -> AllOf (List.map (follow subst) types)
follow subst t = t

makeBindings :: ArgOrd -> String -> [Type] -> Bindings
makeBindings argOrd s types = Map.fromList $ List.zip (Map.elems (argOrd ! s)) types


unify' :: Type -> Type -> Env -> ArgOrd -> Substitution -> Maybe (Type, Substitution)
unify' (TypeVar u) (TypeVar u') env argOrd subst =
  case (follow subst (TypeVar u), follow subst (TypeVar u')) of
    (TypeVar u, TypeVar u') -> Just (TypeVar u, Map.insert u (TypeVar u') subst)
    (TypeVar u, t) -> Just (t, Map.insert u t subst)
    (t, TypeVar u') -> Just (t, Map.insert u' t subst)
    (t, t') -> unify' t t' env argOrd subst
unify' (TypeVar u) t env argOrd subst =
  case follow subst (TypeVar u) of
    TypeVar u -> Just (t, Map.insert u t subst)
    t'        -> case unify' t' t env argOrd subst of
                  Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                  Nothing            -> Nothing
unify' t (TypeVar u) env argOrd subst =
  case follow subst (TypeVar u) of
    TypeVar u -> Just (t, Map.insert u t subst)
    t'        -> case unify' t t' env argOrd subst of
                  Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                  Nothing            -> Nothing
unify' t1@(Name s1 types1) (Name s2 types2) env argOrd subst =
  case subtype' env subst argOrd (env ! s1, bind1) (env ! s2, bind2) of
    (True, subst') -> Just (t1, subst') --TODO: Or t2?
    (False, _) -> Nothing
  where bind1 = makeBindings argOrd s1 types1
        bind2 = makeBindings argOrd s2 types2
unify' t1@(Name s types) t2 env argOrd subst =
  case subtype' env subst argOrd (env ! s, bind) (t2, Map.empty) of
    (True, subst') -> Just (t1, subst') --TODO: Or t2?
    (False, _) -> Nothing
  where bind = makeBindings argOrd s types
unify' t1 t2@(Name s types) env argOrd subst =
  case subtype' env subst argOrd (t1, Map.empty) (env ! s, bind) of
    (True, subst') -> Just (t1, subst') --TODO: Or t2?
    (False, _) -> Nothing
  where bind = makeBindings argOrd s types
unify' (Array t1) (Array t2) env argOrd subst =
  case unify' t1 t2 env argOrd subst of
    Just (t, subst') -> Just (Array t, subst')
    Nothing -> Nothing
unify' (Tuple [t1]) (Tuple [t2]) env argOrd subst =
  unify' t1 t2 env argOrd subst
unify' (Tuple [t1]) t2 env argOrd subst =
  unify' t1 t2 env argOrd subst
unify' t1 (Tuple [t2]) env argOrd subst =
  unify' t1 t2 env argOrd subst
unify' (Tuple types1) (Tuple types2) env argOrd subst =
  case unifyPairwise' types1 types2 env argOrd subst of
    Just (types, subst') -> Just (Tuple types, subst')
    Nothing -> Nothing
unify' (Set t1) (Set t2) env argOrd subst =
  case unify' t1 t2 env argOrd subst of
    Just (t, subst') -> Just (Set t, subst')
    Nothing -> Nothing
unify' (Record fields1) (Record fields2) env argOrd subst =
  if names1 == names2 then
    case unifyPairwise' types1 types2 env argOrd subst of
      Just (types, subst') ->
        let fields = List.zip names1 types
        in Just (Record fields, subst')
      Nothing -> Nothing
  else Nothing
  where fields1' = List.sortBy (comparing fst) fields1
        fields2' = List.sortBy (comparing fst) fields2
        (names1, types1) = List.unzip fields1'
        (names2, types2) = List.unzip fields2'
unify' (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) env argOrd subst =
  case unify' tyDom2 tyDom1 env argOrd subst of
    Just (tyDom, subst') ->
      case unify' tyCod1 tyCod2 env argOrd subst' of
        Just (tyCod, subst'') -> Just (Arrow tyDom tyCod, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' (Union t1 t2) (Union t3 t4) env argOrd subst =
  case unify' t1 t3 env argOrd subst of
    Just (t13, subst') ->
      case unify' t2 t4 env argOrd subst' of
        Just (t24, subst'') -> Just (Union t13 t24, subst'')
        Nothing -> Nothing
    Nothing -> Nothing
unify' ty (Union t1 t2) env argOrd subst =
  case unify' ty t1 env argOrd subst of
    Just (t, subst') -> Just (t, subst')
    Nothing -> unify' ty t2 env argOrd subst
unify' (Union t1 t2) ty env argOrd subst =
  case unify' t1 ty env argOrd subst of
    Just (t, subst') -> Just (t, subst')
    Nothing -> unify' t2 ty env argOrd subst
unify' (AllOf ts1) (AllOf ts2) env argOrd subst =
  Just (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
unify' (AllOf ts) t env argOrd subst =
  if Set.member t (Set.fromList ts) then
    Just (t, subst)
  else Nothing
unify' t (AllOf ts) env argOrd subst = unify' (AllOf ts) t env argOrd subst
unify' t1 t2 env argOrd subst = Nothing

foldlWithKeyM :: Monad m => (a -> k -> b -> m a) -> a -> Map k b -> m a
foldlWithKeyM f acc = Map.foldlWithKey f' (return acc) 
    where
        f' ma k b = ma >>= \a -> f a k b

unifyPairwise' :: [Type] -> [Type] -> Env -> ArgOrd -> Substitution -> Maybe ([Type], Substitution)
unifyPairwise' types1 types2 env argOrd subst =
  if List.length types1 /= List.length types2 then
    Nothing
  else List.foldr f (Just ([], subst)) (List.zip types1 types2)
  where f (t1, t2) (Just (types, subst)) =
            case unify' t1 t2 env argOrd subst of
              Just (t, subst') -> (Just (t : types, subst'))
              Nothing -> Nothing
        f _ Nothing = Nothing
        
-------------------------------------------------------
-- Subtype relation <:
-------------------------------------------------------
data Variance
  = Positive
  | Negative
  | Top
  | Bottom

type Assumptions = Map (String, String) ([Type], [Type])
type Bindings = Map String Type
type ArgOrd = Map String (Map Int String)

lub :: Variance -> Variance -> Variance
lub Positive Positive = Positive
lub Negative Negative = Negative
lub v Bottom = v
lub Bottom v = v
lub _ _ = Top

lub' :: [Variance] -> Variance
lub' = List.foldr lub Bottom

invert :: Variance -> Variance
invert Positive = Negative
invert Negative = Positive
invert v = v

instansiate :: String -> Type -> Type -> Type
instansiate name ty t =
  let inst (Name s [])
        | s == name = ty
        | otherwise = Name s []
      inst (Name s tys) = Name s (List.map inst tys)
      inst (Arrow tDom tCod) = Arrow (inst tDom) (inst tCod)
      inst (Union t1 t2) = Union (inst t1) (inst t2)
      inst (Tuple tys) = Tuple (List.map inst tys)
      inst (Record fields) = Record (List.map (\(s, ty) -> (s, inst ty)) fields)
      inst (Array ty) = Array (inst ty)
      inst (Set ty) = Set (inst ty)
      inst (TypeVar u) = TypeVar u
      inst Error = Error
      inst IntType = IntType
      inst RealType = RealType
      inst BoolType = BoolType
      inst StringType = StringType
      inst (AllOf tys) = AllOf (List.map inst tys)
  in inst t

instansiate' :: Type -> [(String, Type)] -> Type
instansiate' = List.foldr (uncurry instansiate)

variance :: Env -> ArgOrd -> Type -> String -> Variance
variance env argOrd t s =
  let var trace v (Name s' tys)
        | Set.member s' trace = v
        | otherwise =
          case Map.lookup s' env of
            Just ty ->
              let order = argOrd ! s'
                  names = List.map (order !) [0..]
                  ty' = instansiate' ty (List.zip names tys)
              in var (Set.insert s' trace) v ty'
            Nothing
              | s == s'   -> lub v Positive
              | otherwise -> v
      var trace v (Arrow t1 t2) =
        lub (invert (var trace v t1)) (var trace v t2)
      var trace v (Union t1 t2) = lub (var trace v t1) (var trace v t2)
      var trace v (Tuple ts) = lub' (List.map (var trace v) ts)
      var trace v (Record fields) = lub' (List.map (var trace v . snd) fields)
      var trace v (Array ty) = var trace v ty
      var trace v (Set ty) = var trace v ty
      var trace v (AllOf ts) = lub' (List.map (var trace v) ts)
      var trace v _ = v
  in var Set.empty Bottom t

subtype' :: Env -> Substitution -> ArgOrd -> (Type, Bindings) -> (Type, Bindings) -> (Bool, Substitution)
subtype' env subst argOrd (t1, bind1) (t2, bind2) =
  let
    lookup bind env s = Map.findWithDefault (bind ! s) s env

    sub assum subst (Name s1 tys1) (Name s2 tys2) =
      case Map.lookup (s1, s2) assum of
        Just (tys1', tys2') ->
          let ty1 = lookup bind1 env s1
              ty2 = lookup bind2 env s2
              vars1 = List.map (variance env argOrd ty1) (Map.keys bind1)
              vars2 = List.map (variance env argOrd ty2) (Map.keys bind2)
              (b1, subst') = List.foldr f (True, subst) (List.zip3 tys1 tys1' vars1)
          in List.foldr f (b1, subst') (List.zip3 tys1 tys1' vars1)
        Nothing
          | s1 == s2 && Map.notMember s1 bind1 && Map.notMember s2 bind2 ->
            let ty = env ! s1
                vars = List.map (variance env argOrd ty) (Map.keys bind1)
            in List.foldr f (True, subst) (List.zip3 tys1 tys2 vars)
          | otherwise ->
            let t1 = lookup bind1 env s1
                t2 = lookup bind2 env s2
                assum' = Map.insert (s1, s2) (tys1, tys2) assum
            in sub assum' subst t1 t2
       where f (t1, t2, Top) (True, subst) =
               let (b1, subst') = sub assum subst t1 t2
                   (b2, subst'') = sub assum subst' t2 t1
               in (b1 && b2, subst'')
             f (t1, t2, Positive) (True, subst) = sub assum subst t1 t2
             f (t1, t2, Negative) (True, subst) = sub assum subst t2 t1
             f (t1, t2, Bottom) (True, subst) = (True, subst)
             f _ (False, subst) = (False, subst)
    sub assum subst (Name s tys) ty = sub assum subst (lookup bind1 env s) ty
    sub assum subst ty (Name s tys) = sub assum subst ty (lookup bind2 env s)
    sub assum subst (TypeVar u) ty =
      case unify' (TypeVar u) ty env argOrd subst of
        Just (_, subst') -> (True, subst')
        Nothing -> (False, subst)
    sub assum subst ty (TypeVar u) =
      case unify' (TypeVar u) ty env argOrd subst of
        Just (_, subst') -> (True, subst')
        Nothing -> (False, subst)
    sub assum subst (Union t11 t12) (Union t21 t22) =
      let (b1121, subst1121) = sub assum subst t11 t21
          (b1221, subst1221) = sub assum subst1121 t12 t21
          (b1222, subst1222) = sub assum subst1121 t12 t22
      
          (b1122, subst1122) = sub assum subst t11 t22
          (b1221', subst1221') = sub assum subst1122 t12 t21
          (b1222', subst1222') = sub assum subst1122 t12 t22
      in if b1121 && b1221 then (True, subst1221)
         else if b1121 && b1222 then (True, subst1222)
         else if b1122 && b1221' then (True, subst1221')
         else if b1122 && b1222' then (True, subst1222')
         else (False, subst)
    sub assum subst (Union t1 t2) ty =
      let (b1, subst') = sub assum subst t1 ty
          (b2, subst'') = sub assum subst' t2 ty
      in (b1 && b2, subst'')
    sub assum subst ty (Union t1 t2) =
      let (b1, subst') = sub assum subst ty t1
          (b2, subst'') = sub assum subst' ty t2
      in (b1 || b2, subst'')
    sub assum subst (Arrow tDom1 tCod1) (Arrow tDom2 tCod2) =
      let (b1, subst') = sub assum subst tDom2 tDom1
          (b2, subst'') = sub assum subst' tCod1 tCod2
      in (b1 && b2, subst'')
    sub assum subst (Tuple tys1) (Tuple tys2) =
      if List.length tys1 >= List.length tys2 then
        List.foldr f (True, subst) (List.zip tys1 tys2)
      else (False, subst)
      where f (t1, t2) (True, subst) = sub assum subst t1 t2
            f _ (False, subst) = (False, subst)
    sub assum subst (Array t1) (Array t2) = sub assum subst t1 t2
    sub assum subst (Set t1) (Set t2) = sub assum subst t1 t2
    sub assum subst (Record fields1) (Record fields2) =
      List.foldr f (True, subst) fields1
      where f (name, ty) (b, subst) =
             case List.lookup name fields2 of
              Just ty' -> sub assum subst ty ty'
              Nothing -> (False, subst)
    sub assum subst (AllOf tys) ty =
      List.foldr f (True, subst) tys
      where f ty' (True, subst) = sub assum subst ty' ty
            f _ (False, subst) = (False, subst)
    sub assum subst ty (AllOf tys) =
      List.foldr f (True, subst) tys
      where f ty' (True, subst) = sub assum subst ty ty'
            f _ (False, subst) = (False, subst)
    sub _ subst IntType IntType = (True, subst)
    sub _ subst IntType RealType = (True, subst)
    sub _ subst RealType RealType = (True, subst)
    sub _ subst BoolType BoolType = (True, subst)
    sub _ subst StringType StringType = (True, subst)
    sub _ _ _ _ = (False, subst)
  in sub Map.empty subst t1 t2