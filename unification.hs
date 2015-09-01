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
import qualified Debug.Trace as Debug

type Substitution = Map U.Unique Type
type Env = Map String Type

mkTypeVar :: IO Type  
mkTypeVar = U.newUnique >>=
              return . TypeVar

generalize :: U.Unique -> Substitution -> Substitution
generalize u subst =
  case Map.lookup u subst of
    Just (TypeVar u') -> generalize u' (Map.delete u subst)
    Just ty -> Map.delete u subst
    Nothing -> subst

makeBindings :: ArgOrd -> String -> [Type] -> Bindings
makeBindings argOrd s types = Map.fromList $ List.zip (Map.elems (argOrd ! s)) types

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
    Just IntType        -> IntType
    Just StringType     -> StringType
    Just BoolType       -> BoolType
    Just RealType       -> RealType
    Just (Name s types) -> Name s types
    Just (Array ty) -> Array (follow subst ty)
    Just (Tuple types) -> Tuple (List.map (follow subst) types)
    Just (Set ty) -> Set (follow subst ty)
    Just (Record fields) -> let f (s, ty) = (s, follow subst ty)
                            in Record (List.map f fields)
    Just (Arrow tDom tCod) -> Arrow (follow subst tDom) (follow subst tCod)
    Just (Union t1 t2) -> Union (follow subst t1) (follow subst t2)
    Just (Forall u ty) -> Forall u (follow subst ty)
    Just Error -> Error
    Just (AllOf types) -> AllOf (List.map (follow subst) types)
follow subst t = t

unify :: Type -> Type -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
unify t1 t2 env argOrd subst =
  let
    uni (TypeVar u) (TypeVar u') subst =
      case (follow subst (TypeVar u), follow subst (TypeVar u')) of
        (TypeVar u, TypeVar u') ->
          return (TypeVar u, Map.insert u (TypeVar u') subst)
        (TypeVar u, t) ->
          return (t, Map.insert u t subst)
        (t, TypeVar u') ->
          return (t, Map.insert u' t subst)
        (t, t') -> uni t t' subst
    uni (Forall u t1) t2 subst = do
      (ty, subst') <- uni t1 t2 subst
      return (ty, generalize u subst')
    uni t1 (Forall u t2) subst = do
      (ty, subst') <- uni t1 t2 subst
      return (ty, generalize u subst')
    uni (TypeVar u) t subst =
      case follow subst (TypeVar u) of
        TypeVar u -> return (t, Map.insert u t subst)
        t'        -> do (t'', subst') <- uni t t' subst 
                        return (t'', Map.insert u t'' subst')
    uni t (TypeVar u) subst = uni (TypeVar u) t subst
    uni t1@(Name s1 types1) t2@(Name s2 types2) subst =
      case subtype' env subst argOrd (env ! s1, bind1) (env ! s2, bind2) of
        (True, subst') -> return (t1, subst')
        (False, _) -> return (Union t1 t2, subst)
      where bind1 = makeBindings argOrd s1 types1
            bind2 = makeBindings argOrd s2 types2
    uni t1@(Name s types) t2 subst =
      case subtype' env subst argOrd (env ! s, bind) (t2, Map.empty) of
        (True, subst') -> return (t1, subst')
        (False, _) -> return (Union t1 t2, subst)
      where bind = makeBindings argOrd s types
    uni t1 t2@(Name s types) subst =
      case subtype' env subst argOrd (t1, Map.empty) (env ! s, bind) of
        (True, subst') -> return (t1, subst')
        (False, _) -> return (Union t1 t2, subst)
      where bind = makeBindings argOrd s types
    uni (Array t1) (Array t2) subst = do
      (t, subst') <- uni t1 t2 subst 
      return (Array t, subst')
    uni (Tuple [t1]) (Tuple [t2]) subst = do
      (t, subst') <- uni t1 t2 subst 
      return (Tuple [t], subst')
    uni (Tuple [t1]) t2 subst = do
      (t, subst') <- uni t1 t2 subst 
      return (t, subst')
    uni t1 (Tuple [t2]) subst = do
      (t, subst') <- uni t1 t2 subst 
      return (t, subst')
    uni (Tuple types1) (Tuple types2) subst =
      if List.length types1 == List.length types2 then do
        (types, subst') <- unifyPairwise types1 types2 env argOrd subst 
        return (Tuple types, subst')
      else return (Union (Tuple types1) (Tuple types2), subst)
    uni (Set t1) (Set t2) subst = do
      (t, subst') <- uni t1 t2 subst 
      return (Set t, subst')
    uni (Record fields1) (Record fields2) subst = do
      (types, subst') <- unifyPairwise types1 types2 env argOrd subst
      let fields = List.zip names1 types
      if names1 == names2 then
        return (Record fields, subst')
      else return (Union (Record fields1) (Record fields2), subst)
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst = do
      (tyDom, subst') <- uni tyDom1 tyDom2 subst 
      (tyCod, subst'') <- uni tyCod1 tyCod2 subst' 
      return (Arrow tyDom tyCod, subst'')
    uni (Union t1 t2) (Union t3 t4) subst = do -- This is incorrect.
      (t13, subst') <- uni t1 t3 subst         -- The correct version
      (t24, subst'') <- uni t2 t4 subst'       -- should be like in subtype
      return (Union t13 t24, subst'')
    uni (AllOf ts1) (AllOf ts2) subst =
      return (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
    uni (AllOf ts) t subst =
      if Set.member t (Set.fromList ts) then
        return (t, subst)
      else return (Union (AllOf ts) t, subst)
    uni t (AllOf ts) subst = uni (AllOf ts) t subst
    uni IntType IntType subst = return (IntType, subst)
    uni RealType RealType subst = return (RealType, subst)
    uni StringType StringType subst = return (StringType, subst)
    uni BoolType BoolType subst = return (BoolType, subst)
    uni t1 t2 subst = return (Union t1 t2, subst)
  in uni t1 t2 subst

unify' :: Type -> Type -> Env -> ArgOrd -> Substitution -> Maybe (Type, Substitution)
unify' t1 t2 env argOrd subst =
  let
    uni' (TypeVar u) (TypeVar u') subst =
      case (follow subst (TypeVar u), follow subst (TypeVar u')) of
        (TypeVar u, TypeVar u') -> Just (TypeVar u, Map.insert u (TypeVar u') subst)
        (TypeVar u, t) -> Just (t, Map.insert u t subst)
        (t, TypeVar u') -> Just (t, Map.insert u' t subst)
        (t, t') -> uni' t t' subst
    uni' (Forall u t1) t2 subst =
      case uni' t1 t2 subst of
        Just (ty, subst') -> Just (ty, generalize u subst')
        Nothing -> Nothing
    uni' t1 (Forall u t2) subst =
      case uni' t1 t2 subst of
        Just (ty, subst') -> Just (ty, generalize u subst')
        Nothing -> Nothing
    uni' (TypeVar u) t subst =
      case follow subst (TypeVar u) of
        TypeVar u -> Just (t, Map.insert u t subst)
        t'        -> case uni' t' t subst of
                      Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                      Nothing            -> Nothing
    uni' t (TypeVar u) subst =
      case follow subst (TypeVar u) of
        TypeVar u -> Just (t, Map.insert u t subst)
        t'        -> case uni' t t' subst of
                      Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                      Nothing            -> Nothing
    uni' t1@(Name s1 types1) (Name s2 types2) subst =
      case subtype' env subst argOrd (env ! s1, bind1) (env ! s2, bind2) of
        (True, subst') -> Just (t1, subst')
        (False, _) -> Nothing
      where bind1 = makeBindings argOrd s1 types1
            bind2 = makeBindings argOrd s2 types2
    uni' t1@(Name s types) t2 subst =
      case subtype' env subst argOrd (env ! s, bind) (t2, Map.empty) of
        (True, subst') -> Just (t1, subst')
        (False, _) -> Nothing
      where bind = makeBindings argOrd s types
    uni' t1 t2@(Name s types) subst =
      case subtype' env subst argOrd (t1, Map.empty) (env ! s, bind) of
        (True, subst') -> Just (t1, subst')
        (False, _) -> Nothing
      where bind = makeBindings argOrd s types
    uni' (Array t1) (Array t2) subst =
      case uni' t1 t2 subst of
        Just (t, subst') -> Just (Array t, subst')
        Nothing -> Nothing
    uni' (Tuple [t1]) (Tuple [t2]) subst =
      uni' t1 t2 subst
    uni' (Tuple [t1]) t2 subst =
      uni' t1 t2 subst
    uni' t1 (Tuple [t2]) subst =
      uni' t1 t2 subst
    uni' (Tuple types1) (Tuple types2) subst =
      case unifyPairwise' types1 types2 env argOrd subst of
        Just (types, subst') -> Just (Tuple types, subst')
        Nothing -> Nothing
    uni' (Set t1) (Set t2) subst =
      case uni' t1 t2 subst of
        Just (t, subst') -> Just (Set t, subst')
        Nothing -> Nothing
    uni' (Record fields1) (Record fields2) subst =
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
    uni' (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst =
      case uni' tyDom2 tyDom1 subst of
        Just (tyDom, subst') ->
          case uni' tyCod1 tyCod2 subst' of
            Just (tyCod, subst'') -> Just (Arrow tyDom tyCod, subst'')
            Nothing -> Nothing
        Nothing -> Nothing
    uni' (Union t1 t2) (Union t3 t4) subst =
      case uni' t1 t3 subst of
        Just (t13, subst') ->
          case uni' t2 t4 subst' of
            Just (t24, subst'') -> Just (Union t13 t24, subst'')
            Nothing -> Nothing
        Nothing -> Nothing
    uni' ty (Union t1 t2) subst =
      case uni' ty t1 subst of
        Just (t, subst') -> Just (t, subst')
        Nothing -> uni' ty t2 subst
    uni' (Union t1 t2) ty subst =
      case uni' t1 ty subst of
        Just (t, subst') -> Just (t, subst')
        Nothing -> uni' t2 ty subst
    uni' (AllOf ts1) (AllOf ts2) subst =
      Just (AllOf $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
    uni' (AllOf ts) t subst =
      if Set.member t (Set.fromList ts) then
        Just (t, subst)
      else Nothing
    uni' t (AllOf ts) subst = uni' (AllOf ts) t subst
    uni' IntType IntType subst = Just (IntType, subst)
    uni' RealType RealType subst = Just (RealType, subst)
    uni' StringType StringType subst = Just (StringType, subst)
    uni' BoolType BoolType subst = Just (BoolType, subst)
    uni' _ _ _ = Nothing
  in uni' t1 t2 subst

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
      inst (Forall u ty) = Forall u (inst ty)
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
      var trace v (Forall u ty) = var trace v ty
      var trace v (Union t1 t2) = lub (var trace v t1) (var trace v t2)
      var trace v (Tuple ts) = lub' (List.map (var trace v) ts)
      var trace v (Record fields) = lub' (List.map (var trace v . snd) fields)
      var trace v (Array ty) = var trace v ty
      var trace v (Set ty) = var trace v ty
      var trace v (AllOf ts) = lub' (List.map (var trace v) ts)
      var trace v _ = v
  in var Set.empty Bottom t

subtype :: Type -> Type -> Env -> ArgOrd -> Substitution -> (Bool, Substitution)
subtype t1 t2 env argOrd subst = subtype' env subst argOrd (t1, Map.empty) (t2, Map.empty)

subtype' :: Env -> Substitution -> ArgOrd -> (Type, Bindings) -> (Type, Bindings) -> (Bool, Substitution)
subtype' env subst argOrd (t1, bind1) (t2, bind2) =
  let
    lookup bind env s = Map.findWithDefault (bind ! s) s env

    sub assum subst (Forall u t1) t2 =
      case sub assum subst t1 t2 of
        (True, subst') -> (True, generalize u subst')
        (False, subst') -> (False, subst')
    sub assum subst t1 (Forall u t2) =
      case sub assum subst t1 t2 of
        (True, subst') -> (True, generalize u subst')
        (False, subst') -> (False, subst')
    sub assum subst t1 t2@(TypeVar u) =
      case follow subst t2 of
        TypeVar u -> (True, Map.insert u t1 subst)
        ty -> sub assum subst t1 ty
    sub assum subst t1@(TypeVar u) t2 =
      case follow subst t1 of
        TypeVar u -> (True, Map.insert u t2 subst)
        ty -> sub assum subst ty t2
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