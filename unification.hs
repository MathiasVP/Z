module Unification where
import Control.Monad
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Unique as U
import qualified Data.List as List
import Data.Set (Set)
import Data.Map (Map)
import Data.Map ((!))
import Ast
import TypedAst

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
makeBindings argOrd s types =
  case Map.lookup s argOrd of
    Just argOrd -> Map.fromList $ List.zip (Map.elems argOrd) types
    Nothing -> Map.empty

unifyTypes :: [Type] -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
unifyTypes types env argOrd subst = do
  t <- mkTypeVar
  foldM f (t, subst) types
  where f (ty, subst) ty' =
          unify ty ty' env argOrd subst 

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
    Just (Record b fields) -> let f (s, ty) = (s, follow subst ty)
                            in Record b (List.map f fields)
    Just (Arrow tDom tCod) -> Arrow (follow subst tDom) (follow subst tCod)
    Just (Union t1 t2) -> Union (follow subst t1) (follow subst t2)
    Just (Forall u ty) -> Forall u (follow subst ty)
    Just Error -> Error
    Just (Intersection types) -> Intersection (List.map (follow subst) types)
follow subst t = t

inserts :: Ord a => Set a -> [a] -> Set a
inserts = List.foldr Set.insert

unify :: Type -> Type -> Env -> ArgOrd -> Substitution -> IO (Type, Substitution)
unify t1 t2 env argOrd subst =
  let
    lookup bind env s = Map.findWithDefault (bind ! s) s env

    uni trace bind1 bind2 (TypeVar u) (TypeVar u') subst =
      case (follow subst (TypeVar u), follow subst (TypeVar u')) of
        (TypeVar u, TypeVar u') ->
          return (TypeVar u, Map.insert u (TypeVar u') subst)
        (TypeVar u, t) ->
          return (t, Map.insert u t subst)
        (t, TypeVar u') ->
          return (t, Map.insert u' t subst)
        (t, t') -> uni trace bind1 bind2 t t' subst
    uni trace bind1 bind2 (Forall u t1) t2 subst = do
      (ty, subst') <- uni trace bind1 bind2 t1 t2 subst
      return (ty, generalize u subst')
    uni trace bind1 bind2 t1 (Forall u t2) subst = do
      (ty, subst') <- uni trace bind1 bind2 t1 t2 subst
      return (ty, generalize u subst')
    uni trace bind1 bind2 (TypeVar u) t subst =
      case follow subst (TypeVar u) of
        TypeVar u -> return (t, Map.insert u t subst)
        t'        -> do (t'', subst') <- uni trace bind1 bind2 t t' subst 
                        return (t'', Map.insert u t'' subst')
    uni trace bind1 bind2 t (TypeVar u) subst = uni trace bind1 bind2 (TypeVar u) t subst
    uni trace bind1 bind2 t1@(Name s1 types1) t2@(Name s2 types2) subst
      | Set.member s1 trace && Set.member s2 trace =
        return (Union (instansiate' t1 bind1') (instansiate' t2 bind2'), subst)
      | Set.member s1 trace =
        uni (Set.insert s2 trace) bind1 bind2' t1 t2' subst
      | Set.member s2 trace =
        uni (Set.insert s1 trace) bind1' bind2 t1' t2 subst
      | otherwise =
        uni (inserts trace [s1, s2]) bind1' bind2' t1' t2' subst
      where t1' = lookup bind1 env s1
            t2' = lookup bind2 env s2
            bind1' = makeBindings argOrd s1 types1
            bind2' = makeBindings argOrd s2 types2
    uni trace bind1 bind2 t1@(Name s types) t2 subst
      | Set.member s trace =
        return (Union (instansiate' t1 bind) (instansiate' t2 bind2), subst)
      | otherwise =
        uni (Set.insert s trace) bind bind2 t t2 subst
      where t = lookup bind1 env s
            bind = makeBindings argOrd s types
    uni trace bind1 bind2 t1 t2@(Name s types) subst
      | Set.member s trace =
        return (Union (instansiate' t1 bind1) (instansiate' t2 bind), subst)
      | otherwise =
        uni (Set.insert s trace) bind1 bind t1 t subst
      where t = lookup bind2 env s
            bind = makeBindings argOrd s types
    uni trace bind1 bind2 (Array t1) (Array t2) subst = do
      (t, subst') <- uni trace bind1 bind2 t1 t2 subst 
      return (Array t, subst')
    uni trace bind1 bind2 (Tuple [t1]) (Tuple [t2]) subst = do
      (t, subst') <- uni trace bind1 bind2 t1 t2 subst 
      return (Tuple [t], subst')
    uni trace bind1 bind2 (Tuple [t1]) t2 subst = do
      (t, subst') <- uni trace bind1 bind2 t1 t2 subst 
      return (t, subst')
    uni trace bind1 bind2 t1 (Tuple [t2]) subst = do
      (t, subst') <- uni trace bind1 bind2 t1 t2 subst 
      return (t, subst')
    uni trace bind1 bind2 (Tuple types1) (Tuple types2) subst =
      if List.length types1 == List.length types2 then do
        (types, subst') <- unifyPairwise trace bind1 bind2 types1 types2 subst 
        return (Tuple types, subst')
      else return (Union (Tuple types1) (Tuple types2), subst)
    uni trace bind1 bind2 (Record b1 fields1) (Record b2 fields2) subst = do
      (types, subst') <- unifyPairwise trace bind1 bind2 types1 types2 subst
      let fields = List.zip names1 types
      if names1 == names2 then
        return (Record (b1 && b2) fields, subst')
      else return (Union (Record b1 fields1) (Record b2 fields2), subst)
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni trace bind1 bind2 (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst = do
      (tyDom, subst') <- uni trace bind1 bind2 tyDom1 tyDom2 subst 
      (tyCod, subst'') <- uni trace bind1 bind2 tyCod1 tyCod2 subst' 
      return (Arrow tyDom tyCod, subst'')
    uni trace bind1 bind2 (Union t1 t2) (Union t3 t4) subst = do
      (t13, subst') <- uni trace bind1 bind2 t1 t3 subst
      (t24, subst'') <- uni trace bind1 bind2 t2 t4 subst'
      return (Union t13 t24, subst'')
    uni trace bind1 bind2 (Intersection ts1) (Intersection ts2) subst =
      return (Intersection $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
    uni trace bind1 bind2 (Intersection ts) t subst =
      if Set.member t (Set.fromList ts) then
        return (t, subst)
      else return (Union (Intersection ts) t, subst)
    uni trace bind1 bind2 t (Intersection ts) subst = uni trace bind1 bind2 (Intersection ts) t subst
    uni trace bind1 bind2 IntType IntType subst = return (IntType, subst)
    uni trace bind1 bind2 RealType RealType subst = return (RealType, subst)
    uni trace bind1 bind2 StringType StringType subst = return (StringType, subst)
    uni trace bind1 bind2 BoolType BoolType subst = return (BoolType, subst)
    uni trace bind1 bind2 t1 t2 subst = return (Union t1 t2, subst)
    
    unifyPairwise trace bind1 bind2 types1 types2 subst = do
      let types = List.zip types1 types2
      let f (types, subst) (t1, t2) =
            do (t, subst') <- uni trace bind1 bind2 t1 t2 subst 
               return (t : types, subst')
      (types', subst') <- foldM f ([], subst) types
      return (List.reverse types', subst')
  
  in uni Set.empty Map.empty Map.empty t1 t2 subst

unify' :: Type -> Type -> Env -> ArgOrd -> Substitution -> Maybe (Type, Substitution)
unify' t1 t2 env argOrd subst =
  let
    lookup bind env s = Map.findWithDefault (bind ! s) s env

    uni' trace bind1 bind2 (TypeVar u) (TypeVar u') subst =
      case (follow subst (TypeVar u), follow subst (TypeVar u')) of
        (TypeVar u, TypeVar u') -> Just (TypeVar u, Map.insert u (TypeVar u') subst)
        (TypeVar u, t) -> Just (t, Map.insert u t subst)
        (t, TypeVar u') -> Just (t, Map.insert u' t subst)
        (t, t') -> uni' trace bind1 bind2 t t' subst
    uni' trace bind1 bind2 (Forall u t1) t2 subst =
      case uni' trace bind1 bind2 t1 t2 subst of
        Just (ty, subst') -> Just (ty, generalize u subst')
        Nothing -> Nothing
    uni' trace bind1 bind2 t1 (Forall u t2) subst =
      case uni' trace bind1 bind2 t1 t2 subst of
        Just (ty, subst') -> Just (ty, generalize u subst')
        Nothing -> Nothing
    uni' trace bind1 bind2 (TypeVar u) t subst =
      case follow subst (TypeVar u) of
        TypeVar u -> Just (t, Map.insert u t subst)
        t'        -> case uni' trace bind1 bind2 t' t subst of
                      Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                      Nothing            -> Nothing
    uni' trace bind1 bind2 t (TypeVar u) subst =
      case follow subst (TypeVar u) of
        TypeVar u -> Just (t, Map.insert u t subst)
        t'        -> case uni' trace bind1 bind2 t t' subst of
                      Just (t'', subst') -> Just (t'', Map.insert u t'' subst')
                      Nothing            -> Nothing
    uni' trace bind1 bind2 t1@(Name s1 types1) t2@(Name s2 types2) subst
      | Set.member s1 trace && Set.member s2 trace =
        Nothing
      | Set.member s1 trace =
        uni' (Set.insert s2 trace) bind1 bind2' t1 t2' subst
      | Set.member s2 trace =
        uni' (Set.insert s1 trace) bind1' bind2 t1' t2 subst
      | otherwise =
        uni' (inserts trace [s1, s2]) bind1' bind2' t1' t2' subst
      where t1' = lookup bind1 env s1
            t2' = lookup bind2 env s2
            bind1' = makeBindings argOrd s1 types1
            bind2' = makeBindings argOrd s2 types2
    uni' trace bind1 bind2 (Name s types) t2 subst
      | Set.member s trace =
        Nothing
      | otherwise =
        uni' (Set.insert s trace) bind bind2 t t2 subst
      where t = lookup bind1 env s
            bind = makeBindings argOrd s types
    uni' trace bind1 bind2 t1 (Name s types) subst
      | Set.member s trace =
        Nothing
      | otherwise =
        uni' (Set.insert s trace) bind1 bind t1 t subst
      where t = lookup bind2 env s
            bind = makeBindings argOrd s types
    uni' trace bind1 bind2 (Array t1) (Array t2) subst =
      case uni' trace bind1 bind2 t1 t2 subst of
        Just (t, subst') -> Just (Array t, subst')
        Nothing -> Nothing
    uni' trace bind1 bind2 (Tuple [t1]) (Tuple [t2]) subst =
      uni' trace bind1 bind2 t1 t2 subst
    uni' trace bind1 bind2 (Tuple [t1]) t2 subst =
      uni' trace bind1 bind2 t1 t2 subst
    uni' trace bind1 bind2 t1 (Tuple [t2]) subst =
      uni' trace bind1 bind2 t1 t2 subst
    uni' trace bind1 bind2 (Tuple types1) (Tuple types2) subst =
      case unifyPairwise' trace bind1 bind2 types1 types2 subst of
        Just (types, subst') -> Just (Tuple types, subst')
        Nothing -> Nothing
    uni' trace bind1 bind2 (Record b1 fields1) (Record b2 fields2) subst
      | names1 == names2 =
        case unifyPairwise' trace bind1 bind2 types1 types2 subst of
          Just (types, subst') ->
            let fields = List.zip names1 types
            in Just (Record (b1 && b2) fields, subst')
          Nothing -> Nothing
      | otherwise = Nothing
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni' trace bind1 bind2 (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) subst =
      case uni' trace bind1 bind2 tyDom2 tyDom1 subst of
        Just (tyDom, subst') ->
          case uni' trace bind1 bind2 tyCod1 tyCod2 subst' of
            Just (tyCod, subst'') -> Just (Arrow tyDom tyCod, subst'')
            Nothing -> Nothing
        Nothing -> Nothing
    uni' trace bind1 bind2 (Union t11 t12) (Union t21 t22) subst =
      case (uni' trace bind1 bind2 t11 t21 subst,
            uni' trace bind1 bind2 t11 t22 subst) of
        (Just (t1121, subst1121), _) ->
          case (uni' trace bind1 bind2 t12 t21 subst1121,
                uni' trace bind1 bind2 t12 t22 subst1121) of
            (Just (t1221, subst1221), _) -> Just (Union t1121 t1221, subst1221)
            (_, Just (t1222, subst1222)) -> Just (Union t1121 t1222, subst1222)
        (_, Just (t1122, subst1122)) ->
          case (uni' trace bind1 bind2 t12 t21 subst1122,
                uni' trace bind1 bind2 t12 t22 subst1122) of
            (Just (t1221, subst1221), _) -> Just (Union t1122 t1221, subst1221)
            (_, Just (t1222, subst1222)) -> Just (Union t1122 t1222, subst1222)
        (_, _) -> Nothing
    uni' trace bind1 bind2 ty (Union t1 t2) subst =
      case uni' trace bind1 bind2 ty t1 subst of
        Just (t, subst') -> Just (t, subst')
        Nothing -> uni' trace bind1 bind2 ty t2 subst
    uni' trace bind1 bind2 (Union t1 t2) ty subst =
      case uni' trace bind1 bind2 t1 ty subst of
        Just (t, subst') -> Just (t, subst')
        Nothing -> uni' trace bind1 bind2 t2 ty subst
    uni' trace bind1 bind2 (Intersection ts1) (Intersection ts2) subst =
      Just (Intersection $ Set.toList $ Set.intersection (Set.fromList ts1) (Set.fromList ts2), subst)
    uni' trace bind1 bind2 (Intersection ts) t subst
      | Set.member t (Set.fromList ts) = Just (t, subst)
      | otherwise = Nothing
    uni' trace bind1 bind2 t (Intersection ts) subst = uni' trace bind1 bind2 (Intersection ts) t subst
    uni' trace bind1 bind2 IntType IntType subst = Just (IntType, subst)
    uni' trace bind1 bind2 RealType RealType subst = Just (RealType, subst)
    uni' trace bind1 bind2 StringType StringType subst = Just (StringType, subst)
    uni' trace bind1 bind2 BoolType BoolType subst = Just (BoolType, subst)
    uni' trace _ _ _ _ _ = Nothing
    
    unifyPairwise' trace bind1 bind2 types1 types2 subst =
      if List.length types1 /= List.length types2 then
        Nothing
      else List.foldr f (Just ([], subst)) (List.zip types1 types2)
      where f (t1, t2) (Just (types, subst)) =
                case uni' trace bind1 bind2 t1 t2 subst of
                  Just (t, subst') -> (Just (t : types, subst'))
                  Nothing -> Nothing
            f _ Nothing = Nothing
        
  in uni' Set.empty Map.empty Map.empty t1 t2 subst
        
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
      inst (Record b fields) = Record b (List.map (\(s, ty) -> (s, inst ty)) fields)
      inst (Array ty) = Array (inst ty)
      inst (TypeVar u) = TypeVar u
      inst Error = Error
      inst IntType = IntType
      inst RealType = RealType
      inst BoolType = BoolType
      inst StringType = StringType
      inst (Intersection tys) = Intersection (List.map inst tys)
  in inst t

instansiate' :: Type -> Map String Type -> Type
instansiate' = Map.foldrWithKey instansiate

variance :: Env -> ArgOrd -> Type -> String -> Variance
variance env argOrd t s =
  let var trace v (Name s' tys)
        | Set.member s' trace = v
        | otherwise =
          case Map.lookup s' env of
            Just ty ->
              let order = argOrd ! s'
                  names = List.map (order !) [0..]
                  ty' = instansiate' ty (Map.fromList (List.zip names tys))
              in var (Set.insert s' trace) v ty'
            Nothing
              | s == s'   -> lub v Positive
              | otherwise -> v
      var trace v (Arrow t1 t2) =
        lub (invert (var trace v t1)) (var trace v t2)
      var trace v (Forall u ty) = var trace v ty
      var trace v (Union t1 t2) = lub (var trace v t1) (var trace v t2)
      var trace v (Tuple ts) = lub' (List.map (var trace v) ts)
      var trace v (Record b fields) = lub' (List.map (var trace v . snd) fields)
      var trace v (Array ty) = var trace v ty
      var trace v (Intersection ts) = lub' (List.map (var trace v) ts)
      var trace v _ = v
  in var Set.empty Bottom t
  

subtype :: Type -> Type -> Env -> ArgOrd -> Substitution -> (Bool, Substitution)
subtype t1 t2 env argOrd subst =
  let
    lookup bind env s = Map.findWithDefault (bind ! s) s env

    sub trace bind1 bind2 assum subst (Forall u t1) t2 =
      case sub trace bind1 bind2 assum subst t1 t2 of
        (True, subst') -> (True, generalize u subst')
        (False, subst') -> (False, subst')
    sub trace bind1 bind2 assum subst t1 (Forall u t2) =
      case sub trace bind1 bind2 assum subst t1 t2 of
        (True, subst') -> (True, generalize u subst')
        (False, subst') -> (False, subst')
    sub trace bind1 bind2 assum subst t1 t2@(TypeVar u) =
      case follow subst t2 of
        TypeVar u -> (True, Map.insert u t1 subst)
        ty -> sub trace bind1 bind2 assum subst t1 ty
    sub trace bind1 bind2 assum subst t1@(TypeVar u) t2 =
      case follow subst t1 of
        TypeVar u -> (True, Map.insert u t2 subst)
        ty -> sub trace bind1 bind2 assum subst ty t2
    sub trace bind1 bind2 assum subst (Name s1 tys1) (Name s2 tys2) =
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
            in sub trace bind1 bind2 assum' subst t1 t2
       where f (t1, t2, Top) (True, subst) =
               let (b1, subst') = sub trace bind1 bind2 assum subst t1 t2
                   (b2, subst'') = sub trace bind1 bind2 assum subst' t2 t1
               in (b1 && b2, subst'')
             f (t1, t2, Positive) (True, subst) = sub trace bind1 bind2 assum subst t1 t2
             f (t1, t2, Negative) (True, subst) = sub trace bind1 bind2 assum subst t2 t1
             f (t1, t2, Bottom) (True, subst) = (True, subst)
             f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 assum subst (Name s tys) ty
      | Set.member s trace =
        (False, subst)
      | otherwise =
        sub (Set.insert s trace) bind1' bind2 assum subst (lookup bind1 env s) ty
      where bind1' = makeBindings argOrd s tys
    sub trace bind1 bind2 assum subst ty (Name s tys)
      | Set.member s trace =
        (False, subst)
      | otherwise =
        sub (Set.insert s trace) bind1 bind2' assum subst ty (lookup bind2 env s)
      where bind2' = makeBindings argOrd s tys
    sub trace bind1 bind2 assum subst (Union t11 t12) (Union t21 t22) =
      let (b1121, subst1121) = sub trace bind1 bind2 assum subst t11 t21
          (b1221, subst1221) = sub trace bind1 bind2 assum subst1121 t12 t21
          (b1222, subst1222) = sub trace bind1 bind2 assum subst1121 t12 t22
      
          (b1122, subst1122) = sub trace bind1 bind2 assum subst t11 t22
          (b1221', subst1221') = sub trace bind1 bind2 assum subst1122 t12 t21
          (b1222', subst1222') = sub trace bind1 bind2 assum subst1122 t12 t22
      in if b1121 && b1221 then (True, subst1221)
         else if b1121 && b1222 then (True, subst1222)
         else if b1122 && b1221' then (True, subst1221')
         else if b1122 && b1222' then (True, subst1222')
         else (False, subst)
    sub trace bind1 bind2 assum subst (Union t1 t2) ty =
      let (b1, subst') = sub trace bind1 bind2 assum subst t1 ty
          (b2, subst'') = sub trace bind1 bind2 assum subst' t2 ty
      in (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst ty (Union t1 t2) =
      let (b1, subst') = sub trace bind1 bind2 assum subst ty t1
          (b2, subst'') = sub trace bind1 bind2 assum subst' ty t2
      in (b1 || b2, subst'')
    sub trace bind1 bind2 assum subst (Arrow tDom1 tCod1) (Arrow tDom2 tCod2) =
      let (b1, subst') = sub trace bind1 bind2 assum subst tDom2 tDom1
          (b2, subst'') = sub trace bind1 bind2 assum subst' tCod1 tCod2
      in (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst (Tuple tys1) (Tuple tys2) =
      if List.length tys1 >= List.length tys2 then
        List.foldr f (True, subst) (List.zip tys1 tys2)
      else (False, subst)
      where f (t1, t2) (True, subst) = sub trace bind1 bind2 assum subst t1 t2
            f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 assum subst (Array t1) (Array t2) = sub trace bind1 bind2 assum subst t1 t2
    sub trace bind1 bind2 assum subst (Record _ fields1) (Record b2 fields2) =
      List.foldr f (True, subst) fields1
      where f (name, ty) (b, subst) =
             case List.lookup name fields2 of
              Just ty' -> sub trace bind1 bind2 assum subst ty ty'
              Nothing -> (b2, subst)
    sub trace bind1 bind2 assum subst (Intersection tys) ty =
      List.foldr f (True, subst) tys
      where f ty' (True, subst) = sub trace bind1 bind2 assum subst ty' ty
            f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 assum subst ty (Intersection tys) =
      List.foldr f (True, subst) tys
      where f ty' (True, subst) = sub trace bind1 bind2 assum subst ty ty'
            f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 _ subst IntType IntType = (True, subst)
    sub trace bind1 bind2 _ subst IntType RealType = (True, subst)
    sub trace bind1 bind2 _ subst RealType RealType = (True, subst)
    sub trace bind1 bind2 _ subst BoolType BoolType = (True, subst)
    sub trace bind1 bind2 _ subst StringType StringType = (True, subst)
    sub trace bind1 bind2 _ _ _ _ = (False, subst)
  in sub Set.empty Map.empty Map.empty Map.empty subst t1 t2