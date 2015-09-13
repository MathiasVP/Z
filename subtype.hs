module Subtype (subtype) where
import Data.Map (Map)
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import TypeUtils
import TypedAst

data Variance
  = Positive
  | Negative
  | Top
  | Bottom

type Assumptions = Map (String, String) ([Type], [Type])

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
      var trace v (Intersect t1 t2) = lub' (List.map (var trace v) [t1, t2])
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
    sub trace bind1 bind2 assum subst (Intersect t1 t2) ty =
      List.foldr f (True, subst) [t1, t2]
      where f ty' (True, subst) = sub trace bind1 bind2 assum subst ty' ty
            f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 assum subst ty (Intersect t1 t2) =
      List.foldr f (True, subst) [t1, t2]
      where f ty' (True, subst) = sub trace bind1 bind2 assum subst ty ty'
            f _ (False, subst) = (False, subst)
    sub trace bind1 bind2 _ subst IntType IntType = (True, subst)
    sub trace bind1 bind2 _ subst IntType RealType = (True, subst)
    sub trace bind1 bind2 _ subst RealType RealType = (True, subst)
    sub trace bind1 bind2 _ subst BoolType BoolType = (True, subst)
    sub trace bind1 bind2 _ subst StringType StringType = (True, subst)
    sub trace bind1 bind2 _ _ _ _ = (False, subst)
  in sub Set.empty Map.empty Map.empty Map.empty subst t1 t2