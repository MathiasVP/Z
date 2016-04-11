{-# LANGUAGE LambdaCase #-}

module Unification where
import Prelude hiding (lookup)
import Control.Monad
import Data.Foldable
import Data.Ord
import Control.Monad.State.Lazy
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe()
import qualified Data.List as List
import Data.Set (Set)
import Data.Map ((!))
import Types
import Ast()
import TypedAst()
import TypeUtils

makeIntersect :: Type -> Type -> Infer Type
makeIntersect t1 t2 = do
  u <- lift mkTypeVar
  unify u (t1 `intersect` t2)
  return u

makeRecord :: Bool -> [(String, Type)] -> Infer Type
makeRecord b fields = do
  u <- lift mkTypeVar
  unify u (Record b fields)
  return u

unifyTypes :: [Type] -> Infer Type
unifyTypes types = do
  t <- lift mkTypeVar
  foldM unify t types

inserts :: Ord a => Set a -> [a] -> Set a
inserts = List.foldr Set.insert

lookup :: Bindings -> Identifier -> Infer Type
lookup bind s = do
  env <- environment
  case Map.lookup (stringOf s) env of
    Just (_, ty) -> return ty
    Nothing -> return $ bind ! stringOf s

unify :: Type -> Type ->  Infer Type
unify t1 t2 =
  let
    uni :: Set Identifier -> Bindings -> Bindings ->
             Type -> Type -> Infer Type
    uni trace bind1 bind2 (TypeVar u) (TypeVar u') = do
      t <- follow (TypeVar u)
      t' <- follow (TypeVar u')
      case (t, t') of
        (TypeVar u, TypeVar u') -> do
          modifySubst (Map.insert u (TypeVar u'))
          return $ TypeVar u'
        (TypeVar u, t) -> do
          modifySubst (Map.insert u t)
          return t
        (t, TypeVar u') -> do
          modifySubst (Map.insert u' t)
          return t
        (t, t') ->
          uni trace bind1 bind2 t t'
    uni trace bind1 bind2 (Forall u t1) t2 =
      uni trace bind1 bind2 t1 t2
    uni trace bind1 bind2 t1 (Forall u t2) =
      uni trace bind1 bind2 (Forall u t2) t1
    uni trace bind1 bind2 (TypeVar u) t =
      follow (TypeVar u) >>= \case
        TypeVar u -> do
          modifySubst (Map.insert u t)
          return t
        t'        -> do
          t'' <- uni trace bind1 bind2 t t'
          modifySubst (Map.insert u t'')
          return t''
    uni trace bind1 bind2 t (TypeVar u) = uni trace bind1 bind2 (TypeVar u) t
    uni trace bind1 bind2 t1@(Name s1 types1) t2@(Name s2 types2) = do
      t1' <- lookup bind1 s1
      t2' <- lookup bind2 s2
      bind1' <- makeBindings s1 types1
      bind2' <- makeBindings s2 types2
      case (Set.member s1 trace, Set.member s2 trace) of
        (True, True) ->
          return $ union (instansiates t1 bind1') (instansiates t2 bind2')
        (True, False) ->
          uni (Set.insert s2 trace) bind1 bind2' t1 t2'
        (False, True) ->
          uni (Set.insert s1 trace) bind1' bind2 t1' t2
        (False, False) ->
          uni (inserts trace [s1, s2]) bind1' bind2' t1' t2'
    uni trace bind1 bind2 t1@(Name s types) t2 = do
      t <- lookup bind1 s
      bind <- makeBindings s types
      if Set.member s trace then
        return $ union (instansiates t1 bind) (instansiates t2 bind2)
      else uni (Set.insert s trace) bind bind2 t t2
    uni trace bind1 bind2 t1 (Name s types) =
      uni trace bind1 bind2 (Name s types) t1
    uni trace bind1 bind2 (Array t1) (Array t2) = do
      t <- uni trace bind1 bind2 t1 t2
      return $ Array t
    uni trace bind1 bind2 (Tuple [t1]) (Tuple [t2]) = do
      t <- uni trace bind1 bind2 t1 t2
      return $ Tuple [t]
    uni trace bind1 bind2 (Tuple [t1]) t2 =
      uni trace bind1 bind2 t1 t2
    uni trace bind1 bind2 t1 (Tuple [t2]) =
      uni trace bind1 bind2 (Tuple [t2]) t1
    uni trace bind1 bind2 (Tuple types1) (Tuple types2) =
      if List.length types1 == List.length types2 then do
        types <- unifyPairwise trace bind1 bind2 types1 types2
        return $ Tuple types
      else return $ union (Tuple types1) (Tuple types2)
    uni trace bind1 bind2 (Record b1 fields1) (Record b2 fields2) = do
      types <- unifyPairwise trace bind1 bind2 types1 types2
      let fields = List.zip names1 types
      if names1 == names2 then
        return $ Record (b1 && b2) fields
      else return $ union (Record b1 fields1) (Record b2 fields2)
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni trace bind1 bind2 (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) = do
      tyDom <- uni trace bind1 bind2 tyDom1 tyDom2
      tyCod <- uni trace bind1 bind2 tyCod1 tyCod2
      return $ Arrow tyDom tyCod
    -- TODO: Not sure if this is correct. Should go through all possibilities
    uni trace bind1 bind2 (Union t1 t2) (Union t3 t4) = do
      t13 <- uni trace bind1 bind2 t1 t3
      t24 <- uni trace bind1 bind2 t2 t4
      return $ union t13 t24
    -- TODO: Should use uni instead of Eq for intersection
    uni trace bind1 bind2 (Intersect t1 t2) (Intersect t3 t4) =
      let intersection = Set.intersection (Set.fromList [t1, t2]) (Set.fromList [t3, t4])
      in if Set.null intersection then
           return $ union (Intersect t1 t2) (Intersect t3 t4)
         else return $ List.foldl1' Intersect (Set.toList intersection)
    uni trace bind1 bind2 (Intersect t1 t2) t =
      if Set.member t (Set.fromList [t1, t2]) then
        return t
      else return $ union (Intersect t1 t2) t
    uni trace bind1 bind2 t (Intersect t1 t2) =
      uni trace bind1 bind2 (Intersect t1 t2) t
    uni _ _ _ IntType IntType = return IntType
    uni _ _ _ RealType RealType = return RealType
    uni _ _ _ StringType StringType = return StringType
    uni _ _ _ BoolType BoolType = return BoolType
    uni _ _ _ t1 t2 = return $ union t1 t2

    unifyPairwise trace bind1 bind2 types1 types2 =
      let types = List.zip types1 types2
      in mapM (uncurry $ uni trace bind1 bind2) types
  in uni Set.empty Map.empty Map.empty t1 t2

unify' :: Type -> Type -> Infer (Maybe Type)
unify' t1 t2 =
  let
    uni' :: Set Identifier -> Bindings -> Bindings ->
             Type -> Type -> Infer (Maybe Type)
    uni' trace bind1 bind2 (TypeVar u) (TypeVar u') = do
      t <- follow (TypeVar u)
      t' <- follow (TypeVar u')
      case (t, t') of
        (TypeVar u, TypeVar u') -> do
          modifySubst (Map.insert u (TypeVar u'))
          return $ Just (TypeVar u')
        (TypeVar u, t) -> do
          modifySubst (Map.insert u t)
          return $ Just t
        (t, TypeVar u') -> do
          modifySubst (Map.insert u' t)
          return $ Just t
        (t, t') -> uni' trace bind1 bind2 t t'
    uni' trace bind1 bind2 (Forall u t1) t2 =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 t1 (Forall u t2) =
      uni' trace bind1 bind2 (Forall u t2) t1
    uni' trace bind1 bind2 (TypeVar u) t =
      follow (TypeVar u) >>= \case
        TypeVar u -> do
          modifySubst (Map.insert u t)
          return $ Just t
        t' -> uni' trace bind1 bind2 t' t >>= \case
                Just t'' -> do
                  modifySubst (Map.insert u t'' )
                  return $ Just t''
                Nothing -> return Nothing
    uni' trace bind1 bind2 t (TypeVar u) =
      uni' trace bind1 bind2 (TypeVar u) t
    uni' trace bind1 bind2 t1@(Name s1 types1) t2@(Name s2 types2) = do
      t1' <- lookup bind1 s1
      t2' <- lookup bind2 s2
      bind1' <- makeBindings s1 types1
      bind2' <- makeBindings s2 types2
      case (Set.member s1 trace, Set.member s2 trace) of
        (True, True) -> return Nothing
        (True, False) -> uni' (Set.insert s2 trace) bind1 bind2' t1 t2'
        (False, True) -> uni' (Set.insert s1 trace) bind1' bind2 t1' t2
        (False, False) -> uni' (inserts trace [s1, s2]) bind1' bind2' t1' t2'
    uni' trace bind1 bind2 (Name s types) t2 = do
      t <- lookup bind1 s
      bind <- makeBindings s types
      if Set.member s trace then return Nothing
      else uni' (Set.insert s trace) bind bind2 t t2
    uni' trace bind1 bind2 t1 (Name s types) =
      uni' trace bind1 bind2 (Name s types) t1
    uni' trace bind1 bind2 (Array t1) (Array t2) =
      uni' trace bind1 bind2 t1 t2 >>= \case
        Just t -> return $ Just $ Array t
        Nothing -> return Nothing
    uni' trace bind1 bind2 (Tuple [t1]) (Tuple [t2]) =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 (Tuple [t1]) t2 =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 t1 (Tuple [t2]) =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 (Tuple types1) (Tuple types2) =
      unifyPairwise' trace bind1 bind2 types1 types2 >>= \case
        Just types -> return $ Just $ Tuple types
        Nothing -> return Nothing
    uni' trace bind1 bind2 (Record b1 fields1) (Record b2 fields2)
      | names1 == names2 = do
        unifyPairwise' trace bind1 bind2 types1 types2 >>= \case
          Just types ->
            let fields = List.zip names1 types
            in return $ Just $ Record (b1 && b2) fields
          Nothing -> return Nothing
      | otherwise = return Nothing
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni' trace bind1 bind2 (Arrow tyDom1 tyCod1) (Arrow tyDom2 tyCod2) = do
      uni' trace bind1 bind2 tyDom2 tyDom1 >>= \case
        Just tyDom -> do
          uni' trace bind1 bind2 tyCod2 tyCod1 >>= \case
            Just tyCod -> return $ Just $ Arrow tyDom tyCod
            Nothing -> return Nothing
        Nothing -> return Nothing
    uni' trace bind1 bind2 (Union t11 t12) (Union t21 t22) = do
      res1121 <- local $ uni' trace bind1 bind2 t11 t21
      res1122 <- local $ uni' trace bind1 bind2 t11 t22
      case (res1121, res1122) of
        ((Just t1121, subst, env, argOrd), _) -> do
          modifySubst (const subst)
          modifyEnv (const env)
          modifyArgOrd (const argOrd)
          res1221 <- local $ uni' trace bind1 bind2 t12 t21
          res1222 <- local $ uni' trace bind1 bind2 t12 t22
          case (res1221, res1222) of
            ((Just t1221, subst, env, argOrd), _) -> do
              modifySubst (const subst)
              modifyEnv (const env)
              modifyArgOrd (const argOrd)
              return $ Just $ union t1121 t1221
            (_, (Just t1222, subst, env, argOrd)) -> do
              modifySubst (const subst)
              modifyEnv (const env)
              modifyArgOrd (const argOrd)
              return $ Just $ union t1121 t1222
            (_, _) -> return Nothing
        (_, (Just t1122, subst, env, argOrd)) -> do
          modifySubst (const subst)
          modifyEnv (const env)
          modifyArgOrd (const argOrd)
          res1221 <- local $ uni' trace bind1 bind2 t12 t21
          res1222 <- local $ uni' trace bind1 bind2 t12 t22
          case (res1221, res1222) of
            ((Just t1221, subst, env, argOrd), _) -> do
              modifySubst (const subst)
              modifyEnv (const env)
              modifyArgOrd (const argOrd)
              return $ Just $ union t1122 t1221
            (_, (Just t1222, subst, env, argOrd)) -> do
              modifySubst (const subst)
              modifyEnv (const env)
              modifyArgOrd (const argOrd)
              return $ Just $ union t1122 t1222
            (_, _) -> return Nothing
        (_, _) -> return Nothing
    uni' trace bind1 bind2 ty (Union t1 t2) =
      uni' trace bind1 bind2 ty t1 >>= \case
        Just t' ->
          uni' trace bind1 bind2 ty t2 >>= \case
            Just t'' -> return $ Just $ union t' t''
            Nothing -> return Nothing
        Nothing -> return Nothing
    uni' trace bind1 bind2 (Union t1 t2) ty =
      uni' trace bind1 bind2 ty (Union t1 t2)
    uni' trace bind1 bind2 (Intersect t1 t2) (Intersect t3 t4) =
      uni' trace bind1 bind2 t1 (Intersect t3 t4) >>= \case
        Just ty1 ->
          uni' trace bind1 bind2 t2 (Intersect t3 t4) >>= \case
            Just ty2 -> return $ Just $ intersect ty1 ty2
            Nothing -> return $ Just ty1
        Nothing -> return Nothing
    uni' trace bind1 bind2 (Intersect t1 t2) t =
      uni' trace bind1 bind2 t1 t >>= \case
        Just ty1 ->
          uni' trace bind1 bind2 t2 t >>= \case
            Just ty2 -> return $ Just $ intersect ty1 ty2
            Nothing -> return $ Just ty1
        Nothing -> return Nothing
    uni' trace bind1 bind2 t (Intersect t1 t2) =
      uni' trace bind1 bind2 (Intersect t1 t2) t
    uni' trace bind1 bind2 IntType IntType = return $ Just IntType
    uni' trace bind1 bind2 RealType RealType = return $ Just RealType
    uni' trace bind1 bind2 StringType StringType = return $ Just StringType
    uni' trace bind1 bind2 BoolType BoolType = return $ Just BoolType
    uni' trace _ _ _ _ = return Nothing

    unifyPairwise' trace bind1 bind2 types1 types2 =
      if List.length types1 /= List.length types2 then
        return Nothing
      else foldrM f (Just []) (List.zip types1 types2)
      where f (t1, t2) (Just types) =
              uni' trace bind1 bind2 t1 t2 >>= \case
                Just t -> return $ Just $ t : types
                Nothing -> return Nothing
            f _ Nothing = return Nothing
  in uni' Set.empty Map.empty Map.empty t1 t2
