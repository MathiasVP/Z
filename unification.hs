{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Unification where
import Prelude hiding (lookup)
import Control.Monad
import Data.Foldable
import Data.Ord
import Control.Monad.State.Lazy
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.List as List
import Data.Set (Set)
import Data.Map (Map)

--import Data.Map ((!))
import TTypes
import Ast()
import TypedAst()
import TypeUtils

(!) :: (Ord a, Show a, Show b) => Map a b -> a -> b
(!) m k = fromMaybe (error $ show k ++ " ∉ " ++ show m) (Map.lookup k m)

makeRecord :: Bool -> [(String, TType)] -> Infer TType
makeRecord b fields = do
  u <- liftIO mkTypeVar
  unify u (TRecord b fields)
  return u

unifyTypes :: [TType] -> Infer TType
unifyTypes types = do
  t <- liftIO mkTypeVar
  foldM unify t types

inserts :: Ord a => Set a -> [a] -> Set a
inserts = List.foldr Set.insert

unify :: TType -> TType ->  Infer TType
unify t1 t2 =
  let
    uni :: Trace -> Bindings -> Bindings -> TType -> TType -> Infer TType
    uni trace bind1 bind2 (TTypeVar u) (TTypeVar u') = do
      t <- follow (TTypeVar u)
      t' <- follow (TTypeVar u')
      case (t, t') of
        (TTypeVar u, TTypeVar u') -> do
          modifySubst (Map.insert u (TTypeVar u'))
          return $ TTypeVar u'
        (TTypeVar u, t) -> do
          modifySubst (Map.insert u t)
          return t
        (t, TTypeVar u') -> do
          modifySubst (Map.insert u' t)
          return t
        (t, t') ->
          uni trace bind1 bind2 t t'
    uni trace bind1 bind2 (TForall u t1) t2 = do
      t <- liftIO mkTypeVar
      uni trace (Map.insert u t bind1) bind2 t1 t2
    uni trace bind1 bind2 t1 (TForall u t2) =
      uni trace bind2 bind1 (TForall u t2) t1
    uni trace bind1 bind2 (TTypeVar u) t = do
      follow (TTypeVar u) >>= \case
        TTypeVar u -> do
          modifySubst (Map.insert u t)
          return t
        t' -> do
          t'' <- uni trace bind1 bind2 t t'
          modifySubst (Map.insert u t'')
          return t''
    uni trace bind1 bind2 t (TTypeVar u) = uni trace bind2 bind1 (TTypeVar u) t
    uni trace bind1 bind2 (TMu ident1 ty1) (TMu ident2 ty2) = do
      modifySubst $ Map.insert ident1 (TTypeVar ident2)
      TMu ident1 <$> (uni trace bind1 bind2 ty1 ty2)
    uni trace bind1 bind2 (TArray t1) (TArray t2) =
      fmap TArray (uni trace bind1 bind2 t1 t2)
    uni trace bind1 bind2 (TTuple [t1]) (TTuple [t2]) = do
      t <- uni trace bind1 bind2 t1 t2
      return $ TTuple [t]
    uni trace bind1 bind2 (TTuple [t1]) t2 =
      uni trace bind1 bind2 t1 t2
    uni trace bind1 bind2 t1 (TTuple [t2]) =
      uni trace bind2 bind1 (TTuple [t2]) t1
    uni trace bind1 bind2 (TTuple types1) (TTuple types2) =
      if List.length types1 == List.length types2 then do
        types <- unifyPairwise trace bind1 bind2 types1 types2
        return $ TTuple types
      else return $ tunion (TTuple types1) (TTuple types2)
    uni trace bind1 bind2 (TRecord b1 fields1) (TRecord b2 fields2) = do
      types <- unifyPairwise trace bind1 bind2 types1 types2
      let fields = List.zip names1 types
      if names1 == names2 then
        return $ TRecord (b1 && b2) fields
      else return $ tunion (TRecord b1 fields1) (TRecord b2 fields2)
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni trace bind1 bind2 (TArrow tyDom1 tyCod1) (TArrow tyDom2 tyCod2) = do
      tyDom <- uni trace bind1 bind2 tyDom1 tyDom2
      tyCod <- uni trace bind1 bind2 tyCod1 tyCod2
      return $ TArrow tyDom tyCod
    uni trace bind1 bind2 (TUnion t1 t2) (TUnion t3 t4) = do
      t13 <- uni trace bind1 bind2 t1 t3
      t24 <- uni trace bind1 bind2 t2 t4
      return $ tunion t13 t24
    uni _ _ _ TNumber TNumber = return TNumber
    uni _ _ _ TNumber TIntType = return TIntType
    uni _ _ _ TNumber TRealType = return TRealType
    uni _ _ _ TIntType TNumber = return TIntType
    uni _ _ _ TRealType TNumber = return TRealType
    uni _ _ _ TIntType TIntType = return TIntType
    uni _ _ _ TRealType TRealType = return TRealType
    uni _ _ _ TStringType TStringType = return TStringType
    uni _ _ _ TBoolType TBoolType = return TBoolType
    uni _ _ _ t1 t2 = return $ tunion t1 t2

    unifyPairwise trace bind1 bind2 types1 types2 =
      let types = List.zip types1 types2
      in mapM (uncurry $ uni trace bind1 bind2) types
  in uni Set.empty Map.empty Map.empty t1 t2

unify' :: TType -> TType -> Infer (Maybe TType)
unify' t1 t2 =
  let
    uni' :: Trace -> Bindings -> Bindings ->
             TType -> TType -> Infer (Maybe TType)
    uni' trace bind1 bind2 (TTypeVar u) (TTypeVar u') = do
      t <- follow (TTypeVar u)
      t' <- follow (TTypeVar u')
      case (t, t') of
        (TTypeVar u, TTypeVar u') -> do
          modifySubst (Map.insert u (TTypeVar u'))
          return $ Just (TTypeVar u')
        (TTypeVar u, t) -> do
          modifySubst (Map.insert u t)
          return $ Just t
        (t, TTypeVar u') -> do
          modifySubst (Map.insert u' t)
          return $ Just t
        (t, t') -> uni' trace bind1 bind2 t t'
    uni' trace bind1 bind2 (TForall _ t1) t2 =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 t1 (TForall u t2) =
      uni' trace bind2 bind1 (TForall u t2) t1
    uni' trace bind1 bind2 (TTypeVar u) t =
      follow (TTypeVar u) >>= \case
        TTypeVar u -> do
          modifySubst (Map.insert u t)
          return $ Just t
        t' -> uni' trace bind1 bind2 t' t >>= \case
                Just t'' -> do
                  modifySubst (Map.insert u t'' )
                  return $ Just t''
                Nothing -> return Nothing
    uni' trace bind1 bind2 t (TTypeVar u) =
      uni' trace bind2 bind1 (TTypeVar u) t
    uni' trace bind1 bind2 t1@(TMu ident1 ty1) t2@(TMu ident2 ty2) = do
      modifySubst $ Map.insert ident1 (TTypeVar ident2)
      uni' trace bind1 bind2 ty1 ty2
    uni' trace bind1 bind2 (TArray t1) (TArray t2) =
      uni' trace bind1 bind2 t1 t2 >>= \case
        Just t -> return . Just $ TArray t
        Nothing -> return Nothing
    uni' trace bind1 bind2 (TTuple [t1]) (TTuple [t2]) =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 (TTuple [t1]) t2 =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 t1 (TTuple [t2]) =
      uni' trace bind1 bind2 t1 t2
    uni' trace bind1 bind2 (TTuple types1) (TTuple types2) =
      unifyPairwise' trace bind1 bind2 types1 types2 >>= \case
        Just types -> return $ Just $ TTuple types
        Nothing -> return Nothing
    uni' trace bind1 bind2 (TRecord b1 fields1) (TRecord b2 fields2)
      | names1 == names2 =
        unifyPairwise' trace bind1 bind2 types1 types2 >>= \case
          Just types ->
            let fields = List.zip names1 types
            in return $ Just $ TRecord (b1 && b2) fields
          Nothing -> return Nothing
      | otherwise = return Nothing
      where fields1' = List.sortBy (comparing fst) fields1
            fields2' = List.sortBy (comparing fst) fields2
            (names1, types1) = List.unzip fields1'
            (names2, types2) = List.unzip fields2'
    uni' trace bind1 bind2 (TArrow tyDom1 tyCod1) (TArrow tyDom2 tyCod2) =
      uni' trace bind1 bind2 tyDom2 tyDom1 >>= \case
        Just tyDom ->
          uni' trace bind1 bind2 tyCod2 tyCod1 >>= \case
            Just tyCod -> return $ Just $ TArrow tyDom tyCod
            Nothing -> return Nothing
        Nothing -> return Nothing
    uni' trace bind1 bind2 (TUnion t11 t12) (TUnion t21 t22) = do
      res1121 <- local $ uni' trace bind1 bind2 t11 t21
      res1122 <- local $ uni' trace bind1 bind2 t11 t22
      case (res1121, res1122) of
        ((Just t1121, st), _) -> do
          modifySubst (const (subst st))
          modifyEnv (const (env st))
          res1221 <- local $ uni' trace bind1 bind2 t12 t21
          res1222 <- local $ uni' trace bind1 bind2 t12 t22
          case (res1221, res1222) of
            ((Just t1221, st), _) -> do
              modifySubst (const (subst st))
              modifyEnv (const (env st))
              return $ Just $ tunion t1121 t1221
            (_, (Just t1222, st)) -> do
              modifySubst (const (subst st))
              modifyEnv (const (env st))
              return $ Just $ tunion t1121 t1222
            (_, _) -> return Nothing
        (_, (Just t1122, st)) -> do
          modifySubst (const (subst st))
          modifyEnv (const (env st))
          res1221 <- local $ uni' trace bind1 bind2 t12 t21
          res1222 <- local $ uni' trace bind1 bind2 t12 t22
          case (res1221, res1222) of
            ((Just t1221, st), _) -> do
              modifySubst (const (subst st))
              modifyEnv (const (env st))
              return $ Just $ tunion t1122 t1221
            (_, (Just t1222, st)) -> do
              modifySubst (const (subst st))
              modifyEnv (const (env st))
              return $ Just $ tunion t1122 t1222
            (_, _) -> return Nothing
        (_, _) -> return Nothing
    uni' trace bind1 bind2 ty (TUnion t1 t2) =
      uni' trace bind1 bind2 ty t1 >>= \case
        Just t' ->
          uni' trace bind1 bind2 ty t2 >>= \case
            Just t'' -> return $ Just $ tunion t' t''
            Nothing -> return Nothing
        Nothing -> return Nothing
    uni' trace bind1 bind2 (TUnion t1 t2) ty =
      uni' trace bind2 bind1 ty (TUnion t1 t2)
    uni' _ _ _ TNumber TNumber = return $ Just TNumber
    uni' _ _ _ TNumber TIntType = return $ Just TIntType
    uni' _ _ _ TNumber TRealType = return $ Just TRealType
    uni' _ _ _ TIntType TNumber = return $ Just TIntType
    uni' _ _ _ TRealType TNumber = return $ Just TRealType
    uni' _ _ _ TIntType TIntType = return $ Just TIntType
    uni' _ _ _ TIntType TRealType = return $ Just TRealType
    uni' _ _ _ TRealType TIntType = return $ Just TRealType
    uni' _ _ _ TRealType TRealType = return $ Just TRealType
    uni' _ _ _ TStringType TStringType = return $ Just TStringType
    uni' _ _ _ TBoolType TBoolType = return $ Just TBoolType
    uni' _ _ _ _ _ = return Nothing

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
