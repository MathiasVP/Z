{-# LANGUAGE LambdaCase, StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Subtype(subtype) where

import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Loops
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set()
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe
import TTypes
import TypeUtils
import TypedAst()

(!) :: (Ord a, Show a, Show b) => Map a b -> a -> b
(!) m k = fromMaybe (error $ show k ++ " ∉ " ++ show m) (Map.lookup k m)

class Lattice a where
  (\/) :: a -> a -> a
  (/\) :: a -> a -> a
  bot :: a
  top :: a

data Variance
  = Positive
  | Negative
  | Top
  | Bottom

instance Lattice Variance where
  (\/) Positive Positive = Positive
  (\/) Negative Negative = Negative
  (\/) v Bottom = v
  (\/) Bottom v = v
  (\/) _ _ = Top

  (/\) Positive Positive = Positive
  (/\) Negative Negative = Negative
  (/\) v Top = v
  (/\) Top v = v
  (/\) _ _ = Bottom

  bot = Bottom
  top = Top

lubs :: Lattice a => [a] -> a
lubs = List.foldr (\/) bot

invert :: Variance -> Variance
invert Positive = Negative
invert Negative = Positive
invert v = v

maxNumberOfUnrolls :: Int
maxNumberOfUnrolls = 10

variance :: TType -> Identifier -> Infer Variance
variance t s =
  let var trace v (TName s' tys)
        | Set.member s' trace = return v
        | otherwise = do
          env <- environment
          argOrd <- argumentOrder
          case Map.lookup (stringOf s') env of
            Just (_, ty) ->
              let order = argOrd ! s'
                  names = List.map (order !) [0..]
                  ty' = instansiates ty (Map.fromList (List.zip names tys))
              in var (Set.insert s' trace) v ty'
            Nothing
              | s == s'   -> return $ v \/ Positive
              | otherwise -> return v
      var trace v (TArrow t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ invert v1 \/ v2
      var trace v (TForall _ ty) = var trace v ty
      var trace v (TUnion t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ v1 \/ v2
      var trace v (TTuple ts) = do
        vs <- mapM (var trace v) ts
        return $ lubs vs
      var trace v (TRecord _ fields) = do
        vs <- mapM (var trace v . snd) fields
        return $ lubs vs
      var trace v (TArray ty) = var trace v ty
      var trace v (TIntersect t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ v1 \/ v2
      var _ v _ = return v
  in var Set.empty Bottom t

lookup :: Bindings -> Identifier -> Infer TType
lookup bind s = do
  env <- environment
  case Map.lookup (stringOf s) env of
    Just (_, ty) -> return ty
    Nothing -> return $ bind ! s

data TypeCost
  = Free
  | Cost Integer
  | Impossible
  deriving (Eq, Show, Ord)

instance Lattice TypeCost where
  (\/) Free r = r
  (\/) r Free = r
  (\/) Impossible _ = Impossible
  (\/) _ Impossible = Impossible
  (\/) (Cost n) (Cost m) = Cost (n + m)

  (/\) Free _ = Free
  (/\) _ Free = Free
  (/\) Impossible x = x
  (/\) x Impossible = x
  (/\) (Cost n) (Cost m) = Cost (n - m)

  bot = Free
  top = Impossible


subtype :: TType -> TType -> Infer (Maybe TType)
subtype t1 t2 =
  let
    updateOrElse f def k map =
      case Map.lookup k map of
        Just a -> Map.insert k (f a) map
        Nothing -> Map.insert k def map

    sub :: Map Identifier Int -> Bindings -> Bindings ->
               TType -> TType -> Infer (TypeCost, TType)
    sub trace bind1 bind2 (TForall u t1) t2 =
      do TTypeVar u' <- lift mkTypeVar
         (c, t) <- sub trace bind1 bind2 (rename u' u t1) t2
         free (TTypeVar u') >>= \case
          True -> return (c, t)
          False -> return (c, TForall u' t) {- TODO: This doesn't really make sense? -}
    sub trace bind1 bind2 t1 (TForall u t2) =
      do TTypeVar u' <- lift mkTypeVar
         (c, t) <- sub trace bind1 bind2 t1 (rename u' u t2)
         free (TTypeVar u') >>= \case
          True -> return (c, TForall u' t)
          False -> return (c, t)
    sub trace bind1 bind2 t1 t2@(TTypeVar _) =
      follow t2 >>= \case
        TTypeVar u -> do
          t1' <- follow t1
          modifySubst (Map.insert u t1')
          return (Cost 1, TTypeVar u)
        ty -> sub trace bind1 bind2 t1 ty
    sub trace bind1 bind2 t1@(TTypeVar _) t2 =
      follow t1 >>= \case
        TTypeVar u -> do
          t2' <- follow t2
          modifySubst (Map.insert u t2')
          return (Cost 1, TTypeVar u)
        ty -> sub trace bind1 bind2 ty t2
    sub trace bind1 bind2 (TName s1 tys1) (TName s2 tys2) =
      if s1 == s2 && Map.notMember s1 bind1 && Map.notMember s2 bind2 then do
          env <- environment
          let (_, ty) = env ! stringOf s1
          vars <- mapM (variance ty) (Map.keys bind1)
          (c, tys) <- foldM f (Free, []) (List.zip3 tys1 tys2 vars)
          return (c, TName s1 tys)
      else do
          t1 <- lookup bind1 s1
          t2 <- lookup bind2 s2
          sub trace bind1 bind2 t1 t2
       where f (c, ts) (t1, t2, Positive) | c /= Impossible = do
               (c', t) <- sub trace bind1 bind2 t1 t2
               return (c \/ c', ts ++ [t])
             f (c, ts) (t1, t2, Negative) | c /= Impossible = do
               (c', t) <- sub trace bind1 bind2 t2 t1
               return (c \/ c', ts ++ [t])
             f (c, t) (_, _, Bottom) = return (c, t)
             f (_, t) _ = return (Impossible, t)
    sub trace bind1 bind2 (TName s tys) ty =
      case Map.lookup s trace of
        Just n | n >= maxNumberOfUnrolls -> return (Impossible, TError)
        _ -> do
          t <- lookup bind1 s
          bind1' <- makeBindings s bind1 tys
          sub (updateOrElse (+1) 0 s trace) bind1' bind2 t ty
    sub trace bind1 bind2 ty (TName s tys) =
      case Map.lookup s trace of
        Just n | n >= maxNumberOfUnrolls -> return (Impossible, TError)
        _ -> do
          t <- lookup bind2 s
          bind2' <- makeBindings s bind2 tys
          sub (updateOrElse (+1) 0 s trace) bind1 bind2' ty t
    sub trace bind1 bind2 (TUnion t11 t12) (TUnion t21 t22) = do
      let poss =
            [(sub trace bind1 bind2 t11 t21, sub trace bind1 bind2 t12 t21),
             (sub trace bind1 bind2 t11 t21, sub trace bind1 bind2 t12 t22),
             (sub trace bind1 bind2 t11 t22, sub trace bind1 bind2 t12 t21),
             (sub trace bind1 bind2 t11 t22, sub trace bind1 bind2 t12 t22)]
      st <- get
      Just (inl, inr) <- liftIO $ minimumOnM (\(inl, inr) -> do
                ((c1, _), st') <- runInfer inl st
                ((c2, _), _) <- runInfer inr st'
                return $ c1 \/ c2) poss
      (c1, inl') <- inl
      (c2, inr') <- inr
      return (c1 \/ c2, tunion inl' inr')
    sub trace bind1 bind2 (TUnion t1 t2) ty = do
      st <- get
      (r1, st1) <- liftIO $ runInfer (sub trace bind1 bind2 t1 ty) st
      (r2, st2) <- liftIO $ runInfer (sub trace bind1 bind2 t2 ty) st
      if fst r1 < fst r2 then modify (const st1) >> return r1
      else modify (const st2) >> return r2
    sub trace bind1 bind2 ty (TUnion t1 t2) = do
      (c1, t1') <- sub trace bind1 bind2 ty t1
      (c2, t2') <- sub trace bind1 bind2 ty t2
      return (c1 /\ c2, tunion t1' t2')
    sub trace bind1 bind2 (TArrow tDom1 tCod1) (TArrow tDom2 tCod2) = do
      (c1, tDom) <- sub trace bind1 bind2 tDom1 tDom2
      (c2, tCod) <- sub trace bind1 bind2 tCod2 tCod1
      return (c1 \/ c2, TArrow tDom tCod)
    sub trace bind1 bind2 (TTuple [t1]) t2 =
      sub trace bind1 bind2 t1 t2
    sub trace bind1 bind2 t1 (TTuple [t2]) =
      sub trace bind1 bind2 t1 t2
    sub trace bind1 bind2 (TTuple tys1) (TTuple tys2) =
      if List.length tys1 == List.length tys2 then do
        (c, ts) <- foldM (\(c, ts) (t1, t2) -> do
          (c', t) <- sub trace bind1 bind2 t1 t2
          return (c \/ c', ts ++ [t])) (Free, []) (List.zip tys1 tys2)
        return (c, TTuple ts)
      else return (Impossible, TError)
    sub trace bind1 bind2 (TArray t1) (TArray t2) =
      sub trace bind1 bind2 t1 t2
    sub trace bind1 bind2 (TRecord _ fields1) (TRecord mut2 fields2) = do
      (c, fields) <- foldM f (Free, []) fields1
      return (c, TRecord mut2 fields)
      where f (c, fields) (name, ty) =
             case List.lookup name fields2 of
              Just ty' -> do
                (c', ty'') <- sub trace bind1 bind2 ty ty'
                return (c \/ c', fields ++ [(name, ty'')])
              Nothing -> return $ if mut2 then (c, fields)
                                  else (Impossible, fields ++ [(name, TError)])
    sub trace bind1 bind2 (TIntersect t1 t2) ty = do
      (c1, t1') <- sub trace bind1 bind2 ty t1
      (c2, t2') <- sub trace bind1 bind2 ty t2
      return (c1 /\ c2, tunion t1' t2')
    sub trace bind1 bind2 ty (TIntersect t1 t2) = do
      st <- get
      (r1, st1) <- liftIO $ runInfer (sub trace bind1 bind2 ty t1) st
      (r2, st2) <- liftIO $ runInfer (sub trace bind1 bind2 ty t2) st
      if fst r1 < fst r2 then modify (const st1) >> return r1
      else modify (const st2) >> return r2
    sub _ _ _ TIntType TIntType = return (Free, TIntType)
    sub _ _ _ TIntType TRealType = return (Free, TRealType)
    sub _ _ _ TRealType TRealType = return (Free, TRealType)
    sub _ _ _ TBoolType TBoolType = return (Free, TBoolType)
    sub _ _ _ TStringType TStringType = return (Free, TStringType)
    sub _ _ _ _ _ = return (Impossible, TError)
  in sub Map.empty Map.empty Map.empty t1 t2 >>= \case
       (Free, t) -> return $ Just t
       (Cost _, t) -> return $ Just t
       (Impossible, _) -> return Nothing
