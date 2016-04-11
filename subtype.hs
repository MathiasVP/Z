{-# LANGUAGE LambdaCase #-}

module Subtype where
import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.State.Lazy
import Data.Map (Map)
import Data.Map ((!))
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Types
import TypeUtils
import TypedAst

data Variance
  = Positive
  | Negative
  | Top
  | Bottom

lub :: Variance -> Variance -> Variance
lub Positive Positive = Positive
lub Negative Negative = Negative
lub v Bottom = v
lub Bottom v = v
lub _ _ = Top

lubs :: [Variance] -> Variance
lubs = List.foldr lub Bottom

invert :: Variance -> Variance
invert Positive = Negative
invert Negative = Positive
invert v = v

maxNumberOfUnrolls = 100

variance :: Type -> String -> Infer Variance
variance t s =
  let var trace v (Name s' tys)
        | Set.member s' trace = return v
        | otherwise = do
          env <- environment
          argOrd <- argumentOrder
          case Map.lookup (stringOf s') env of
            Just (_, ty) ->
              let order = argOrd ! stringOf s'
                  names = List.map (order !) [0..]
                  ty' = instansiates ty (Map.fromList (List.zip names tys))
              in var (Set.insert s' trace) v ty'
            Nothing
              | s == stringOf s'   -> return $ lub v Positive
              | otherwise          -> return v
      var trace v (Arrow t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ lub (invert v1) v2
      var trace v (Forall u ty) = var trace v ty
      var trace v (Union t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ lub v1 v2
      var trace v (Tuple ts) = do
        vs <- mapM (var trace v) ts
        return $ lubs vs
      var trace v (Record b fields) = do
        vs <- mapM (var trace v . snd) fields
        return $ lubs vs
      var trace v (Array ty) = var trace v ty
      var trace v (Intersect t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ lub v1 v2
      var trace v _ = return v
  in var Set.empty Bottom t

lookup :: Bindings -> Identifier -> Infer Type
lookup bind s = do
  env <- environment
  case Map.lookup (stringOf s) env of
    Just (_, ty) -> return ty
    Nothing -> return $ bind ! stringOf s

subtype :: Type -> Type -> Infer Bool
subtype t1 t2 =
  let
    updateOrElse f def k map =
      case Map.lookup k map of
        Just a -> Map.insert k (f a) map
        Nothing -> Map.insert k def map

    sub :: Map Identifier Int -> Bindings -> Bindings ->
             Map (Identifier, Identifier) ([Type], [Type]) ->
               Type -> Type -> Infer Bool
    sub trace bind1 bind2 assum (Forall u t1) t2 =
      do TypeVar u' <- lift mkTypeVar
         sub trace bind1 bind2 assum (rename u' u t1) t2
    sub trace bind1 bind2 assum t1 (Forall u t2) =
      do TypeVar u' <- lift mkTypeVar
         sub trace bind1 bind2 assum t1 (rename u' u t2)
    sub trace bind1 bind2 assum t1 t2@(TypeVar u) =
      follow t2 >>= \case
        TypeVar u -> do
          t1' <- follow t1
          modifySubst (Map.insert u t1')
          return True
        ty -> sub trace bind1 bind2 assum t1 ty
    sub trace bind1 bind2 assum t1@(TypeVar u) t2 =
      follow t1 >>= \case
        TypeVar u -> do
          t2' <- follow t2
          modifySubst (Map.insert u t2')
          return True
        ty -> sub trace bind1 bind2 assum ty t2
    sub trace bind1 bind2 assum (Name s1 tys1) (Name s2 tys2) =
      case Map.lookup (s1, s2) assum of
        Just (tys1', tys2') -> do
          ty1 <- lookup bind1 s1
          ty2 <- lookup bind2 s2
          vars1 <- mapM (variance ty1) (Map.keys bind1)
          vars2 <- mapM (variance ty2) (Map.keys bind2)
          b1 <- foldM f True (List.zip3 tys1' tys2' vars1)
          foldM f b1 (List.zip3 tys1' tys2' vars1)
        Nothing
          | s1 == s2 && Map.notMember (stringOf s1) bind1 &&
            Map.notMember (stringOf s2) bind2 -> do
              env <- environment
              let (_, ty) = env ! stringOf s1
              vars <- mapM (variance ty) (Map.keys bind1)
              foldM f True (List.zip3 tys1 tys2 vars)
          | otherwise -> do
              t1 <- lookup bind1 s1
              t2 <- lookup bind2 s2
              let assum' = Map.insert (s1, s2) (tys1, tys2) assum
              sub trace bind1 bind2 assum' t1 t2
       where f True (t1, t2, Top) = do
               b1 <- sub trace bind1 bind2 assum t1 t2
               b2 <- sub trace bind1 bind2 assum t2 t1
               return (b1 && b2)
             f True (t1, t2, Positive) = sub trace bind1 bind2 assum t1 t2
             f True (t1, t2, Negative) = sub trace bind1 bind2 assum t2 t1
             f True (t1, t2, Bottom) = return True
             f False _ = return False
    sub trace bind1 bind2 assum (Name s tys) ty =
      case Map.lookup s trace of
        Just n -> return $ n < maxNumberOfUnrolls
        Nothing -> do
          t <- lookup bind1 s
          bind1' <- makeBindings s tys
          sub (updateOrElse (+1) 0 s trace) bind1' bind2 assum t ty
    sub trace bind1 bind2 assum ty (Name s tys) =
      case Map.lookup s trace of
        Just n -> return $ n < maxNumberOfUnrolls
        Nothing -> do
          t <- lookup bind2 s
          bind2' <- makeBindings s tys
          sub (updateOrElse (+1) 0 s trace) bind1 bind2' assum ty t
{-    sub trace bind1 bind2 assum subst (Union t11 t12) (Union t21 t22) = do
      (b1121, subst1121) <- sub trace bind1 bind2 assum subst t11 t21
      (b1221, subst1221) <- sub trace bind1 bind2 assum subst1121 t12 t21
      (b1222, subst1222) <- sub trace bind1 bind2 assum subst1121 t12 t22

      (b1122, subst1122) <- sub trace bind1 bind2 assum subst t11 t22
      (b1221', subst1221') <- sub trace bind1 bind2 assum subst1122 t12 t21
      (b1222', subst1222') <- sub trace bind1 bind2 assum subst1122 t12 t22
      if b1121 && b1221 then return (True, subst1221)
      else if b1121 && b1222 then return (True, subst1222)
      else if b1122 && b1221' then return (True, subst1221')
      else if b1122 && b1222' then return (True, subst1222')
      else return (False, subst)
    sub trace bind1 bind2 assum subst (Union t1 t2) ty = do
      (b1, subst') <- sub trace bind1 bind2 assum subst t1 ty
      (b2, subst'') <- sub trace bind1 bind2 assum subst' t2 ty
      return (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst ty (Union t1 t2) = do
      (b1, subst') <- sub trace bind1 bind2 assum subst ty t1
      (b2, subst'') <- sub trace bind1 bind2 assum subst' ty t2
      return (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst (Arrow tDom1 tCod1) (Arrow tDom2 tCod2) = do
      (b1, subst') <- sub trace bind1 bind2 assum subst tDom1 tDom2
      (b2, subst'') <- sub trace bind1 bind2 assum subst' tCod2 tCod1
      return (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst (Tuple [t1]) t2 =
      sub trace bind1 bind2 assum subst t1 t2
    sub trace bind1 bind2 assum subst t1 (Tuple [t2]) =
      sub trace bind1 bind2 assum subst t1 t2
    sub trace bind1 bind2 assum subst (Tuple tys1) (Tuple tys2) =
      if List.length tys1 == List.length tys2 then
        foldM f (True, subst) (List.zip tys1 tys2)
      else return (False, subst)
      where f (True, subst) (t1, t2) = sub trace bind1 bind2 assum subst t1 t2
            f (False, subst) _ = return (False, subst)
    sub trace bind1 bind2 assum subst (Array t1) (Array t2) =
      sub trace bind1 bind2 assum subst t1 t2
    sub trace bind1 bind2 assum subst (Record _ fields1) (Record mut2 fields2) =
      foldM f (True, subst) fields1
      where f :: (Bool, Substitution) -> (String, Type) -> IO (Bool, Substitution)
            f (_, subst) (name, ty) =
             case List.lookup name fields2 of
              Just ty' -> sub trace bind1 bind2 assum subst ty ty'
              Nothing -> return (mut2, subst)
    sub trace bind1 bind2 assum subst (Intersect t1 t2) ty = do
      (b1, subst') <- sub trace bind1 bind2 assum subst t1 ty
      (b2, subst'') <- sub trace bind1 bind2 assum subst' t2 ty
      return (b1 && b2, subst'')
    sub trace bind1 bind2 assum subst ty (Intersect t1 t2) = do
      (b1, subst') <- sub trace bind1 bind2 assum subst ty t1
      (b2, subst'') <- sub trace bind1 bind2 assum subst' ty t2
      return (b1 || b2, subst'')
    sub trace bind1 bind2 _ subst IntType IntType = return (True, subst)
    sub trace bind1 bind2 _ subst IntType RealType = return (True, subst)
    sub trace bind1 bind2 _ subst RealType RealType = return (True, subst)
    sub trace bind1 bind2 _ subst BoolType BoolType = return (True, subst)
    sub trace bind1 bind2 _ subst StringType StringType = return (True, subst)
    sub trace bind1 bind2 _ _ _ _ = return False-}
  in sub Map.empty Map.empty Map.empty Map.empty t1 t2
