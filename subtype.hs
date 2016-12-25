{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Subtype(subtype) where
import Prelude hiding (lookup)
import Control.Monad
import Control.Monad.State.Lazy
import Control.Monad.Loops
import Data.Map (Map, (!))
import qualified Data.Map as Map
import Data.Set()
import qualified Data.Set as Set
import qualified Data.List as List
import TTypes
import TypeUtils
import TypedAst()

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

maxNumberOfUnrolls :: Int
maxNumberOfUnrolls = 100

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
              | s == s'   -> return $ lub v Positive
              | otherwise -> return v
      var trace v (TArrow t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ lub (invert v1) v2
      var trace v (TForall _ ty) = var trace v ty
      var trace v (TUnion t1 t2) = do
        v1 <- var trace v t1
        v2 <- var trace v t2
        return $ lub v1 v2
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
        return $ lub v1 v2
      var _ v _ = return v
  in var Set.empty Bottom t

lookup :: Bindings -> Identifier -> Infer TType
lookup bind s = do
  env <- environment
  case Map.lookup (stringOf s) env of
    Just (_, ty) -> return ty
    Nothing -> return $ bind ! s

subtype :: TType -> TType -> Infer Bool
subtype t1 t2 =
  let
    updateOrElse f def k map =
      case Map.lookup k map of
        Just a -> Map.insert k (f a) map
        Nothing -> Map.insert k def map

    sub :: Map Identifier Int -> Bindings -> Bindings ->
             Map (Identifier, Identifier) ([TType], [TType]) ->
               TType -> TType -> Infer Bool
    sub trace bind1 bind2 assum (TForall u t1) t2 =
      do TTypeVar u' <- lift mkTypeVar
         sub trace bind1 bind2 assum (rename u' u t1) t2
    sub trace bind1 bind2 assum t1 (TForall u t2) =
      do TTypeVar u' <- lift mkTypeVar
         sub trace bind1 bind2 assum t1 (rename u' u t2)
    sub trace bind1 bind2 assum t1 t2@(TTypeVar _) =
      follow t2 >>= \case
        TTypeVar u -> do
          t1' <- follow t1
          modifySubst (Map.insert u t1')
          return True
        ty -> sub trace bind1 bind2 assum t1 ty
    sub trace bind1 bind2 assum t1@(TTypeVar _) t2 =
      follow t1 >>= \case
        TTypeVar u -> do
          t2' <- follow t2
          modifySubst (Map.insert u t2')
          return True
        ty -> sub trace bind1 bind2 assum ty t2
    sub trace bind1 bind2 assum (TName s1 tys1) (TName s2 tys2) =
      case Map.lookup (s1, s2) assum of
        Just (tys1', tys2') -> do
          ty1 <- lookup bind1 s1
          ty2 <- lookup bind2 s2
          vars1 <- mapM (variance ty1) (Map.keys bind1)
          vars2 <- mapM (variance ty2) (Map.keys bind2)
          b1 <- foldM f True (List.zip3 tys1' tys2' vars1)
          foldM f b1 (List.zip3 tys1' tys2' vars2)
        Nothing
          | s1 == s2 && Map.notMember s1 bind1 &&
            Map.notMember s2 bind2 -> do
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
             f True (_, _, Bottom) = return True
             f False _ = return False
    sub trace bind1 bind2 assum (TName s tys) ty =
      case Map.lookup s trace of
        Just n -> return $ n < maxNumberOfUnrolls
        Nothing -> do
          t <- lookup bind1 s
          bind1' <- makeBindings s tys
          sub (updateOrElse (+1) 0 s trace) bind1' bind2 assum t ty
    sub trace bind1 bind2 assum ty (TName s tys) =
      case Map.lookup s trace of
        Just n -> return $ n < maxNumberOfUnrolls
        Nothing -> do
          t <- lookup bind2 s
          bind2' <- makeBindings s tys
          sub (updateOrElse (+1) 0 s trace) bind1 bind2' assum ty t
    sub trace bind1 bind2 assum (TUnion t11 t12) (TUnion t21 t22) = do
      subst <- substitution
      b1121 <- sub trace bind1 bind2 assum t11 t21
      subst1121 <- substitution
      b1221 <- sub trace bind1 bind2 assum t12 t21
      if b1121 && b1221 then return True
      else do
        modifySubst (const subst1121)
        b1222 <- sub trace bind1 bind2 assum t12 t22
        if b1121 && b1222 then return True
        else do
          modifySubst (const subst)
          b1122 <- sub trace bind1 bind2 assum t11 t22
          subst1122 <- substitution
          b1221' <- sub trace bind1 bind2 assum t12 t21
          if b1122 && b1221' then return True
          else do
            modifySubst (const subst1122)
            b1222' <- sub trace bind1 bind2 assum t12 t22
            if b1122 && b1222' then return True
            else do
              modifySubst (const subst)
              return False
    sub trace bind1 bind2 assum (TUnion t1 t2) ty = do
      b1 <- sub trace bind1 bind2 assum t1 ty
      b2 <- sub trace bind1 bind2 assum t2 ty
      return $ b1 || b2
    sub trace bind1 bind2 assum ty (TUnion t1 t2) = do
      b1 <- sub trace bind1 bind2 assum ty t1
      b2 <- sub trace bind1 bind2 assum ty t2
      return $ b1 && b2
    sub trace bind1 bind2 assum (TArrow tDom1 tCod1) (TArrow tDom2 tCod2) = do
      b1 <- sub trace bind1 bind2 assum tDom1 tDom2
      b2 <- sub trace bind1 bind2 assum tCod2 tCod1
      return $ b1 && b2
    sub trace bind1 bind2 assum (TTuple [t1]) t2 =
      sub trace bind1 bind2 assum t1 t2
    sub trace bind1 bind2 assum t1 (TTuple [t2]) =
      sub trace bind1 bind2 assum t1 t2
    sub trace bind1 bind2 assum (TTuple tys1) (TTuple tys2) =
      if List.length tys1 == List.length tys2 then
        allM (uncurry $ sub trace bind1 bind2 assum) (List.zip tys1 tys2)
      else return False
    sub trace bind1 bind2 assum (TArray t1) (TArray t2) =
      sub trace bind1 bind2 assum t1 t2
    sub trace bind1 bind2 assum (TRecord _ fields1) (TRecord mut2 fields2) =
      foldM f True fields1
      where f _ (name, ty) =
             case List.lookup name fields2 of
              Just ty' -> sub trace bind1 bind2 assum ty ty'
              Nothing -> return mut2
    sub trace bind1 bind2 assum (TIntersect t1 t2) ty = do
      b1 <- sub trace bind1 bind2 assum t1 ty
      b2 <- sub trace bind1 bind2 assum t2 ty
      return $ b1 && b2
    sub trace bind1 bind2 assum ty (TIntersect t1 t2) = do
      b1 <- sub trace bind1 bind2 assum ty t1
      b2 <- sub trace bind1 bind2 assum ty t2
      return $ b1 || b2
    sub _ _ _ _ TIntType TIntType = return True
    sub _ _ _ _ TIntType TRealType = return True
    sub _ _ _ _ TRealType TRealType = return True
    sub _ _ _ _ TBoolType TBoolType = return True
    sub _ _ _ _ TStringType TStringType = return True
    sub _ _ _ _ _ _ = return False
  in sub Map.empty Map.empty Map.empty Map.empty t1 t2
