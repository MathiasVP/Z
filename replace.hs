{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Replace where
import Types
import TypeUtils
import TypedAst
import Control.Monad.State.Lazy
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map()
import Unique

replaceType :: Substitution -> Type -> Type
replaceType subst ty =
  let replace :: Set UniqueInt -> Type -> State (Set UniqueInt) Type
      replace _ IntType = return IntType
      replace _ BoolType = return BoolType
      replace _ StringType = return StringType
      replace _ RealType = return RealType
      replace trace (Name s types) =
        fmap (Name s) (mapM (replace trace) types)
      replace trace (Array ty) = fmap Array (replace trace ty)
      replace trace (Tuple [ty]) = replace trace ty
      replace trace (Tuple types) =
        fmap Tuple (mapM (replace trace) types)
      replace trace (Record b fields) =
        fmap (Record b) (mapM field fields)
        where field (s, ty) = replace trace ty >>= \ty -> return (s, ty)
      replace trace (Arrow tDom tCod) = do
        tDom' <- replace trace tDom
        tCod' <- replace trace tCod
        return $ Arrow tDom' tCod'
      replace trace (Union t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ union t1' t2'
      replace trace (Intersect t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ intersect t1' t2'
      replace trace (Forall u ty) = do
        free <- get
        put (Set.insert u free)
        ty' <- replace trace ty
        return $ Forall u ty'
      replace trace (TypeVar u)
        | Set.member u trace = return $ TypeVar u
        | otherwise =
          gets (Set.member u) >>= \case
            True -> return $ TypeVar u
            False ->
              case Map.lookup u subst of
                Just ty -> replace (Set.insert u trace) ty
                Nothing -> return $ TypeVar u
      replace _ Error = return Error
  in evalState (replace Set.empty ty) Set.empty

replaceDecl :: Substitution -> TypedDecl -> TypedDecl
replaceDecl subst td =
  case td of
    TTypeDecl s targs t ->
      TTypeDecl s targs (replaceType subst t)
    TFunDecl name targs args retTy s ->
      TFunDecl name targs (List.map (replaceMatchExpr subst) args)
                          (replaceType subst retTy) (replaceStatement subst s)

replaceMatchExpr :: Substitution -> TypedMatchExpr -> TypedMatchExpr
replaceMatchExpr subst (tme, ty) =
  let replace (TTupleMatchExpr tmes, ty) =
        let ty' = replaceType subst ty
        in (TTupleMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
      replace (TListMatchExpr tmes, ty) =
        let ty' = replaceType subst ty
        in (TListMatchExpr (List.map (replaceMatchExpr subst) tmes), ty')
      replace (TRecordMatchExpr fields, ty) =
        let ty' = replaceType subst ty
            f (s, tme) = (s, replaceMatchExpr subst tme)
        in (TRecordMatchExpr (List.map f fields), ty')
      replace (tme, ty) = (tme, replaceType subst ty)
  in replace (tme, ty)

replaceStatement :: Substitution -> TypedStatement -> TypedStatement
replaceStatement subst ts =
  let replace (TIfStatement te ts tsm) =
        TIfStatement (replaceExpr subst te) (replace ts)
                     (fmap replace tsm)
      replace (TWhileStatement te ts) =
        TWhileStatement (replaceExpr subst te) (replace ts)
      replace (TForStatement tme te ts) =
        TForStatement (replaceMatchExpr subst tme)
                      (replaceExpr subst te) (replace ts)
      replace (TCompoundStatement tss) =
        TCompoundStatement (List.map replace tss)
      replace (TAssignStatement tme_tlve te) =
        TAssignStatement (either (Left . replaceMatchExpr subst)
                                 (Right . replaceLValueExpr subst) tme_tlve)
                         (replaceExpr subst te)
      replace (TMatchStatement te actions) =
        let f (tme, ts) = (replaceMatchExpr subst tme, replace ts)
        in TMatchStatement (replaceExpr subst te) (List.map f actions)
      replace (TReturnStatement tem) =
        TReturnStatement (replaceExpr subst tem)
      replace TBreakStatement = TBreakStatement
      replace TContinueStatement = TContinueStatement
      replace (TDeclStatement td) = TDeclStatement (replaceDecl subst td)
  in replace ts

replaceExpr :: Substitution -> TypedExpr -> TypedExpr
replaceExpr subst (te, ty) =
  let replace (TIntExpr n, ty) = (TIntExpr n, replaceType subst ty)
      replace (TRealExpr d, ty) = (TRealExpr d, replaceType subst ty)
      replace (TBoolExpr b, ty) = (TBoolExpr b, replaceType subst ty)
      replace (TStringExpr s, ty) = (TStringExpr s, replaceType subst ty)
      replace (TOrExpr te1 te2, ty) =
        (TOrExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TAndExpr te1 te2, ty) =
        (TAndExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TEqExpr te1 te2, ty) =
        (TEqExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TNeqExpr te1 te2, ty) =
        (TNeqExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TLtExpr te1 te2, ty) =
        (TLtExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TGtExpr te1 te2, ty) =
        (TGtExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TLeExpr te1 te2, ty) =
        (TLeExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TGeExpr te1 te2, ty) =
        (TGeExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TAddExpr te1 te2, ty) =
        (TAddExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TSubExpr te1 te2, ty) =
        (TSubExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TMultExpr te1 te2, ty) =
        (TMultExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TDivExpr te1 te2, ty) =
        (TDivExpr (replace te1) (replace te2), replaceType subst ty)
      replace (TUnaryMinusExpr te, ty) =
        (TUnaryMinusExpr (replace te), replaceType subst ty)
      replace (TBangExpr te, ty) =
        (TBangExpr (replace te), replaceType subst ty)
      replace (TCallExpr teFun teArg, ty) =
        (TCallExpr (replace teFun) (replace teArg), replaceType subst ty)
      replace (TListExpr tes, ty) =
        (TListExpr (List.map replace tes), replaceType subst ty)
      replace (TTupleExpr tes, ty) =
        (TTupleExpr (List.map replace tes), replaceType subst ty)
      replace (TRecordExpr fields, ty) =
        (TRecordExpr (List.map f fields), ty')
        where f (s, te) = (s, replace te)
              ty' = replaceType subst ty
      replace (TLValue tlve, ty) =
        (TLValue (replaceLValueExpr subst tlve), replaceType subst ty)

      replace (TLambdaExpr tmes ts, ty) =
        (TLambdaExpr (List.map (replaceMatchExpr subst) tmes)
                    (replaceStatement subst ts), replaceType subst ty)
  in replace (te, ty)

replaceLValueExpr :: Substitution -> TypedLValueExpr -> TypedLValueExpr
replaceLValueExpr subst (tlve, ty) =
  let replace (TVarExpr s, ty) =
        let ty' = replaceType subst ty
        in (TVarExpr s, ty')
      replace (TFieldAccessExpr tlve s, ty) =
        let ty' = replaceType subst ty
        in (TFieldAccessExpr (replace tlve) s, ty')
      replace (TArrayAccessExpr tlve te, ty) =
        let ty' = replaceType subst ty
        in (TArrayAccessExpr (replace tlve) (replaceExpr subst te), ty')
  in replace (tlve, ty)
