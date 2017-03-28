{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Replace where
import TTypes
import TypeUtils
import TypedAst
import Control.Monad.State.Lazy
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set(Set)
import Data.Map()

replaceType :: Substitution -> Env -> TType -> TType
replaceType subst env ty =
  let replace :: Trace -> TType -> State (Set Identifier) TType
      replace _ TIntType = return TIntType
      replace _ TBoolType = return TBoolType
      replace _ TStringType = return TStringType
      replace _ TRealType = return TRealType
      replace trace (TName s types) =
        fmap (TName s) (mapM (replace trace) types)
      replace trace (TArray ty) = fmap TArray (replace trace ty)
      replace trace (TTuple [ty]) = replace trace ty
      replace trace (TTuple types) =
        fmap TTuple (mapM (replace trace) types)
      replace trace (TRecord b fields) =
        fmap (TRecord b) (mapM field fields)
        where field (s, ty) = replace trace ty >>= \ty -> return (s, ty)
      replace trace (TArrow tDom tCod) = do
        tDom' <- replace trace tDom
        tCod' <- replace trace tCod
        return $ TArrow tDom' tCod'
      replace trace (TUnion t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ tunion t1' t2'
      replace trace (TIntersect t1 t2) = do
        t1' <- replace trace t1
        t2' <- replace trace t2
        return $ tintersect t1' t2'
      replace trace (TRef name tys) = do
        tys' <- mapM (replace trace) tys
        case Map.lookup name env of
          Just (uniq, _) -> return $ TName (Identifier (name, uniq)) tys'
          Nothing -> error $ "Undefined type name " ++ name
      replace trace (TForall ident ty) = do
        free <- get
        put (Set.insert ident free)
        ty' <- replace trace ty
        return $ TForall ident ty'
      replace trace (TTypeVar ident)
        | Set.member ident trace = return $ TTypeVar ident
        | otherwise =
          gets (Set.member ident) >>= \case
            True -> return $ TTypeVar ident
            False ->
              case Map.lookup ident subst of
                Just ty -> replace (Set.insert ident trace) ty
                Nothing -> return $ TTypeVar ident
      replace _ TError = return TError
  in evalState (replace Set.empty ty) Set.empty

replaceDecl :: Substitution -> Env -> TypedDecl -> TypedDecl
replaceDecl subst env (ident, td) = (ident, replaceDeclData subst env td)

replaceIdent :: Substitution -> Env -> Identifier -> Identifier
replaceIdent subst env ident =
  case Map.lookup (stringOf ident) env of
    Just (_, TTypeVar ident') ->
      case Map.lookup ident' subst of
        Just (TTypeVar ident'') -> ident''
        _ -> ident'
    _ -> ident

replaceDeclData :: Substitution -> Env -> TypedDeclData -> TypedDeclData
replaceDeclData subst env td =
  case td of
    TTypeDecl t ->
      TTypeDecl (replaceType subst env t)
    TFunDecl typeargs args retTy s ->
      TFunDecl (List.map (replaceIdent subst env) typeargs)
        (List.map (replaceMatchExpr subst env) args)
                                  (replaceType subst env retTy)
                                  (replaceStatement subst env s)

replaceMatchExpr :: Substitution -> Env -> TypedMatchExpr -> TypedMatchExpr
replaceMatchExpr subst env (tme, ty) =
  let replace (TTupleMatchExpr tmes, ty) =
        let ty' = replaceType subst env ty
        in (TTupleMatchExpr (List.map replace tmes), ty')
      replace (TListMatchExpr tmes, ty) =
        let ty' = replaceType subst env ty
        in (TListMatchExpr (List.map replace tmes), ty')
      replace (TRecordMatchExpr fields, ty) =
        let ty' = replaceType subst env ty
            f (s, tme) = (s, replace tme)
        in (TRecordMatchExpr (List.map f fields), ty')
      replace (tme, ty) = (tme, replaceType subst env ty)
  in replace (tme, ty)

replaceStatement :: Substitution -> Env -> TypedStatement -> TypedStatement
replaceStatement subst env ts =
  let replace (TIfStatement te ts tsm) =
        TIfStatement (replaceExpr subst env te) (replace ts)
                     (fmap replace tsm)
      replace (TWhileStatement te ts) =
        TWhileStatement (replaceExpr subst env te) (replace ts)
      replace (TForStatement tme te ts) =
        TForStatement (replaceMatchExpr subst env tme)
                      (replaceExpr subst env te) (replace ts)
      replace (TCompoundStatement tss) =
        TCompoundStatement (List.map replace tss)
      replace (TAssignStatement tme_tlve te) =
        TAssignStatement (either (Left . replaceMatchExpr subst env)
                                 (Right . replaceLValueExpr subst env) tme_tlve)
                         (replaceExpr subst env te)
      replace (TMatchStatement te actions) =
        let f (tme, ts) = (replaceMatchExpr subst env tme, replace ts)
        in TMatchStatement (replaceExpr subst env te) (List.map f actions)
      replace (TReturnStatement tem) =
        TReturnStatement (replaceExpr subst env tem)
      replace TBreakStatement = TBreakStatement
      replace TContinueStatement = TContinueStatement
      replace (TDeclStatement td) = TDeclStatement (replaceDecl subst env td)
  in replace ts

replaceExpr :: Substitution -> Env -> TypedExpr -> TypedExpr
replaceExpr subst env (te, ty) =
  let replace (TIntExpr n, ty) = (TIntExpr n, replaceType subst env ty)
      replace (TRealExpr d, ty) = (TRealExpr d, replaceType subst env ty)
      replace (TBoolExpr b, ty) = (TBoolExpr b, replaceType subst env ty)
      replace (TStringExpr s, ty) = (TStringExpr s, replaceType subst env ty)
      replace (TOrExpr te1 te2, ty) =
        (TOrExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TAndExpr te1 te2, ty) =
        (TAndExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TEqExpr te1 te2, ty) =
        (TEqExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TNeqExpr te1 te2, ty) =
        (TNeqExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TLtExpr te1 te2, ty) =
        (TLtExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TGtExpr te1 te2, ty) =
        (TGtExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TLeExpr te1 te2, ty) =
        (TLeExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TGeExpr te1 te2, ty) =
        (TGeExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TAddExpr te1 te2, ty) =
        (TAddExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TSubExpr te1 te2, ty) =
        (TSubExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TMultExpr te1 te2, ty) =
        (TMultExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TDivExpr te1 te2, ty) =
        (TDivExpr (replace te1) (replace te2), replaceType subst env ty)
      replace (TUnaryMinusExpr te, ty) =
        (TUnaryMinusExpr (replace te), replaceType subst env ty)
      replace (TBangExpr te, ty) =
        (TBangExpr (replace te), replaceType subst env ty)
      replace (TCallExpr teFun teArg, ty) =
        (TCallExpr (replace teFun) (replace teArg), replaceType subst env ty)
      replace (TListExpr tes, ty) =
        (TListExpr (List.map replace tes), replaceType subst env ty)
      replace (TTupleExpr tes, ty) =
        (TTupleExpr (List.map replace tes), replaceType subst env ty)
      replace (TRecordExpr fields, ty) =
        (TRecordExpr (List.map f fields), ty')
        where f (s, te) = (s, replace te)
              ty' = replaceType subst env ty
      replace (TLValue tlve, ty) =
        (TLValue (replaceLValueExpr subst env tlve), replaceType subst env ty)

      replace (TLambdaExpr tmes ts, ty) =
        (TLambdaExpr (List.map (replaceMatchExpr subst env) tmes)
                    (replaceStatement subst env ts), replaceType subst env ty)
  in replace (te, ty)

replaceLValueExpr :: Substitution -> Env -> TypedLValueExpr -> TypedLValueExpr
replaceLValueExpr subst env (tlve, ty) =
  let replace (TVarExpr s, ty) =
        let ty' = replaceType subst env ty
        in (TVarExpr s, ty')
      replace (TFieldAccessExpr tlve s, ty) =
        let ty' = replaceType subst env ty
        in (TFieldAccessExpr (replace tlve) s, ty')
      replace (TArrayAccessExpr tlve te, ty) =
        let ty' = replaceType subst env ty
        in (TArrayAccessExpr (replace tlve) (replaceExpr subst env te), ty')
  in replace (tlve, ty)
