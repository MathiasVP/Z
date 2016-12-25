{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module CallGraph where
import Types
import TypedAst
import TypeUtils
import Data.Graph.Inductive.PatriciaTree(Gr)
import Control.Monad.State
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Map((!))
import qualified CubicSolver as S
import qualified Data.List as List
import Data.Hash.MD5
import Control.Monad.Reader
import qualified Debug.Trace as Debug

newtype CallGraph = CallGraph (Gr Identifier ())
  deriving Show

type ST = S.Instance TLValueExpr TExpr
type CG = ReaderT (Env, Map Identifier FunctionInfo) (State ST) ()

construct :: Env -> Map Identifier FunctionInfo -> [TypedDecl] -> S.Solution TLValueExpr TExpr
construct env funcs decls =
  S.solution $ execState (runReaderT (mapM_ visitDecl decls) (env, funcs)) S.empty

visitDecl :: TypedDecl -> CG
visitDecl (TFunDecl name _ _ _ stmt) = do
  funcs <- asks snd
  let set = TLValue (TVarExpr name, funty (funcs ! name))
  modify (S.constraint (S.Membership (S.Element (TVarExpr name)) (S.Set set)))
  visitStmt stmt
visitDecl _ = return ()

visitStmt :: TypedStatement -> CG
visitStmt (TIfStatement e stmt Nothing) =
  visitExpr e >> visitStmt stmt
visitStmt (TIfStatement e stmt1 (Just stmt2)) =
  visitExpr e >> visitStmt stmt1 >> visitStmt stmt2
visitStmt (TWhileStatement e stmt) =
  visitExpr e >> visitStmt stmt
visitStmt (TForStatement _ e stmt) =
  visitExpr e >> visitStmt stmt
visitStmt (TCompoundStatement stmts) =
  mapM_ visitStmt stmts
visitStmt (TAssignStatement lhs e) =
  either (constraintMatchExpr e) (constraintLValueExpr e) lhs >>
  visitExpr e
visitStmt (TMatchStatement e matches) =
  visitExpr e >> mapM_ visit matches
  where visit (_, stmt) = visitStmt stmt
visitStmt (TReturnStatement e) = visitExpr e
visitStmt TBreakStatement = return ()
visitStmt TContinueStatement = return ()
visitStmt (TDeclStatement decl) = visitDecl decl

constraintMatchExpr :: TypedExpr -> TypedMatchExpr ->CG
constraintMatchExpr (TTupleExpr exprs, _) (TTupleMatchExpr mexprs, _) =
  mapM_ (uncurry constraintMatchExpr) (List.zip exprs mexprs)
constraintMatchExpr (TListExpr exprs, _) (TListMatchExpr mexprs, _) =
  mapM_ (uncurry constraintMatchExpr) (List.zip exprs mexprs)
constraintMatchExpr (TRecordExpr exprFields, _)
                    (TRecordMatchExpr matchFields, _) =
  mapM_ constraintField exprFields
  where constraintField (name, expr) = constraintMatchExpr expr (m ! name)
        m = Map.fromList matchFields
constraintMatchExpr (e, _) (TVarMatch id, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TVarExpr id, ty))))
--constraintMatchExpr' _ _ _ = return () --TODO: More cases

constraintLValueExpr :: TypedExpr -> TypedLValueExpr -> CG
constraintLValueExpr (e, _) (TVarExpr id, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TVarExpr id, ty))))
constraintLValueExpr (e, _) (TFieldAccessExpr lve s, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TFieldAccessExpr lve s, ty))))

visitExprs :: [TypedExpr] -> CG
visitExprs = mapM_ visitExpr

visitExpr :: TypedExpr -> CG
visitExpr (TIntExpr _, _) = return ()
visitExpr (TRealExpr _, _) = return ()
visitExpr (TBoolExpr _, _) = return ()
visitExpr (TStringExpr _, _) = return ()
visitExpr (TOrExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TAndExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TEqExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TNeqExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TLtExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TGtExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TLeExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TGeExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TAddExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TSubExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TMultExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TDivExpr e1 e2, _) = visitExprs [e1, e2]
visitExpr (TUnaryMinusExpr e, _) = visitExpr e
visitExpr (TBangExpr e, _) = visitExpr e
visitExpr (TCallExpr ((TLValue (TVarExpr ident, _)), _) e2, _) = do
  Debug.trace (_ ident) $ return ()
  --fs <- asks snd
  --return $ _ fs
  --visitExprs [e1, e2]
visitExpr (TListExpr es, _) = visitExprs es
visitExpr (TRecordExpr fields, _) = mapM_ (visitExpr . snd) fields
visitExpr (TTupleExpr es, _) = visitExprs es
visitExpr (TLValue lve, _) = visitLValueExpr lve
visitExpr (TLambdaExpr mes stmt, ty) =
  modify (S.constraint (S.Membership (S.Element elem) (S.Set set)))
  where name = placeholder (md5s (Str (show (TLambdaExpr mes stmt, ty))))
        elem = TVarExpr name
        set = TLValue (TVarExpr name, ty)

visitLValueExpr :: TypedLValueExpr -> CG
visitLValueExpr (lve, _) = visitLValueExpr' lve

visitLValueExpr' :: TLValueExpr -> CG
visitLValueExpr' (TVarExpr _) = return ()
visitLValueExpr' (TFieldAccessExpr lve _) = visitLValueExpr lve
visitLValueExpr' (TArrayAccessExpr lve e) =
  visitLValueExpr lve >> visitExpr e
