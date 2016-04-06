module CallGraph where

import Types
import TypedAst
import TypeUtils
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.PatriciaTree(Gr)
import Control.Monad.State
import qualified Data.Map as Map
import Data.Map(Map, (!))
import qualified CubicSolver as S
import qualified Data.List as List
import Data.Hash.MD5

newtype CallGraph = CallGraph (Gr Identifier ())
  deriving Show

type ST = S.Instance TLValueExpr TExpr

construct env decls =
  S.solution $ execState (mapM_ (visitDecl env) decls) S.empty

 --TODO: Will fail for locally defined functions
visitDecl :: Env -> TypedDecl -> State ST ()
visitDecl env (TFunDecl name _ args ty stmt) =
  modify (S.constraint (S.Membership (S.Element elem) (S.Set $ set))) >>
  visitStmt env stmt
  where elem = TVarExpr name
        set = TLValue (TVarExpr name, snd $ env ! (stringOf name))
visitDecl _ _ = return ()
  
visitStmt env (TIfStatement e stmt Nothing) =
  visitExpr env e >> visitStmt env stmt
visitStmt env (TIfStatement e stmt1 (Just stmt2)) =
  visitExpr env e >> visitStmt env stmt1 >> visitStmt env stmt2
visitStmt env (TWhileStatement e stmt) =
  visitExpr env e >> visitStmt env stmt
visitStmt env (TForStatement me e stmt) =
  visitExpr env e >> visitStmt env stmt
visitStmt env (TCompoundStatement stmts) =
  mapM_ (visitStmt env) stmts
visitStmt env (TAssignStatement lhs e) =
  either (constraintMatchExpr env e) (constraintLValueExpr env e) lhs >>
  visitExpr env e
visitStmt env (TMatchStatement e matches) =
  visitExpr env e >> mapM_ visit matches
  where visit (_, stmt) = visitStmt env stmt
visitStmt env (TReturnStatement e) = visitExpr env e
visitStmt env TBreakStatement = return ()
visitStmt env TContinueStatement = return ()
visitStmt env (TDeclStatement decl) = visitDecl env decl

constraintMatchExpr :: Env -> TypedExpr -> TypedMatchExpr -> State ST ()
constraintMatchExpr env (TTupleExpr exprs, _) (TTupleMatchExpr mexprs, _) =
  mapM_ (uncurry $ constraintMatchExpr env) (List.zip exprs mexprs)
constraintMatchExpr env (TListExpr exprs, _) (TListMatchExpr mexprs, _) =
  mapM_ (uncurry $ constraintMatchExpr env) (List.zip exprs mexprs)
constraintMatchExpr env (TRecordExpr exprFields, _)
                         (TRecordMatchExpr matchFields, _) =
  mapM_ constraintField exprFields
  where constraintField (name, expr) = constraintMatchExpr env expr (m ! name)
        m = Map.fromList matchFields
constraintMatchExpr env (e, _) (TVarMatch id, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TVarExpr id, ty))))
--constraintMatchExpr' _ _ _ = return () --TODO: More cases

constraintLValueExpr :: Env -> TypedExpr -> TypedLValueExpr -> State ST ()
constraintLValueExpr env (e, _) (TVarExpr id, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TVarExpr id, ty))))
constraintLValueExpr env (e, _) (TFieldAccessExpr lve s, ty) =
  modify $ S.constraint (S.Inclusion (S.Set e)
             (S.Set (TLValue (TFieldAccessExpr lve s, ty))))
  
visitExprs :: Env -> [TypedExpr] -> State ST ()
visitExprs env = mapM_ (visitExpr env)

visitExpr :: Env -> TypedExpr -> State ST ()
visitExpr env (TIntExpr _, _) = return ()
visitExpr env (TRealExpr _, _) = return ()
visitExpr env (TBoolExpr _, _) = return ()
visitExpr env (TStringExpr _, _) = return ()
visitExpr env (TOrExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TAndExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TEqExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TNeqExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TLtExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TGtExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TLeExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TGeExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TAddExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TSubExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TMultExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TDivExpr e1 e2, _) = visitExprs env [e1, e2]
visitExpr env (TUnaryMinusExpr e, _) = visitExpr env e
visitExpr env (TBangExpr e, _) = visitExpr env e
visitExpr env (TCallExpr e1 e2, ty) = error (show $ numberOfArgs (TCallExpr e1 e2, ty)) --visitExprs env [e1, e2]
visitExpr env (TListExpr es, _) = visitExprs env es
visitExpr env (TRecordExpr fields, _) = mapM_ (visitExpr env . snd) fields
visitExpr env (TTupleExpr es, _) = visitExprs env es
visitExpr env (TLValue lve, _) = visitLValueExpr env lve
visitExpr env (TLambdaExpr mes stmt, ty) =
  modify (S.constraint (S.Membership (S.Element elem) (S.Set $ set)))
  where name = placeholder (md5s (Str (show (TLambdaExpr mes stmt, ty))))
        elem = TVarExpr name
        set = TLValue (TVarExpr name, ty)

numberOfArgs :: TypedExpr -> Int
numberOfArgs (TCallExpr e1 e2, _) = numberOfArgs e1 + 1
numberOfArgs _ = 0
        
visitLValueExpr :: Env -> TypedLValueExpr -> State ST ()
visitLValueExpr env (lve, ty) = visitLValueExpr' env lve

visitLValueExpr' :: Env -> TLValueExpr -> State ST ()
visitLValueExpr' env (TVarExpr _) = return ()
visitLValueExpr' env (TFieldAccessExpr lve _) = visitLValueExpr env lve
visitLValueExpr' env (TArrayAccessExpr lve e) =
  visitLValueExpr env lve >> visitExpr env e