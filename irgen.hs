{-# LANGUAGE LambdaCase #-}

module IRGen where
import Prelude hiding(seq)
import TypedAst
import Utils
import TypeUtils
import IR
import Types
import Unique
import Data.Maybe
import Control.Arrow
import Data.Bool
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Tree as Tree
import Data.Map(Map, (!))
import Data.Tree(Tree, Forest)
import Control.Monad.State.Lazy
import qualified Debug.Trace as Debug

drawTree :: Show a => Tree a -> String
drawTree t = Tree.drawTree (fmap show t)

drawForest :: Show a => Forest a -> String
drawForest = unlines . List.map drawTree

data Frame = Frame { stack :: Int
                   , closure :: Int }

data Access = StackLocal Type Int
            | ClosureLocal Type Int
            | FunctionParam Type Int

data IRGenState = IRGenState { stringmap :: Map String UniqString
                             , fragmap :: Map UniqString Fragment
                             , frame :: Frame
                             , venv :: Map UniqString Access
                             , breakLabel :: Maybe UniqString
                             , contLabel :: Maybe UniqString
                             , endLabel :: Maybe UniqString }
type IRGenM a = StateT IRGenState IO a

insertName :: String -> UniqString -> IRGenState -> IRGenState
insertName key value state =
  state { stringmap = Map.insert key value (stringmap state) }

insertFrag :: UniqString -> Fragment -> IRGenState -> IRGenState
insertFrag key value state =
  state { fragmap = Map.insert key value (fragmap state) }
  
insertVar :: UniqString -> Access -> IRGenState -> IRGenState
insertVar s loc state =
  state { venv = Map.insert s loc (venv state) }
  
updateEndLabel :: UniqString -> IRGenState -> IRGenState
updateEndLabel lab state = state {endLabel = Just lab}

updateBreakLabel :: Maybe UniqString -> IRGenState -> IRGenState
updateBreakLabel lab state = state {breakLabel = lab}
  
updateContLabel :: Maybe UniqString -> IRGenState -> IRGenState
updateContLabel lab state = state {contLabel = lab}

stackAlloc :: Type -> Int -> IRGenM Access
stackAlloc ty n =
  do fr <- gets frame
     modify (\x -> x { frame = (frame x) { stack = stack (frame x) + n } })
     return $ StackLocal ty (stack fr)
     
closureAlloc :: Type -> Int -> IRGenM Access
closureAlloc ty n =
  do fr <- gets frame
     modify (\x -> x { frame = (frame x) { closure = closure (frame x) + n } })
     return $ ClosureLocal ty (closure fr)

heapAlloc :: Type -> Int -> IR.TExpr
heapAlloc ty n =
  (IR.Call (IR.Name (UniqString "malloc"), IntType) [intConst n], ty)

  
uniq :: String -> IRGenM UniqString
uniq s = liftM (UniqString . (s ++) . show) (io unique)

seq :: [Stmt] -> Stmt
seq = List.foldl1 Seq

seqM :: IRGenM [Stmt] -> IRGenM Stmt
seqM stmtsm = stmtsm >>= return . seq

eseq :: [Stmt] -> IR.TExpr -> IR.TExpr
eseq stmt texpr@(expr, ty) = (SeqExpr (seq stmt) texpr, ty)

irGen :: Env -> [TypedDecl] -> IO [Fragment]
irGen env ast = execStateT (mapM (declGen env) ast) initGenState
                  >>= return . Map.elems . fragmap
  where initGenState = IRGenState { stringmap = Map.empty
                                  , fragmap = Map.empty
                                  , frame = Frame { stack = 0
                                                  , closure = 0 }
                                  , venv = Map.empty
                                  , breakLabel = Nothing
                                  , contLabel = Nothing
                                  , endLabel = Nothing }

declGen :: Env -> TypedDecl -> IRGenM ()
declGen env (TTypeDecl name args ty) = return ()
declGen env (TFunDecl name tyargs args ty stmt) =
  do uname <- uniq name
     retname <- uniq (name ++ "ret")
     modify (insertName name uname)
     modify (updateEndLabel retname)
     stmt' <- stmtGen env stmt
     Just endLab <- gets endLabel
     modify (insertFrag uname (ProcFrag uname ty (Seq stmt' (Label retname))))

if_ :: View -> IR.Stmt -> IR.Stmt -> IRGenM IR.Stmt
if_ mtest then_ else_ =
  do thenLab <- uniq "then"
     elseLab <- uniq "else"
     doneLab <- uniq "done"
     return $ seq [ unCx mtest thenLab elseLab,
                    Label thenLab,
                    then_,
                    Jump doneLab,
                    Label elseLab,
                    else_,
                    Label doneLab ]

intConst :: Int -> IR.TExpr
intConst n = (IntConst n, IntType)

simpleVar :: Access -> IR.TExpr
simpleVar (StackLocal ty offs) =
  (Mem (BinOp Plus (fp IntType)
                   (intConst offs), ty), ty)
simpleVar (FunctionParam ty num) =
  (IR.Name (UniqString ("t" ++ show num)), ty)
simpleVar (ClosureLocal ty offs) =
  (Mem (BinOp Plus (simpleVar (FunctionParam ty 0)) (intConst offs), ty), ty)

unCx :: View -> UniqString -> UniqString -> IR.Stmt
unCx (Cx gen) trueLab falseLab = gen trueLab falseLab
unCx (Ex texpr) trueLab falseLab = CJump Rneq texpr false trueLab falseLab

unEx :: View -> IRGenM IR.TExpr
unEx (Cx gen) =
  do trueLab <- uniq "true"
     falseLab <- uniq "false"
     tmp <- stackAlloc IntType 1
     let expr = simpleVar tmp
     return $ eseq [ IR.Move expr true
                   , gen trueLab falseLab
                   , Label falseLab
                   , IR.Move expr false
                   , Label trueLab ] expr
unEx (Ex texpr) = return texpr

while :: IR.View -> IR.Stmt -> IRGenM IR.Stmt
while test body =
  do breakLab <- uniq "break"
     thenLab <- uniq "then"
     testLab <- uniq "test"
     
     oldBreakLab <- gets breakLabel
     oldContLab <- gets contLabel

     modify (updateBreakLabel (Just breakLab))
     modify (updateContLabel (Just testLab))
     modify (updateBreakLabel oldBreakLab)
     modify (updateContLabel oldContLab)
     return $ seq [ Label testLab,
                    unCx test thenLab breakLab,
                    Label thenLab,
                    body,
                    Jump testLab,
                    Label breakLab ]

rv :: Type -> IR.TExpr
rv ty = (RV, ty)

fp :: Type -> IR.TExpr
fp ty = (FP, ty)

false :: IR.TExpr
false = (IntConst 0, BoolType)

true :: IR.TExpr
true = (IntConst 1, BoolType)

emptyStmt :: Monad m => m Stmt
emptyStmt = return $ ExprStmt false

return_ :: [IR.TExpr] -> IRGenM IR.Stmt
return_ exprs =
  let types = List.map typeOf exprs
      rvs = map rv types
      dsts = List.zip (List.zipWith (BinOp Plus) rvs offsets) types
  in gets endLabel >>= \(Just endLab) ->
        return $ seq (List.zipWith IR.Move dsts exprs ++ [Jump endLab])
 where offsets = List.map intConst [0..]

assign :: Forest IR.TExpr -> [IR.TExpr] -> IRGenM IR.Stmt
assign vars exprs = error ("\n" ++ show vars) --return . seq . List.map (uncurry doAssign) $ List.zip vars exprs
  where doAssign :: Tree IR.TExpr -> IR.TExpr -> IR.Stmt
        doAssign (Tree.Node e forests) rhs = error "TODO: 14.3 in Appel"

stmtGen :: Env -> TypedStatement -> IRGenM IR.Stmt
stmtGen env (TIfStatement testExpr thenStmt elseStmt) =
  do [view] <- exprGen env testExpr
     then' <- stmtGen env thenStmt
     else' <- maybe emptyStmt (stmtGen env) elseStmt
     if_ view then' else'
stmtGen env (TWhileStatement testExpr stmt) =
  do [view] <- exprGen env testExpr
     stmt' <- stmtGen env stmt
     while view stmt'
stmtGen env (TCompoundStatement stmts) =
  seqM (mapM (stmtGen env) stmts)
stmtGen env TBreakStatement =
  gets breakLabel >>= return . Jump . fromJust
stmtGen env TContinueStatement =
  gets contLabel >>= return . Jump . fromJust
stmtGen env (TReturnStatement expr) =
  exprGen env expr >>= mapM unEx >>= return_
stmtGen env (TAssignStatement (Left mexpr) expr) =
  matchExprGen env mexpr >>= \varmap ->
  exprGen env expr >>=
  mapM unEx >>= assign varmap

returnEx :: IR.TExpr -> IRGenM View
returnEx = return . Ex

returnExs :: [IR.TExpr] -> IRGenM [View]
returnExs = sequence . liftM returnEx

moves :: IR.TExpr -> [IR.TExpr] -> [IR.TExpr] -> IR.Stmt
moves base offs exprs =
  seq $ List.zipWith genMove offs exprs
  where genMove offs = IR.Move
                         (IR.Mem
                           ((IR.BinOp Plus base offs), typeOf base),
                           typeOf base)

exprGen :: Env -> TypedExpr -> IRGenM [View]
exprGen env (TIntExpr n, ty) = returnExs [(IntConst n, ty)]
exprGen env (TRealExpr n, ty) = returnExs [(RealConst n, ty)]
exprGen env (TBoolExpr b, ty) = returnExs [(IntConst (bool 0 1 b), ty)]
exprGen env (TStringExpr s, ty) =
  do key <- uniq "string"
     modify (insertFrag key (StringFrag s))
     returnExs [(IR.Name key, ty)]
exprGen env (TTupleExpr exprs, ty) =
  liftM List.concat $ mapM (exprGen env) exprs
exprGen env (TListExpr exprs, Array ty) =
  concatMapM (exprGen env) exprs >>= \views ->
  mapM unEx views >>= \exprs ->
  liftM simpleVar (stackAlloc ty 1) >>= \dst ->
  let n = List.length views
      alloc = heapAlloc ty (n+1)
      moves_ = moves dst [intConst offs | offs <- [0..]]
                         (intConst n : exprs)
  in returnExs [(SeqExpr (Seq (IR.Move dst alloc) moves_) dst, typeOf dst)]
exprGen env (TBangExpr expr, ty) =
  exprGen env expr >>= \[view] ->
  unEx view >>= \expr' ->
  returnExs [(BinOp Minus (intConst 1) expr', ty)]


lookupm :: Ord k => Maybe k -> Map k a -> Maybe a
lookupm key map = join $ liftM (flip Map.lookup map) key

matchExprGen :: Env -> TypedMatchExpr -> IRGenM (Forest IR.TExpr)
matchExprGen env (TVarMatch s, ty) =
  do venv_ <- gets venv
     stringmap_ <- gets stringmap
     case lookupm (Map.lookup s stringmap_) venv_ of
       Just frag -> return [Tree.Node (simpleVar frag) []]
       Nothing -> do
         us <- uniq s
         modify (insertName s us)
         frag <- stackAlloc ty 1
         modify (insertVar us frag)
         return [Tree.Node (simpleVar frag) []]
matchExprGen env (TTupleMatchExpr mexprs, ty) =
  mapM (matchExprGen env) mexprs >>= return . List.concat
matchExprGen env (TIntMatchExpr n, ty) =
  return [Tree.Node (IntConst n, ty) []]
matchExprGen env (TStringMatchExpr s, ty) =
  do key <- uniq "string"
     modify (insertFrag key (StringFrag s))
     return [Tree.Node (IR.Name key, ty) []]
matchExprGen env (TBoolMatchExpr b, ty)
  | b         = return [Tree.Node (IntConst 1, ty) []]
  | otherwise = return [Tree.Node (IntConst 0, ty) []]
matchExprGen env (TListMatchExpr mexprs, ty) =
  mapM (matchExprGen env) mexprs >>= return . List.concat
matchExprGen env (TRecordMatchExpr fields, ty) =
  undefined --mapM (second (matchExprGen env)) fields >>= error "TODO: 14.3 in Appel"