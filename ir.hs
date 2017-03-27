module IR where
import Types
import Unique
import Control.Monad
import qualified Data.List as List
import Control.Monad.Trans.State.Lazy



newtype UniqString = UniqString String
  deriving (Ord, Eq)

instance Show UniqString where
  show (UniqString s) = s

data Expr
  = BinOp BOp TExpr TExpr
  | Mem TExpr
  | Temp UniqueInt
  | Name UniqString
  | IntConst Int
  | RealConst Double
  | Call TExpr [TExpr]
  | SeqExpr Stmt TExpr
  | RV
  | FP
  deriving Show

type TExpr = (Expr, Type)

data View = Ex TExpr
          | Cx (UniqString -> UniqString -> Stmt)

data BOp
  = Plus | Minus | Mult | Div |
    Beq | Bneq | Blt | Bgt | Ble | Bge
  deriving Show

data ROp
  = Req | Rneq | Rlt | Rgt | Rle | Rge
  deriving Show

data Stmt
  = Label UniqString
  | CJump ROp TExpr TExpr UniqString UniqString
  | Jump UniqString
  | Move TExpr TExpr
  | ExprStmt TExpr
  | Seq Stmt Stmt

data Fragment
  = StringFrag String
  | ProcFrag UniqString Type Stmt

instance Show Fragment where
  show (StringFrag s) = "StringFrag " ++ s
  show (ProcFrag (UniqString s) ty stmt) =
    "ProcFrag " ++ s ++ " " ++ show ty ++ "\n" ++ show stmt

instance (Show Stmt) where
  show = ppIR

ppIR :: Stmt -> String
ppIR stmt = evalState (ppStmt stmt) 0

indent :: String -> State Int String
indent s = get >>= return . (++ s) . (flip replicate ' ')

indentM :: State Int String -> State Int String
indentM sm =
  get >>= \n ->
  sm >>= \s -> return ((replicate n ' ') ++ s)

(<++>) :: Monad m => m [a] -> m [a] -> m [a]
(<++>) xsm ysm =
  xsm >>= \xs ->
  ysm >>= \ys ->
  return (xs ++ ys)

infixr 5 <++>

(<<+>) :: Monad m => m [a] -> [a] -> m [a]
(<<+>) xsm ys =
  xsm >>= \xs ->
  return (xs ++ ys)

infixr 5 <<+>

(<+>>) :: Monad m => [a] -> m [a] -> m [a]
(<+>>) xs ysm =
  ysm >>= \ys ->
  return (xs ++ ys)

incr :: Int -> State Int String
incr n = modify (n +) >> return ""

decr :: Int -> State Int String
decr n = modify (\m -> m - n) >> return ""

infixr 5 <+>>

ppStmt :: Stmt -> State Int String
ppStmt (Label us) = return $ "(Label " ++ show us ++ ")"
ppStmt (Jump us) = return $ "(Jump " ++ show us ++ ")"
ppStmt (Move expr1 expr2) =
  "(Move\n" <+>>
    incr 2 <++>
    indentM (ppExpr expr1) <++>
    "\n" <+>>
    indentM (ppExpr expr2) <++>
    decr 2 <<+>
  ")"
ppStmt (ExprStmt expr) =
  "(ExprStmt " <+>>
    incr 10 <++>
    ppExpr expr <++>
    decr 10 <<+>
  ")"
ppStmt (CJump op lhs rhs us1 us2) =
  "(CJump " <+>> show op <+>> "\n" <+>>
    incr 2 <++>
    indentM (ppExpr lhs) <++>
    "\n" <+>>
    indentM (ppExpr rhs) <++>
    "\n" <+>>
    indent (show us1) <++>
    "\n" <+>>
    indent (show us2) <++>
    decr 2 <<+>
  ")"
ppStmt (Seq stmt1 stmt2) =
  "(Seq\n" <+>>
    incr 2 <++>
    indentM (ppStmt stmt1) <++>
    "\n" <+>>
    indentM (ppStmt stmt2) <++>
    decr 2 <<+>
  ")"

ppExpr :: TExpr -> State Int String
ppExpr ((BinOp op expr1 expr2), _) =
  "(BinOp\n" <+>>
    incr 2 <++>
    indent (show op) <++>
    "\n" <+>>
    indentM (ppExpr expr1) <++>
    "\n" <+>>
    indentM (ppExpr expr2) <++>
    decr 2 <<+>
  ")"
ppExpr (Mem expr, _) =
  "(Mem \n" <+>>
    incr 2 <++>
    indentM (ppExpr expr) <++>
    decr 2 <<+>
  ")"
ppExpr (Temp un, _) =
  return $ "(Temp " ++ show un ++ ")"
ppExpr (IR.Name us, _) =
  return $ "(Name " ++ show us ++ ")"
ppExpr (IntConst n, _) = return $ show n
ppExpr (RealConst n, _) = return $ show n
ppExpr (Call expr exprs, _) =
  "(Call\n" <+>>
  incr 2 <++>
  indentM (ppExpr expr) <++>
  "\n" <+>>
  indent "[" <++>
  incr 2 <++>
  format (mapM ppExpr exprs) <++>
  decr 2 <<+>
  "])"
  where format = liftM (List.concat . List.intersperse ",")
ppExpr (SeqExpr stmt expr, _) =
  "(SeqExpr\n" <+>>
    incr 2 <++>
    indentM (ppStmt stmt) <++>
    "\n" <+>>
    indentM (ppExpr expr) <++>
    decr 2 <<+>
  ")"
ppExpr (RV, _) = return "RV"
ppExpr (FP, _) = return "FP"
