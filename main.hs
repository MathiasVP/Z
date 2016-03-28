import Parser as P
import qualified TypeInfer as T
--import qualified IRGen as IR
import qualified InferFieldOffsets as IFO
import qualified Data.List as List
import CubicSolver as S
import Text.Groom

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                  let constraints = [
                        constraint (Membership (Token "inc") (Variable "inc")),
                        constraint (Membership (Token "dec") (Variable "dec")),
                        constraint (Membership (Token "ide") (Variable "ide")),
                        
                        constraint (Inclusion (Variable "ide") (Variable "f")),
                        constraint (Inclusion (Variable "(f)(n)") (Variable "r")),
                        
                        constraint (CondInclusion (Token "inc") (Variable ("f")) (Variable "n") (Variable "i")),
                        constraint (CondInclusion (Token "inc") (Variable ("f")) (Variable "i+1") (Variable "(f)(n)")),
                        
                        constraint (CondInclusion (Token "dec") (Variable ("f")) (Variable "n") (Variable "j")),
                        constraint (CondInclusion (Token "dec") (Variable ("f")) (Variable "j-1") (Variable "(f)(n)")),
                        
                        constraint (CondInclusion (Token "ide") (Variable ("f")) (Variable "n") (Variable "k")),
                        constraint (CondInclusion (Token "ide") (Variable ("f")) (Variable "k") (Variable "(f)(n)")),
                        
                        constraint (Inclusion (Variable "input") (Variable "x")),
                        constraint (Inclusion (Variable "foo(x,inc)") (Variable "y")),
                        constraint (Inclusion (Variable "foo(x,dec)") (Variable "y")),
                        
                        constraint (Membership (Token "foo") (Variable "foo")),
                        
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "x") (Variable "n")),
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "inc") (Variable "f")),
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "r") (Variable "foo(x,inc)")),
                        
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "x") (Variable "n")),
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "dec") (Variable "f")),
                        constraint (CondInclusion (Token "foo") (Variable "foo") (Variable "r") (Variable "foo(x,dec)"))]
                      inst = List.foldl (flip ($)) S.empty constraints
                  putStrLn (groom inst)
                 --(typed, env, subst) <- T.infer ast
                 --let fieldMap = IFO.construct env typed
                 --putStrLn (groom typed)
                 --putStrLn (groom fieldMap)
                 --ir <- IR.irGen env typed
                 --print ir