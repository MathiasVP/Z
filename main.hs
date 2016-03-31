import Parser as P
import qualified TypeInfer as T
--import qualified IRGen as IR
import qualified InferFieldOffsets as IFO
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map(Map, (!))
import CubicSolver as S
import Data.Graph.Inductive.Dot
import Text.Groom

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                  let constraints = [
                        constraint (Membership (Element "inc") (Set "inc")),
                        constraint (Membership (Element "dec") (Set "dec")),
                        constraint (Membership (Element "ide") (Set "ide")),
                        
                        constraint (Inclusion (Set "ide") (Set "f")),
                        constraint (Inclusion (Set "(f)(n)") (Set "r")),
                        
                        constraint (CondInclusion (Element "inc") (Set ("f")) (Set "n") (Set "i")),
                        constraint (CondInclusion (Element "inc") (Set ("f")) (Set "i+1") (Set "(f)(n)")),
                        
                        constraint (CondInclusion (Element "dec") (Set ("f")) (Set "n") (Set "j")),
                        constraint (CondInclusion (Element "dec") (Set ("f")) (Set "j-1") (Set "(f)(n)")),
                        
                        constraint (CondInclusion (Element "ide") (Set ("f")) (Set "n") (Set "k")),
                        constraint (CondInclusion (Element "ide") (Set ("f")) (Set "k") (Set "(f)(n)")),
                        
                        constraint (Inclusion (Set "input") (Set "x")),
                        constraint (Inclusion (Set "foo(x,inc)") (Set "y")),
                        constraint (Inclusion (Set "foo(x,dec)") (Set "y")),
                        
                        constraint (Membership (Element "foo") (Set "foo")),
                        
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "x") (Set "n")),
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "inc") (Set "f")),
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "r") (Set "foo(x,inc)")),
                        
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "x") (Set "n")),
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "dec") (Set "f")),
                        constraint (CondInclusion (Element "foo") (Set "foo") (Set "r") (Set "foo(x,dec)"))]
                      inst = List.foldl (flip ($)) S.empty constraints
                  putStrLn $ groom $ (solution inst) ! (Set "f")
                 --(typed, env, subst) <- T.infer ast
                 --let fieldMap = IFO.construct env typed
                 --putStrLn (groom typed)
                 --putStrLn (groom fieldMap)
                 --ir <- IR.irGen env typed
                 --print ir