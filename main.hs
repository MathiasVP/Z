import Parser as P
import TypeInfer as T
import MatchCheck as MC
import Control.Monad.Trans.Writer.Lazy

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                 (typed, env, subst) <- T.infer ast
                 print env
                 let (b, s) = runWriter (MC.matchCheck typed)
                 print b
                 putStrLn s