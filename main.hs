import Parser as P
import TypeInfer as T

import Data.List as List

main :: IO ()
main = let path = "../test.z"
       in do content <- readFile path
             case P.parse content of
               Left err -> print err
               Right ast -> do
                (typed, env, subst) <- T.infer ast
                print typed
                putStrLn ""
                print env
                putStrLn ""
                print subst