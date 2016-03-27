module CallGraph where

newtype CallGraph = CallGraph (Gr )

construct :: Env -> [TypedDecl] -> CallGraph
construct env decl = 