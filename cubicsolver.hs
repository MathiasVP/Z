{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module CubicSolver(Element(Element), Set(Set), Instance,
                   Constraint(Membership, Inclusion, CondInclusion), Solution,
                   empty, constraint, solution) where

import Prelude hiding ((++))
import Control.Monad.State
import qualified Data.Vector as Vector
import Data.Vector((!?), (!), (//), (++), Vector)
import Data.List()
import Data.Maybe
import qualified Data.Map as Map
import Data.Map(Map)
import qualified Data.Set as Set
import qualified Data.Graph.Inductive.Graph as Gr
import Data.Graph.Inductive.Graph((&))
import Data.Graph.Inductive.PatriciaTree(Gr)

newtype Element a = Element a
  deriving (Ord, Eq, Show)
newtype Set a = Set a
  deriving (Ord, Eq, Show)

newtype Node a b = Node (Set b, BitVector b)
  deriving Show

type BitVector b = Vector (Bool, [(Set b, Set b)])
type Pos = Int

data Instance a b
  = Instance (Gr (Node a b) ())
             (Map (Element a) Pos)
             (Map Pos (Element a))
             (Map (Set b) Gr.Node)
  deriving Show

empty :: Instance a b
empty = Instance Gr.empty Map.empty Map.empty Map.empty

zeroBitsOfLength :: Int -> BitVector b
zeroBitsOfLength k = Vector.replicate k (False, [])

zeroBits :: State (Instance a b) (BitVector b)
zeroBits = fmap zeroBitsOfLength bitlength

insertNode :: Ord b => Set b -> State (Instance a b) Gr.Node
insertNode v = do
  node <- zeroBits >>= \zerobits -> return (Node (v, zerobits))
  modify $ \(Instance gr tokmap invtokmap varmap) ->
    let n = Gr.noNodes gr
        varmap' = Map.insert v n varmap
    in Instance (Gr.insNode (n, node) gr) tokmap invtokmap varmap'
  gets $ \(Instance gr _ _ _) -> (Gr.noNodes gr - 1)

nodeOf :: Ord b => Set b -> State (Instance a b) Gr.Node
nodeOf v =
  gets (\(Instance _ _ _ m) -> Map.lookup v m) >>= \case
    Just node -> return node
    Nothing -> insertNode v

posOf :: Ord a => Element a -> State (Instance a b) Pos
posOf t = do
  (Instance gr tokmap invtokmap varmap) <- get
  case Map.lookup t tokmap of
    Just p -> return p
    Nothing -> do
      let p = Map.size tokmap
      put (Instance gr (Map.insert t p tokmap)
                       (Map.insert p t invtokmap)
                       varmap)
      return p

bitvectorOf :: Ord b => Set b -> State (Instance a b) (BitVector b)
bitvectorOf v = do
  node <- nodeOf v
  gets $ \(Instance gr _ _ _) ->
    let (Just (_, _, Node (_, bits), _), _) = Gr.match node gr
    in bits

bitlength :: State (Instance a b) Int
bitlength = gets $ \(Instance _ tokmap _ _) -> Map.size tokmap

isSet :: (Ord a, Ord b) => Set b -> Element a -> State (Instance a b) Bool
isSet v t = do
  p <- posOf t
  bits <- bitvectorOf v
  case bits !? p of
    Just (b, _) -> return b
    Nothing -> return False

pairs :: (Ord a, Ord b) => Set b -> Element a ->
           State (Instance a b) [(Set b, Set b)]
pairs v t = do
  p <- posOf t
  bits <- bitvectorOf v
  return $ snd $ entry bits p

insertPair :: (Ord a, Ord b) => (Set b, Set b) -> Set b -> Element a ->
                State (Instance a b) ()
insertPair pair v t = do
  node <- nodeOf v
  p <- posOf t
  bits <- bitvectorOf v
  k <- bitlength
  let bits' =
        case bits !? p of
          Just (b, pairs) -> bits // [(p, (b, pair : pairs))]
          Nothing -> let n = Vector.length bits
                         bits' = bits ++ zeroBitsOfLength (k - n)
                      in bits' // [(p, (False, [pair]))]
  modify $ \(Instance gr tokmap invtokmap varmap) ->
    let (Just (to, _, _, from), gr') = Gr.match node gr
    in Instance ((to, node, Node (v, bits'), from) & gr')
                tokmap invtokmap varmap

entry :: BitVector b -> Pos -> (Bool, [(Set b, Set b)])
entry bits p = fromMaybe (False, []) (bits !? p)

set :: (Ord a, Ord b) => Set b -> Element a -> State (Instance a b) ()
set v t = do
  node <- nodeOf v
  p <- posOf t
  bits <- bitvectorOf v
  k <- bitlength
  let n = Vector.length bits
      (bits', pairs) =
        if n > p then
          (bits // [(p, (True, []))], snd $ bits ! p)
        else let bits' = bits ++ zeroBitsOfLength (k - n)
             in (bits' // [(p, (True, []))], [])
  modify (\(Instance gr tokmap invtokmap varmap) ->
          let (Just (to, _, Node (_, _), from), gr') = Gr.match node gr
          in Instance ((to, node, Node (v, bits'), from) & gr')
                      tokmap invtokmap varmap)
  mapM_ insertEdge pairs

insertEdge :: (Ord a, Ord b) => (Set b, Set b) -> State (Instance a b) ()
insertEdge (src, dst) = do
  from <- nodeOf src
  to <- nodeOf dst
  srcBits <- bitvectorOf src
  let n = Vector.length srcBits
  modify $ \(Instance gr tokmap invtokmap varmap) ->
          Instance (Gr.insEdge (from, to, ()) gr) tokmap invtokmap varmap
  invtokmap <- gets $ \(Instance _ _ invtokmap _) -> invtokmap
  Vector.mapM_ (f invtokmap) $ Vector.zip (Vector.enumFromN 0 n) srcBits
  where f _ (_, (False, _)) = return ()
        f invtokmap (p, (True, _)) = set dst (invtokmap Map.! p)

data Constraint a b
  = Membership (Element a) (Set b)
  | Inclusion (Set b) (Set b)
  | CondInclusion (Element a) (Set b) (Set b) (Set b)

type Solution a b = Map (Set b) (Set.Set (Element a))

constraint :: (Ord a, Ord b) => Constraint a b -> Instance a b -> Instance a b
constraint (Membership t v) =
  execState $ do
    set v t
    ps <- pairs v t
    mapM_ insertEdge ps
constraint (Inclusion x y) =
  execState $ insertEdge (x, y)
constraint (CondInclusion t v x y) =
  execState $ do
    b <- isSet v t
    if b then insertEdge (x, y)
    else insertPair (x, y) v t

solution :: (Ord a, Ord b) => Instance a b -> Solution a b
solution (Instance gr _ invtokmap varmap) =
  Map.foldrWithKey extract Map.empty varmap
  where
    extract var node =
      let (Just (_, _, Node (_, bits), _), _) = Gr.match node gr
      in Map.insert var (Set.unions . Vector.toList $
                          Vector.imap (tokens var) bits)

    tokens _ p (True, _) = Set.singleton tok
      where tok = invtokmap Map.! p
    tokens _ _ (False, _) = Set.empty
