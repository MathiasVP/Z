module Hash where
import Data.Map()
import Data.Foldable()
import Data.Hashable
import Unique
import Data.Bits

newtype Identifier = Identifier (String, UniqueInt)
  deriving (Eq, Ord, Show)

unIdentifier :: Identifier -> (String, UniqueInt)
unIdentifier (Identifier (s, u)) = (s, u)

instance Hashable Identifier where
  hashWithSalt n (Identifier (s, u)) =
    hashWithSalt n (s, u)

stringOf :: Identifier -> String
stringOf (Identifier (s, _)) = s

idOf :: Identifier -> UniqueInt
idOf (Identifier (_, u)) = u

identifier :: String -> UniqueInt -> Identifier
identifier s u = Identifier (s, u)

fromString :: String -> IO Identifier
fromString s = unique >>= \u -> return (Identifier (s, u))

placeholder :: String -> Identifier
placeholder s = Identifier (s, UniqueInt (-1))

-- Combining function from the boost library from C++
combine :: Int -> Int -> Int
combine h1 h2 = h1 + 0x9e3779b9 + (h2 `shiftL` 6) + (h2 `shiftR` 2)
