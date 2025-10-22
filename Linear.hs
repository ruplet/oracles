{-# LANGUAGE LinearTypes #-}
module Linear where

import qualified Prelude as P

-- We define our own bitstring type to represent integers,
-- as operations from Prelude on Int are *not* linear and don't typecheck.

-- Bitstrings (little-endian)
data Bit  = Zero | One deriving (P.Show, P.Eq)
data Bits = End     -- 0 (empty)
          | B0 Bits -- prepend 0-bit as LSB
          | B1 Bits
  deriving (P.Show)

burn :: Bits %1-> ()
burn End      = ()
burn (B0 xs)  = burn xs
burn (B1 xs)  = burn xs

evenBits :: Bits %1-> P.Bool
evenBits End      = P.True
evenBits (B0 xs)  = case burn xs of () -> P.True
evenBits (B1 xs)  = case burn xs of () -> P.False

bits5 :: Bits
bits5 = B1 (B0 (B1 End))

bits6 :: Bits
bits6 = B0 (B1 (B1 End))

half :: Bits %1-> Bits
half End      = End
half (B0 xs)  = xs
half (B1 xs)  = xs

plus2x1 :: Bits %1-> Bits
plus2x1 x = B1 x


branchConst :: Bits %1-> Bits
branchConst x =
  if evenBits x
    then bits5
    else bits6

collatzBad :: Bits %1-> Bits
collatzBad x =
  if evenBits x
    then half bits5       -- ERROR: x already consumed by 'evenBits x'
    else plus2x1 bits5    -- ERROR: x already consumed by 'evenBits x'

collatzBad :: Bits %1-> Bits
collatzBad x =
  if evenBits x
    then half x       -- ERROR: x already consumed by 'evenBits x'
    else plus2x1 x    -- ERROR: x already consumed by 'evenBits x'