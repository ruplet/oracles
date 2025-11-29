{-# LANGUAGE LinearTypes #-} -- compilation: `ghc Linear.hs`, ghc >= 9.0.1
module Linear where
import Prelude

-- Define own bitstring type for ints, as operations from Prelude
-- on Int are *not* linear and will not typecheck.
data Bit  = Zero | One
data Bits = Nil | B0 Bits | B1 Bits  -- Prepend 0 or 1 as the LSB.
const_5 :: Bits = B1 (B0 (B1 Nil))
const_6 :: Bits = B0 (B1 (B1 Nil))

burn :: Bits %1-> ()
burn Nil      = ()
burn (B0 xs)  = burn xs
burn (B1 xs)  = burn xs

evenBits :: Bits %1-> Prelude.Bool
evenBits Nil      = Prelude.True
evenBits (B0 xs)  = case burn xs of () -> Prelude.True
evenBits (B1 xs)  = case burn xs of () -> Prelude.False

half :: Bits %1-> Bits
half Nil      = Nil
half (B0 xs)  = xs
half (B1 xs)  = xs

plus2x1 :: Bits %1-> Bits
plus2x1 x = B1 x

branchConst :: Bits %1-> Bits
branchConst x =
  if evenBits x
    then half const_5
    else plus2x1 const_6

-- collatzBad2 :: Bits %1-> Bits
-- collatzBad2 x =
--   if evenBits x
--     then half x       -- ERROR: x already consumed by 'evenBits x'
--     else plus2x1 x    -- ERROR: x already consumed by 'evenBits x'