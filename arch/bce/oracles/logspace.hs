-- Define data types for representing expressions in LF language
data Func =
  BaseFunction !BaseFunc
  -- safe affine composition
  -- Composition (f: N^{M, N} -> N), (g1, ..., gM: N^{m, 0} -> N),
  -- (h1: N^{m, n_1} -> N, ..., hN: N^{m, n_N} -> N)
  | Composition !Func ![Func] ![Func]
  -- safe affine course-of-value recursion
  -- Recursion (g: N^{m, n} -> N), (h0, h1: N^{m+1, 1} -> N),
  -- (d0, d1: N^{m + 1, 0})
  | Recursion !Func !Func !Func !Func !Func
  deriving Show

data Bit = Zero | One

-- Define data type for representing base functions
data BaseFunc =
  ZeroFunc
  | PFunc [Bit]
  | PiFunc Int [[Bit]] [[Bit]]
  | S0Func [Bit]
  | S1Func [Bit]
  | CFunc [Bit] [Bit] [Bit]
  deriving Show

main :: IO ()
main = do
  let plus = 
  -- div: plus, minus
