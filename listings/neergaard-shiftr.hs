-- Proposition 1. Let m and n by numbers in binary. Right shift shiftR(m : n) of
-- m by |n| and selection of bit |n| from m are definable in BCeps-.

-- shiftR(n : m) = m >> |n|
shiftR :: Func
shiftR =
  let g = Proj 0 1 1 in
  let d = oneNormalToZero in
  -- h(timer : recursive) = tail(recursive)
  let h = Composition 0 1 1 [1] Tail [] [Proj 1 1 2] in
  Recursion 0 1 g h h d d