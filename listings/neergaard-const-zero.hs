constZero :: Int -> Int -> Func
constZero 0 0 = ZeroFunc
constZero 0 nSafe =
  Composition 0 (nSafe + 1) 0 [nSafe, 0] (Proj 0 2 2) [] [Proj 0 nSafe 1, ZeroFunc]
constZero nNormal nSafe =
  let g = constZero (nNormal - 1) nSafe in
  let h = Proj nNormal 1 (nNormal + 1) in
  let d = Proj nNormal 0 1 in
  Recursion (nNormal - 1) nSafe g h h d d