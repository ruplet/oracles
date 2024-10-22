import Control.Exception (Exception)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Identity (Identity)
import Control.Exception.Base (throw)
import Data.Functor.Identity (runIdentity)
import Control.Monad.Except (runExceptT)
import System.IO.Unsafe (unsafePerformIO)
import Test.QuickCheck (quickCheck)
import Test.QuickCheck.Arbitrary (Arbitrary, arbitrary)

trace string e = unsafePerformIO $ do
  putStrLn string
  return e

-- Define data types for representing expressions in BCe language
data Func =
  ZeroFunc
  | Tail
  | Proj !Int !Int !Int
  | AppendZero
  | AppendOne
  | Cond
  | Composition !Int !Int !Int ![Int] !Func ![Func] ![Func]
  | Recursion !Int !Int !Func !Func !Func !Func !Func
  deriving (Show)

data Bit = Zero | One
  deriving (Eq, Show)

instance Arbitrary Bit where
  arbitrary = do
    b <- arbitrary
    return $ if b then One else Zero

data Exc =
  InvalidArgumentNumber !String
  | InvalidProjectionIndex
  | InvalidRecursionIndex
  deriving (Eq)

instance Show Exc where
  show (InvalidArgumentNumber s) = "Invalid argument number: " ++ s
  show InvalidProjectionIndex = "Invalid projection index"
  show InvalidRecursionIndex = "Invalid recursion index"
instance Exception Exc

type IM = ExceptT Exc Identity

-- LSB first!, i.e. s[0] = LSB, s[n-1] = MSB
type Val = [Bit]

valToInt :: Val -> Int
valToInt [] = 0
valToInt (Zero:rest) = 2 * valToInt rest
valToInt (One:rest) = 1 + 2 * valToInt rest

data Expr =
  EVal !Val
  | EFunc !Func ![Expr] ![Expr]
  deriving (Show)

eval :: Expr -> IM Val
eval (EVal v) = return v

eval (EFunc ZeroFunc (_:_) _) = throw $ InvalidArgumentNumber "ZeroFunc"
eval (EFunc ZeroFunc [] (_:_)) = throw $ InvalidArgumentNumber "ZeroFunc"
eval (EFunc ZeroFunc [] []) = return []

eval (EFunc Tail (_:_) _) = throw $ InvalidArgumentNumber "Tail"
eval (EFunc Tail [] []) = throw $ InvalidArgumentNumber "Tail"
eval (EFunc Tail [] (_:_:_)) = throw $ InvalidArgumentNumber "Tail"
eval (EFunc Tail [] (safeArg:_)) = do
    result <- eval safeArg
    case result of
      [] -> return []
      (lsb:tail_) -> return tail_

eval (EFunc (Proj nNormalArgs nSafeArgs projIndex) normalArgs safeArgs)
  | length normalArgs /= nNormalArgs || length safeArgs /= nSafeArgs
    = throw $ InvalidArgumentNumber "Proj"
  | projIndex < 1 || projIndex > nNormalArgs + nSafeArgs
    = throw InvalidProjectionIndex
  | projIndex <= nNormalArgs = eval $ normalArgs !! (projIndex - 1)
  | otherwise = eval $ safeArgs !! (projIndex - nNormalArgs - 1)

eval (EFunc AppendZero (_:_) _) = throw $ InvalidArgumentNumber "AppendZero"
eval (EFunc AppendZero [] []) = throw $ InvalidArgumentNumber "AppendZero"
eval (EFunc AppendZero [] (_:_:_)) = throw $ InvalidArgumentNumber "AppendZero"
eval (EFunc AppendZero [] (safeArg:_)) = do
    result <- eval safeArg
    return (Zero : result)

eval (EFunc AppendOne (_:_) _) = throw $ InvalidArgumentNumber "AppendOne"
eval (EFunc AppendOne [] []) = throw $ InvalidArgumentNumber "AppendOne"
eval (EFunc AppendOne [] (_:_:_)) = throw $ InvalidArgumentNumber "AppendOne"
eval (EFunc AppendOne [] (safeArg:_)) = do
    result <- eval safeArg
    return (One : result)

eval (EFunc Cond (_:_) _) = throw $ InvalidArgumentNumber "Cond"
eval (EFunc Cond [] (e1:e2:e3:tl))
  | not (null tl) = throw $ InvalidArgumentNumber "Cond"
  | otherwise = do
    result <- eval e1
    case result of
      (One:_) -> eval e2
      (Zero:_) -> eval e3
      [] -> eval e3
eval (EFunc Cond [] _) = throw $ InvalidArgumentNumber "Cond"

eval (EFunc (Composition fm fn m ns f gs hs) normalArgs safeArgs)
  | length gs /= fm
    || length hs /= fn
    || length normalArgs /= m
    || length safeArgs /= sum ns = throw $ InvalidArgumentNumber "Composition"
  | otherwise = do
    -- trace ("evaluating composition" ++ show f ++ show gs ++ show hs) $ return ()
    -- apply every g_i to whole normalArgs
    let transf :: Func -> IM Expr
        transf g = do
          result <- eval (EFunc g normalArgs [])
          return $ EVal result

    gsResults <- mapM transf gs
    -- apply every h_i to whole normalArgs and safeArgs[sum of previous n_is : sum of previous n_is + n_i]
    hsResults <- applyWithArities hs ns normalArgs safeArgs
    eval $ EFunc f gsResults hsResults

  where
    applyWithArities :: [Func] -> [Int] -> [Expr] -> [Expr] -> IM [Expr]
    applyWithArities [] _ _ _ = throw $ InvalidArgumentNumber $ "applyWithArities" ++ show (normalArgs, safeArgs, hs, ns)
    applyWithArities _ [] _ _ = throw $ InvalidArgumentNumber $ "applyWithArities" ++ show (normalArgs, safeArgs, hs, ns)
    applyWithArities (f: fs) (n: ns) normal safeArgs = do
      -- trace "applyWithArities1" $ return ()
      let (currentSafe, remainingSafe) = splitAt n safeArgs
      head <- eval $ EFunc f normal currentSafe
      if null fs
        then return [EVal head]
      else do
        tail <- applyWithArities fs ns normal remainingSafe
        return $ EVal head : tail

eval (EFunc Recursion {} [] _) = throw $ InvalidArgumentNumber "Recursion null"
eval (EFunc (Recursion m n g h0 h1 d0 d1) (timerExpr:normalArgs) safeArgs)
  | length normalArgs /= m = throw $ InvalidArgumentNumber "Recursion normalArgs"
  | length safeArgs /= n = throw $ InvalidArgumentNumber "Recursion safeArgs"
  | otherwise = do
    -- trace ("evaluating recursion" ++ show timerExpr) $ return ()
    timer <- eval timerExpr
    if null timer
      then do
        -- trace ("null timer " ++ show g) $ return ()
        eval $ EFunc g normalArgs safeArgs
    else do
      let (h, d) = if head timer == Zero then (h0, d0) else (h1, d1)
      delta <- eval $ EFunc d (EVal (tail timer) : normalArgs) []
      let newNormal = EVal (drop (1 + length delta) timer) : normalArgs
      -- trace ("new Normal: " ++ show newNormal) $ return ()
      recursive <- eval $ EFunc (Recursion m n g h0 h1 d0 d1) newNormal safeArgs
      eval $ EFunc h (EVal (tail timer) : normalArgs) [EVal recursive]

arity :: Func -> (Int, Int)
arity ZeroFunc = (0, 0)
arity Tail = (0, 1)
arity (Proj nNormalArgs nSafeArgs _) = (nNormalArgs, nSafeArgs)
arity AppendZero = (0, 1)
arity AppendOne = (0, 1)
arity Cond = (0, 3)
arity (Composition _ _ m ns _ _ _) = (m, sum ns)
arity (Recursion m n _ _ _ _ _) = (m + 1, n)

runEval :: Expr -> Either Exc Val
runEval = runIdentity . runExceptT . eval

-- Define some basic functions
identity :: Func
identity = Proj 1 0 1

prop_identity :: Val -> Bool
prop_identity elt = runTest identity [elt] [] == Right elt

-- function which takes one safe argument, and returns zero
oneSafeToZero :: Func
oneSafeToZero = Composition 0 2 0 [1, 0] (Proj 0 2 2) [] [Proj 0 1 1, ZeroFunc]
prop_oneSafeToZero :: Val-> Bool
prop_oneSafeToZero elt = runTest oneSafeToZero [] [elt] == Right []

oneNormalToZero :: Func
oneNormalToZero = 
  let g = ZeroFunc in
  let h = Proj 1 1 2 in
  let d = identity in
  Recursion 0 0 g h h d d
prop_oneNormalToZero :: Val -> Bool
prop_oneNormalToZero elt = runTest oneNormalToZero [elt] [] == Right []

oneNormalToOne :: Func
oneNormalToOne = 
  Composition 0 1 1 [0] AppendOne [] [oneNormalToZero]
prop_oneNormalToOne :: Val -> Bool
prop_oneNormalToOne elt = runTest oneNormalToOne [elt] [] == Right [One]

twoNormalToZero :: Func
twoNormalToZero = 
  let g = oneNormalToZero in
  let h = Proj 2 1 3 in
  let d = Proj 2 0 1 in
  Recursion 1 0 g h h d d
prop_twoNormalToZero :: Val -> Val -> Bool
prop_twoNormalToZero elt1 elt2 = runTest twoNormalToZero [elt1, elt2] [] == Right []

constZero :: Int -> Int -> Func
constZero 0 0 = ZeroFunc
constZero 0 nSafe = Composition 0 (nSafe + 1) 0 [nSafe, 0] (Proj 0 2 2) [] [Proj 0 nSafe 1, ZeroFunc]
constZero nNormal nSafe =
  let g = constZero (nNormal - 1) nSafe in
  let h = Proj nNormal 1 (nNormal + 1) in
  let d = Proj nNormal 0 1 in
  Recursion (nNormal - 1) nSafe g h h d d

prop_constZero00 :: Bool
prop_constZero00 = runTest (constZero 0 0) [] [] == Right []

prop_constZero01 :: Val -> Bool
prop_constZero01 safeArgs =
  runTest (constZero 0 1) [] [safeArgs] == runTest oneSafeToZero [] [safeArgs]

prop_constZero10 :: Val -> Bool
prop_constZero10 normalArgs =
  runTest (constZero 1 0) [normalArgs] [] == runTest oneNormalToZero [normalArgs] []

prop_constZero20 :: Val -> Val -> Bool
prop_constZero20 norm1 norm2 =
  runTest (constZero 2 0) [norm1, norm2] [] == runTest twoNormalToZero [norm1, norm2] []

prop_constZero11 :: Val -> Val -> Bool
prop_constZero11 norm safe =
  runTest (constZero 1 1) [norm] [safe] == Right []

constOne :: Int -> Int -> Func
constOne nNormal nSafe = Composition 0 1 nNormal [nSafe] AppendOne [] [constZero nNormal nSafe]

constListZero :: Int -> Int -> Func
constListZero nNormal nSafe = Composition 0 1 nNormal [nSafe] AppendZero [] [constZero nNormal nSafe]

prop_constOne00 :: Bool
prop_constOne00 = runTest (constOne 0 0) [] [] == Right [One]

prop_constOne01 :: Val -> Bool
prop_constOne01 safeArgs =
  runTest (constOne 0 1) [] [safeArgs] == Right [One]

prop_constOne10 :: Val -> Bool
prop_constOne10 normalArgs =
  runTest (constOne 1 0) [normalArgs] [] == Right [One]

prop_constOne11 :: Val -> Val -> Bool
prop_constOne11 norm safe =
  runTest (constOne 1 1) [norm] [safe] == Right [One]

-- function which takes nNormal normal arguments, nSafe safe arguments, and returns empty list
-- constantZero :: Int -> Int -> Func
-- constantZero nNormal nSafe = Composition 0 3 nNormal [nSafe, 0, 0] Cond [] hs
--   where hs = [Proj nNormal nSafe 1, ]

-- Proposition 1. Let m and n by numbers in binary. Right shift shiftR(m : n) of
-- m by |n| and selection of bit |n| from m are definable in BCε.

-- shiftR(n : m) = m >> |n|
shiftR :: Func
shiftR =
  let g = Proj 0 1 1 in
  let d = oneNormalToZero in
  -- h(timer : recursive) = tail(recursive)
  let h = Composition 0 1 1 [1] Tail [] [Proj 1 1 2] in
  Recursion 0 1 g h h d d

prop_shiftR :: Val -> Val -> Bool
prop_shiftR shift arg = runTest shiftR [shift] [arg] == Right (drop (length shift) arg)

-- selectWeak(n : m) = m[|n|]
select :: Func
select =
  Composition 0 3 1 [1, 0, 0] Cond [] [shiftR, constOne 1 0, constListZero 1 0]

prop_select :: Val -> Val -> Bool
prop_select shift arg =
  let expected = if length shift >= length arg then [Zero] else [arg !! length shift] in
  runTest select [shift] [arg] == Right expected

headNormal :: Func
headNormal =
  let g = ZeroFunc in
  let h0 = constListZero 1 1 in
  let h1 = constOne 1 1 in 
  let d = identity in
  Recursion 0 0 g h0 h1 d d

prop_headNormal :: Val -> Bool
prop_headNormal [] = runTest headNormal [[]] [] == Right []
prop_headNormal elt = runTest headNormal [elt] [] == Right [head elt]

headSafe :: Func
headSafe =
  Composition 1 1 0 [1] select [constZero 0 0] [Proj 0 1 1]

prop_headSafe :: Val -> Bool
prop_headSafe [] = runTest headSafe [] [[]] == Right [Zero]
prop_headSafe elt = runTest headSafe [] [elt] == Right [head elt]


-- Proposition 2. Let b be either 0 or 1. The following function is representable
-- in BCε:

-- setb(m, n:) = set mth LSD of n to b
-- setb(m, n:) = shiftR(n: m) -> empty? return n, else return 
-- h(t, n: g(n))
set :: Bit -> Func
set b =
  Composition fm 0 2 [] (f(x,y:) = x empty? y else ) [gs] []
-- set b =
--   let g = if b == Zero then AppendZero else AppendOne in
--   -- h0(counter, n : recursive) = append0 to recursive
--   let h0 = Composition 0 1 2 [1] AppendZero [] [Proj 2 1 3] in
--   let h1 = Composition 0 1 2 [1] AppendOne [] [Proj 2 1 3] in
--   let d = twoNormalToZero in
--   Recursion 1 0 g h0 h1 d d

prop_set :: Bit -> Val -> Val -> Bool
prop_set bit shift arg =
  let n = length arg in
  let expected = if length shift >= n then arg else take n arg ++ [bit] ++ drop (n + 1) arg in
  runTest (set bit) [shift, arg] [] == Right expected

-- cond przyjmuje dwa argumenty: funkcje f i g, obie arności (0, 1)
cond :: Func -> Func -> Func
cond fComp gComp =
  let g = Proj 0 1 1 in
  let d = Proj 1 0 1 in
  -- h0 (_ : n) = g(n)
  -- Composition M N m [ni] f [gi] [hi]
  -- note: M, N could be implicitly deducted from the arity of f
  -- same with m and ni
  let h0 = Composition 0 1 1 [1] gComp [] [Proj 1 1 2] in
  -- h1 (_ : n) = f(n)
  let h1 = Composition 0 1 1 [1] fComp [] [Proj 1 1 2] in
  Recursion 0 1 g h0 h1 d d

prop_cond :: Val -> Val -> Bool
prop_cond [] _ = True
prop_cond m@(Zero : _) n =
  runTest (cond (constOne 0 1) (constListZero 0 1)) [m] [n] == Right [Zero]
prop_cond m@(One : _) n =
  runTest (cond (constOne 0 1) (constListZero 0 1)) [m] [n] == Right [One]

makeArgs :: [[Integer]] -> [[Integer]] -> ([Expr], [Expr])
makeArgs normalArgs safeArgs = (map (EVal . map toBit) normalArgs, map (EVal . map toBit) safeArgs)
  where
    toBit 0 = Zero
    toBit 1 = One
    toBit _ = error "toBit: invalid argument"

runTest :: Func -> [Val] -> [Val] -> Either Exc Val
runTest f normalArgs safeArgs = runEval $ EFunc f (map EVal normalArgs) (map EVal safeArgs)

manualTest :: Func -> [[Integer]] -> [[Integer]] -> Either Exc [Integer]
manualTest f normalArgs safeArgs = do
  let args = makeArgs normalArgs safeArgs
  result <- runEval $ uncurry (EFunc f) args
  return $ map fromBit result
  where
    fromBit Zero = 0
    fromBit One = 1

main :: IO ()
main = do
  quickCheck prop_identity
  quickCheck prop_oneSafeToZero
  quickCheck prop_oneNormalToZero
  quickCheck prop_twoNormalToZero
  quickCheck prop_shiftR
  quickCheck prop_select
  quickCheck prop_oneNormalToOne
  quickCheck prop_constZero00
  quickCheck prop_constZero01
  quickCheck prop_constZero10
  quickCheck prop_constZero11
  quickCheck prop_constZero20
  quickCheck prop_constOne00
  quickCheck prop_constOne01
  quickCheck prop_constOne10
  quickCheck prop_constOne11
  quickCheck prop_headNormal
  quickCheck prop_headSafe
  quickCheck prop_cond
  quickCheck prop_set

