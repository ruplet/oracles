import Control.Exception (Exception)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Identity (Identity)
import Control.Exception.Base (throw)
import Data.Functor.Identity (runIdentity)
import Control.Monad.Except (runExceptT)

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

data Exc =
  InvalidArgumentNumber
  | InvalidProjectionIndex
  | InvalidRecursionIndex
  deriving (Show)
instance Exception Exc

type IM = ExceptT Exc Identity

-- LSB first!, i.e. s[0] = LSB, s[n-1] = MSB
type Val = [Bit]

data Expr =
  EVal !Val
  | EFunc !Func ![Expr] ![Expr]
  deriving (Show)

eval :: Expr -> IM Val
eval (EVal v) = return v

eval (EFunc ZeroFunc (_:_) _) = throw InvalidArgumentNumber
eval (EFunc ZeroFunc [] (_:_)) = throw InvalidArgumentNumber
eval (EFunc ZeroFunc [] []) = return []

eval (EFunc Tail (_:_) _) = throw InvalidArgumentNumber
eval (EFunc Tail [] []) = throw InvalidArgumentNumber
eval (EFunc Tail [] (_:_:_)) = throw InvalidArgumentNumber
eval (EFunc Tail [] (safeArg:_)) = do
    result <- eval safeArg
    case result of
      [] -> return []
      (lsb:tail_) -> return tail_

eval (EFunc (Proj nNormalArgs nSafeArgs projIndex) normalArgs safeArgs)
  | length normalArgs /= nNormalArgs || length safeArgs /= nSafeArgs
    = throw InvalidArgumentNumber
  | projIndex < 1 || projIndex > nNormalArgs + nSafeArgs
    = throw InvalidProjectionIndex
  | projIndex <= nNormalArgs = eval $ normalArgs !! (projIndex - 1)
  | otherwise = eval $ safeArgs !! (projIndex - nNormalArgs - 1)

eval (EFunc AppendZero (_:_) _) = throw InvalidArgumentNumber
eval (EFunc AppendZero [] []) = throw InvalidArgumentNumber
eval (EFunc AppendZero [] (_:_:_)) = throw InvalidArgumentNumber
eval (EFunc AppendZero [] (safeArg:_)) = do
    result <- eval safeArg
    return (Zero : result)

eval (EFunc AppendOne (_:_) _) = throw InvalidArgumentNumber
eval (EFunc AppendOne [] []) = throw InvalidArgumentNumber
eval (EFunc AppendOne [] (_:_:_)) = throw InvalidArgumentNumber
eval (EFunc AppendOne [] (safeArg:_)) = do
    result <- eval safeArg
    return (One : result)

eval (EFunc Cond (_:_) _) = throw InvalidArgumentNumber
eval (EFunc Cond [] (e1:e2:e3:tl))
  | not (null tl) = throw InvalidArgumentNumber
  | otherwise = do
    result <- eval e1
    case result of
      (One:_) -> eval e2
      (Zero:_) -> eval e3
      [] -> eval e3
eval (EFunc Cond [] _) = throw InvalidArgumentNumber

eval (EFunc (Composition fm fn m ns f gs hs) normalArgs safeArgs)
  | length gs /= fm
    || length hs /= fn
    || length normalArgs /= m
    || length safeArgs /= sum ns = throw InvalidArgumentNumber
  | otherwise = do
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
    applyWithArities [] _ _ _ = throw InvalidArgumentNumber
    applyWithArities _ [] _ _ = throw InvalidArgumentNumber
    applyWithArities (f: fs) (n: ns) normal safeArgs = do
      let (currentSafe, remainingSafe) = splitAt n safeArgs
      head <- eval $ EFunc f normal currentSafe
      tail <- applyWithArities fs ns normal remainingSafe
      return $ EVal head : tail

eval (EFunc Recursion {} [] _) = throw InvalidArgumentNumber
eval (EFunc (Recursion m n g h0 h1 d0 d1) (timerExpr:normalArgs) safeArgs)
  | length normalArgs /= m
    || length safeArgs /= n = throw InvalidArgumentNumber
  | otherwise = do
    timer <- eval timerExpr
    if null timer
      then eval $ EFunc g normalArgs safeArgs
    else do
      let (h, d) = if head timer == Zero then (h0, d0) else (h1, d1)
      delta <- eval $ EFunc d (EVal (tail timer) : normalArgs) []
      let newNormal = EVal (drop (1 + length delta) timer) : normalArgs
      recursive <- eval $ EFunc (Recursion m n g h0 h1 d0 d1) newNormal safeArgs
      eval $ EFunc h (EVal (tail timer) : normalArgs) [EVal recursive]

runEval :: Expr -> Either Exc Val
runEval = runIdentity . runExceptT . eval