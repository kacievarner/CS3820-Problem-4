module Tests where

-- GHC
import System.Exit
import System.Environment
import Data.Char (isPunctuation)
import Data.List (sort)

-- External
import Test.HUnit
-- import Test.QuickCheck

-- Lib
import Problem4



a, b, c :: Formula
a = variable "a"
b = variable "b"
c = variable "c"

ab = ["a", "b"]
abc = ["a", "b", "c"]

allDistinct          :: [Formula] -> Bool
allDistinct []       = True
allDistinct (f : fs) = distinct f fs && allDistinct fs
  where
    distinct f [] = True
    distinct f1 (f2 : fs) = f1 /= f2 && distinct f1 fs


repeatNeg :: Int -> Formula -> Formula
repeatNeg 0 f = f
repeatNeg n f = neg (repeatNeg (n - 1) f)

con = foldr conj a [a, b, c]
dis = foldr disj a [c, b, a]

unnecessarilyComplicatedFormula :: (Formula -> Formula) -> Formula
unnecessarilyComplicatedFormula f = foldr disj con (map f [con, dis, con, dis])

envTT, envFF, envTF, envFT :: Environment
makeEnv vs bs = zip vs bs
envTT = makeEnv ab [True, True]
envFF = makeEnv ab [False, False]
envTF = makeEnv ab [True, False]
envFT = makeEnv ab [False, True]

p41 :: Test
p41 =  test [
    -- smart constructors have
    -- no runtime errors
   a        @?= a,
   neg a    @?= neg a,
   conj a b @?= conj a b,
   disj a b @?= disj a b,
   allDistinct [
       a,
       b,
       neg (neg a),
       neg a,
       neg b,
       conj a b,
       conj b a,
       disj a b,
       disj b a
       ] @? "Smart constructors construct distinct terms",

  -- Small step semantics
  eval envTF a          @?= True,
  eval envTF b          @?= False,
  eval envTF (neg a)    @?= False,
  eval envTF (neg b)    @?= True,
  -- empty env
  eval []    a          @?= False,
  -- And spec
  eval envTT (conj a b) @?= True,
  eval envTF (conj a b) @?= False,
  eval envFT (conj a b) @?= False,
  eval envFF (conj a b) @?= False,
  -- Or spec
  eval envTT (disj a b) @?= True,
  eval envTF (disj a b) @?= True,
  eval envFT (disj a b) @?= True,
  eval envFF (disj a b) @?= False,
  -- repeated negation
  eval envTF (repeatNeg 6 a)           @?= True,
  eval envTF (repeatNeg 7 a)           @?= False,
  eval envTF (repeatNeg 8 (conj a b))  @?= False,
  eval envTF (repeatNeg 9 (conj a b))  @?= True,
  eval envTF (repeatNeg 10 (disj a b)) @?= True,
  eval envTF (repeatNeg 11 (disj a b)) @?= False,
  -- for fun, again
  eval envTF (unnecessarilyComplicatedFormula id)          @?= True,
  eval envTF (unnecessarilyComplicatedFormula neg)         @?= True,
  eval envTF (unnecessarilyComplicatedFormula (conj c))    @?= False,
  eval envTF (unnecessarilyComplicatedFormula (disj c))    @?= True
  ]

p42 = test [
  (vars a)          @?=  ["a"],
  (vars (neg a))    @?=  ["a"],
  sort (vars (disj a b)) @?= ["a", "b"],
  sort (vars (conj a b)) @?= ["a", "b"],
  -- vars doesn't incur duplicates
  vars (conj a a) @?= ["a"],
  vars (disj a a) @?= ["a"],
  sort (vars (unnecessarilyComplicatedFormula id)) @?= ["a", "b", "c"],
  -- environments
  sort (environments ["a"]) @?= ([
                                    [("a", False)],
                                    [("a", True)]
                                 ]),
  sort (environments ["a", "b"]) @?=  ([
                                          envFF,
                                          envFT,
                                          envTF,
                                          envTT
                                       ]),
  sort (environments ["a", "b", "c"]) @?=  sort ([
                                          makeEnv abc [True, True, True],
                                          makeEnv abc [True, True, False],
                                          makeEnv abc [True, False, True],
                                          makeEnv abc [True, False, False],
                                          makeEnv abc [False, False, False],
                                          makeEnv abc [False, True, False],
                                          makeEnv abc [False, False, True],
                                          makeEnv abc [False, True, True]
                                       ])
  ]

cnf3 =
  (a `disj` b `disj` c) `conj`
  (a `disj` b `disj` (neg c)) `conj`
  (a `disj` (neg b) `disj` c) `conj`
  (a `disj` (neg b) `disj` (neg c)) `conj`
  ((neg a) `disj` b `disj` c) `conj`
  ((neg a) `disj` b `disj` (neg c)) `conj`
  ((neg a) `disj` (neg b) `disj` c) `conj`
  ((neg a) `disj` (neg b) `disj` (neg c))
  
p43 = test [
  unsat a @?= False,
  unsat (neg a) @?= False,
  unsat (conj a b) @?= False,
  unsat (disj a b) @?= False,
  unsat (conj a (neg a)) @?= True,
  unsat (conj (neg a) (disj a a)) @?= True,
  unsat (disj (neg a) a) @?= False,
  unsat (unnecessarilyComplicatedFormula id) @?= False,
  unsat cnf3 @?= True
  ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

argMap 1 = test [p41]
argMap 2 = test [p42]
argMap 3 = test [p43]

hd :: [a] -> Maybe a
hd (x : xs) = Just x
hd []       = Nothing

main :: IO ()
main = do
  args <- getArgs
  let
    tests = case read <$> (hd args) of
          Just x -> argMap x
          Nothing -> test [p41, p42, p43]
  results <- runTestTT tests
  if (errors results + failures results == 0)
    then
      exitWith ExitSuccess
    else
      exitWith (ExitFailure 1)
