{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Problem4 where
import Data.List
import Data.Maybe (fromMaybe)

{-------------------------------------------------------------------------------

CS:3820 Fall 2021 Problem of the Week, Week 4
=============================================

This week's problem continues our development of data types and their
manipulation, further developing the idea of simple logical formulae.

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

Part 0: A type!
-----------------

We'll begin with the same type you constructed last week to represent logical
formulae.  To review, your datatype should (somehow) incorporate the following
cases:

    Syntax   |  Meaning
    ---------+------------------------------------------------
    P, Q, R  |  Propositional variable (any string)
    ¬ F      |  Negation of F (where F is any formula)
    F ∧ G    |  Conjunction of F and G
    F ∨ G    |  Disjunction of F and G

You should be able to (and it is not a violation of academic integrity to) reuse
last week's data type and functions directly here.

-------------------------------------------------------------------------------}

data Formula = Negate Formula
             | Var String
             | ConjLabel Formula Formula
             | DisjLabel Formula Formula
  deriving (Eq, Show)

-- Constructor functions

variable :: String -> Formula
variable = Var

neg :: Formula -> Formula
neg = Negate

conj, disj :: Formula -> Formula -> Formula
conj = ConjLabel
disj = DisjLabel

-- A few examples.

form1, form2, form3 :: Formula
form1 = neg (variable "X")
form2 = (neg (variable "X") `conj` variable "Y") `disj` variable "Z"
form3 = (variable "X" `disj` variable "Y") `conj` variable "Z"

{-------------------------------------------------------------------------------

Part 1: Evaluating formulae
---------------------------

Your first task in this problem is to write a function that computes the *value*
of a given formula---that is to say, whether the formula works out to `True` or
to `False`.  There is, however, one problem: our formulae contain propositional
variables.  So, if we're going to talk about what formulae mean, we have to talk
about what the propositional variables mean.

To give meanings to variables, we use an *environment*.  An environment is a
mapping of variables to their meanings---in our case, a mapping from `String`s,
corresponding to the propositional variables in formulae, to `Bool`s.  One way
we can represent mappings in Haskell is with lists of pairs, so we'll define
environment by the following:

-------------------------------------------------------------------------------}

type Environment = [(String, Bool)]

{-------------------------------------------------------------------------------

Now, you might imagine that you'll be writing an evaluation function with a type
like the following:

    eval :: Environment -> Formula -> Bool

And you will do that, but you'll discover two problems along the way.  The first
is once you get to evaluating a variable: how do you determine what value an
`Environment` associates with a given `String`?  You could write a function to
figure this out yourself, but there's also a function in the Prelude that will
do it for you:

    lookup :: Eq a => a -> [(a, b)] -> Maybe b

which in our case works out to:

    lookup :: String -> [(String, Bool)] -> Maybe Bool

That's almost what you want, but not quite---what's this `Maybe` business about?
`Maybe` is how Haskell represents computations that may not succeed---in this
case, you may try to look up a value that's not in the environment:

    lookup "A" [("B", True), ("C", False)]

The `lookup` function uses the `Maybe` type to capture these situations.  It's
defined as:

    data Maybe a = Just a | Nothing

In this case, for example:

>>> lookup "B" [("B", True), ("C", False)]
Just True

>>> lookup "A" [("B", True), ("C", False)]
Nothing

So what should your evaluation function do with propositional variables that
aren't defined in the environment?  We could propagate the failures on, writing
an evaluation function of the type

    eval :: Environment -> Formula -> Maybe Bool

but instead, let's just assume that propositional variables outside the
environment are all mapped to False.

-------------------------------------------------------------------------------}

eval :: Environment -> Formula -> Bool --Discrete definitions for the environment
eval environmentHelper (Var a) = fromMaybe False (lookup a environmentHelper) --Note: using fromMaybe to compare values and return any significant values of maybe
eval environmentHelper (Negate a) = not $ eval environmentHelper a --Negate the environment
eval environmentHelper (ConjLabel a b) = eval environmentHelper a && eval environmentHelper b --Conj the environment
eval environmentHelper (DisjLabel a b) = eval environmentHelper a || eval environmentHelper b --Disj the environment

-- >>> eval [("X", True), ("Y", False), ("Z", False)] form2
-- False

-- >>> eval [("X", True)] form2
-- False

-- >>> eval [("X", True), ("Y", True), ("Z", True)] form3
-- True

{-------------------------------------------------------------------------------

Part 2: Variables and environments
----------------------------------

Recall from discrete math that a formula is *unsatisfiable* if it is false for
*every* possible interpretation of its variables.  We're working towards writing
a (very naive!) unsatisfiability checker for our simple formulae.  Part 1 has
equipped us to check whether a formula is valid under *one* interpretation of
its variables.  Now we're going to have to figure out how to enumerate all the
interpretations of a formula's variables.

We'll get there in two steps.  First, you'll define a function

    vars :: Formula -> [String]

that returns a list of every variable name in a formula.  Be careful: you don't
want to repeat variable names, even if a variable appears multiple times.
Again, you've seen enough Haskell to do this yourself, but there's a Prelude
function that will make your life easier:

    nub :: Eq a => [a] -> [a]

`nub xs` computes a list that contains all the *unique* values in `xs`---no
repeats.  Next, you'll define a function


    environments :: [String] -> [Environment]

which computes every possible environment for a given list of variable names.
For example:

    environments ["A", "B"]
  ==>
    [ [("A", True), ("B", True)]
    , [("A", True), ("B", False)]
    , [("A", False), ("B", True)]
    , [("A", False), ("B", False)] ]

It's not important in which order your `environments` function returns these
environments, just that you return them all.  Think carefully about your base
case: which environments assign meaning to no variables?  You might find it
easiest to use some list comprehensions here, although you certainly don't have
to.

-------------------------------------------------------------------------------}

vars :: Formula -> [String]
vars (Var a) = [a] --Var a is a list of strings
vars (Negate b) = nub (vars b) --Note: Used nub to remove duplicate elements in string list
vars (ConjLabel b c) = nub (vars b ++ vars c) --See note // combines formulas b and c
vars (DisjLabel b c) = nub (vars b ++ vars c) --Also see note // combines formulas b and c

-- >>> vars form2    
-- ["X","Y","Z"]

helperFunctionEnv :: Int -> [[Bool]] -- converts ints into a bool to build environment
helperFunctionEnv 1 = [[True], [False]] --base case 1
helperFunctionEnv 2 = [[a,b] | a <- [True,False], b <- [True,False]] --base case 2
helperFunctionEnv z = [a:b | a <- [True,False], b <- helperFunctionEnv(z-1)] --Recursively populates the environment

environments ::[String] -> [Environment] --Defines and populates an environment
environments [] = [[]] -- Constructs an empty string list/environment to populate
environments variableList = [zip variableList x | x <- helperFunctionEnv(length variableList)] --Populates environment using booleans gathered from helper function


-- >>> environments (vars (variable "X" `conj` neg (variable "Y")))
-- [[("X",True),("Y",True)],[("X",True),("Y",False)],[("X",False),("Y",True)],[("X",False),("Y",False)]]

-- Remember: it's okay if you produced the environments in a different order
-- than I did!

{-------------------------------------------------------------------------------

Part 3: Unsatisfiability
--------------------------------------------------------------------------------

Now we've done most of the work, we just have to put the pieces together.  Your
final task is to write a function

    unsat :: Formula -> Bool

that returns `True` if the input formula is unsatisfiable---that is, if it
evaluates to `False` under every interpretation of the variables.  The only new
thing you might want here is the function:

    and :: [Bool] -> Bool

which returns `True` if every `Bool` in its input list is `True`, and `False`
otherwise.  Again, you may find a list comprehension helpful here.

-------------------------------------------------------------------------------}
unsatFormulaHelper :: Formula -> [Bool] --Helper to gather the enviornment to compare in main function
unsatFormulaHelper x = [eval y x | y <- environments(vars x)] --Evaluates the formula from vars and populats with bool from environment

unsat :: Formula -> Bool --Determines if formula is satisfiable or not
unsat unsatFormula | or (unsatFormulaHelper unsatFormula) = False --If not unsatasfiable = false
                   | not (or (unsatFormulaHelper unsatFormula)) = True --If unsatisfiable = true

-- >>> unsat form2
-- False

-- >>> unsat (variable "X" `conj` (variable "Y" `conj` (neg (variable "Y") `disj` neg (variable "X"))))
-- True

{-------------------------------------------------------------------------------

Of course, this isn't the most efficient way to determine unsatisfiability of a
logical formula: the number of environments we have to consider grows very
rapidly.  (How rapidly?)  But it serves to illustrate the idea, at least.

-------------------------------------------------------------------------------}
