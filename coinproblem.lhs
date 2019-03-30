> module CoinProblem where

> import Data.List (minimumBy)
> import Data.List (elemIndex) -- imported by non-essential functions
> import Debug.Trace

We therefore model the state of the simulation by the datatype State:

> data State = Pair Int Int | Triple Int Int Int | Invalid
>   deriving (Eq, Show)

> data Test = TPair (Int, Int) (Int, Int) | TTrip (Int, Int, Int) (Int, Int, Int)
>     deriving (Eq, Show)

> valid :: State -> Test -> Bool
> valid Invalid _ = False
> valid (Pair _ _) (TTrip _ _) = False
> valid (Triple _ _ _) (TPair _ _) = False
> valid (Pair u g) (TPair (a,b) (c,d)) = allPositive && equalPans && sufficientCoins
>       where
>           allPositive = all (>=0) [u,g,a,b,c,d]
>           equalPans = sum[a,b] == sum[c,d]
>           sufficientCoins = sum[a,c] <= u && sum[b,d] <= g
> valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = allPositive && equalPans && sufficientCoins
>       where
>           allPositive = all (>=0) [l,h,g,a,b,c,d,e,f]
>           equalPans = sum[a,b,c] == sum[d,e,f]
>           sufficientCoins = sum[a,d] <= l && sum[b,e] <= h && sum[c,f] <= g

TODO: do we need an otherwise at the last one above?

2. We represent the three outcomes of a test as a list. Define a function

> mkTriple :: Int -> Int -> Int -> State
> mkTriple a b c
>         | a == 0 && b == 0 = Invalid
>         | otherwise = (Triple a b c)

> outcomes :: State -> Test -> [State]
> outcomes (Pair u g) (TPair (a,b) (c,d))
>       | valid (Pair u g) (TPair (a,b) (c,d))
>           = [
>               mkTriple  a c (g+u-us),
>               Pair    (u-us) (g+us),
>               mkTriple  c a (g+u-us)
>             ]
>       | otherwise = []
>     where
>         us = a + c
>
> outcomes (Triple l h g) (TTrip (a,b,c) (d,e,f))
>     | valid (Triple l h g) (TTrip (a,b,c) (d,e,f))
>         = [
>               (mkTriple a e (g+l+h-a-e)),
>               (mkTriple l' h' (g+a+b+d+e)),
>               (mkTriple d b (g+l+h-b-d))
>           ]
>     | otherwise = []
>     where
>       l' = l - a - d
>       h' = h - b - e


to compute the three outcomes of a valid test. For example,
outcomes (Pair 12 0) (TPair (3, 0) (3, 0))
= [Triple 3 3 6, Pair 6 6, Triple 3 3 6]

TODO: Explain the 2*a+b <= u is (a+c) <= u and the c=a+b.

> weighings :: State -> [Test]
> weighings (Pair u g) = [TPair (a, b) (a+b, 0) | a <- [0..m], b <- [0..g], a+b /= 0, 2*a + b <= u]
>     where
>           m = u `div` 2
> weighings (Triple l h g) = [TTrip (a,b,c) (d,e,f)
>                                   | k       <- [1..krange],
>                                     (a,b,c) <- choices k (l, h, g),
>                                     (d,e,f) <- choices k (l, h, g),
>                                      b + e <= h,
>  									                   c + f <= g,
>                                      a + d <= l,
>                                      a + b + c == d + e + f,
>  									                   c * f == 0,
>                                      show (a,b,c) <= show (d,e,f)
> 								]
>
>     where
>           krange = (l+h+g) `div` 2

ANSWER:
-------
(why?):
If we take b = 0, then we have a = c + d according to condition (1)
With d != 0, we have c < a, but if c < a then (a,b) > (c,d) which violates condition (6)
Hence d == 0.


4. Define choices.

> choices :: Int -> (Int, Int, Int) -> [(Int, Int, Int)]
> choices k (l, h, g) = [(i,j,k-i-j) | i <- [0..l], j <- [0..h], (k-i-j) <= g && (k-i-j) >= 0]


6. Complete the definition of the ordering on State.

TODO: check if there is a neater way to do the below:

> instance Ord State where
>         compare Invalid _ = LT
>         compare _ Invalid = GT
>         compare (Pair _ _) (Triple _ _ _) 		= GT
>         compare (Triple _ _ _) (Pair _ _) 		= LT
>         compare (Pair _ g1) (Pair _ g2) 			= compare g2 g1
>         compare (Triple _ _ g1) (Triple _ _ g2) 	= compare g2 g1

-- > instance Eq TreeH where
-- >         compare

7. Define a predicate productive

> productive :: State -> Test -> Bool
> productive s t = all (<s) $ outcomes s t

8. Finally, we fulfill the third criterion by keeping only the productive tests
among the possible weighings; define the function tests to do this.

> tests :: State -> [Test]
> tests s = filter (\w -> productive s w) $ weighings s

4 Decision trees
================

> data Tree = Stop State | Node Test [Tree]
> 		deriving Show

9. Define a predicate

We could have defined final to just check u == 0 and assuming the function was called in a
valid state based on our definition (n>2) then all would be fine. But I believe it is more
correct to return 'false' if we are given `final (State 0 0)` or `final (State 0 1)`.

Looking at the tree, it is clear that a leaf State if:
	1) when it is Pair, u=0 and g=n
	2) when it is a Triple, (l=0 and h=1) or (l=1 and h=0) and g=(n-1)

The function is defined such that it has no context as to how many coins there are overall, so we cannot check
on the values of g to see that they are equal to n-1 or n.

TODO: Similarly with the Triple case, we cannot identify the counterfeit coin with only two, so we check the total number of coins.
TODO: Check if we want to make checks on the provided states before answering 'final'

> final :: State -> Bool
> final Invalid = True
> final (Pair u g) 		= u == 0
> final (Triple l h g) 	= foundSingleFake || allGenuine
> 			where
> 				foundSingleFake = (l + h == 1) && (l * h == 0)
> 				allGenuine = l == 0 && h == 0 && g /= 0

TODO: rephrase below.
We can make more checks on the value of g so that we reject
We could have defined final to just check u == 0 and assuming the function was called in a
valid state based on our definition (n>2) then all would be fine. But I believe it is more
correct to return 'false' if we are given `final (State 0 0)` or `final (State 0 1)`.

final (Pair u g) 		  = g > 1 && u == 0
final (Triple l h g) 	= g > 1 && (l + h == 1) && (l * h == 0)

to determine whether a State is final—that is, whether it has determined
either that all coins or genuine, or that one coin is fake, and in the latter case
which coin and whether it is light or heavy.

10. Define a function height

> height :: Tree -> Int
> height (Stop _) = 0
> height (Node _ nodes) = 1 + (maximum $ map height nodes)


TEST
----

Below is a test of the tree presented in the assignment.

> mrr = Node (TTrip (1,0,0) (1,0,0)) [Stop (Triple 1 0 7), Stop (Triple 0 1 7), Stop (Triple 1 0 7)]
> rr = Node (TTrip (0,0,1) (0,1,0)) [Stop (Triple 0 1 7), mrr, Stop (Triple 0 0 0)]
> rmr = Node (TTrip (1,0,0) (1,0,0)) (replicate 3 (Stop (Triple 1 0 7)))
> mmr = Node (TPair (0,1) (1,0)) [Stop (Triple 0 1 7), Stop (Pair 0 8), Stop (Triple 1 0 7)]
> lmr = Node (TTrip (0,1,0) (0,1,0)) (replicate 3 (Stop (Triple 0 1 7)))
> mr = Node (TPair (3,0) (3,0)) [lmr, mmr, rmr]
> mlr = Node (TTrip (1,0,0) (1,0,0)) [Stop (Triple 1 0 7), Stop (Triple 0 1 7), Stop (Triple 1 0 7)]
> lr = Node (TTrip (0,0,1) (0,1,0)) [ Stop (Triple 0 1 7) , mlr, Stop (Triple 0 0 0) ] -- the Triple 0 0 0 means invalid case
> root = Node (TPair (2,0) (2,0)) [ lr, mr ]
> testHeight = height root



11. Define a function

> minHeight :: [Tree] -> Tree
> minHeight trees = minimumBy treeCmp trees
> 		where
> 			treeCmp t1 t2 = (height t1) `compare` (height t2)

An alternative definition (TODO: check why elemIndex is failing)

> -- minHeight' :: [Tree] -> Tree
> -- minHeight' trees = trees !! elemIndex smallest
> -- 		where smallest = minimum $ map height trees

that returns the tree of minimum height from a non-empty list of trees.

12. Hence define a function

> s1 = Pair 12 0
> tt = tests s1
> newTrees t = map mktree $ outcomes s1 t
> f1 t = (Node t $ newTrees t)

> minHeightOrMe :: Tree -> [Tree] -> Tree
> minHeightOrMe t [] = t
> minHeightOrMe _ s = minHeight s

Used for debugging

> traceIt s = trace ("->" ++ show s)
> traceIt1 s = trace ("--> " ++ show s ++ "\n=================\n")

> mktreeDebug :: State -> Tree
> mktreeDebug s
>     | final s || (length allTests == 0) = Stop s
>     | otherwise = (traceIt s) $ minHeight $ map testToTree allTests
>       where
>         allTests = tests s
>         testToTree t = Node t $ map mktreeDebug $ outcomes s t


One that is cleaner:

> mktree :: State -> Tree
> mktree s
> 		| final s = Stop s
> 		| otherwise = minHeight $ map testToTree allTests
> 			where
> 				allTests = tests s
> 				testToTree t = Node t $ map mktree $ outcomes s t

To find the minimum tree,

s = Pair 12 0
t = tests s
putStr $ (unlines) $ map (show . outcomes s) t


5 Caching heights
==================

> data TreeH = StopH State | NodeH Int Test [TreeH]
>     deriving Show

> heightH :: TreeH -> Int
> heightH (StopH s) = 0
> heightH (NodeH h t ts) = h

> treeH2tree :: TreeH -> Tree
> treeH2tree (StopH s) = Stop s
> treeH2tree (NodeH h t ts) = Node t (map treeH2tree ts)

> nodeH :: Test -> [TreeH] -> TreeH
> nodeH t children = NodeH h t children
>       where
>         h = 1 + (maximum $ map heightH children)

> tree2treeH :: Tree -> TreeH
> tree2treeH (Stop s) = StopH s
> tree2treeH (Node t children) = nodeH t $ map tree2treeH children

TODO: convince yourself that heightH . tree2treeH = height

> mktreeHTrace :: State -> TreeH
> mktreeHTrace s
>     | final s = StopH s
>     | otherwise = traceIt1 s $ minimumBy treeCmp $ map testToTree allTests
>         where
>           allTests = tests s
>           testToTree t = nodeH t (map mktreeHTrace $ outcomes s t)
>           treeCmp t1 t2 = (heightH t1) `compare` (heightH t2)

TODO:
NOTE: I think this is wrong. we do minimumBy, but these should be the
children of the papa node.

TODO: minimumBy treeCmp is repeated twice, create a special function
for it.

> mktreeH :: State -> TreeH
> mktreeH s
>     | final s = StopH s
>     | otherwise = minimumBy treeCmp $ map testToTree allTests
>         where
>           allTests = tests s
>           testToTree t = nodeH t (map mktreeH $ outcomes s t)
>           treeCmp t1 t2 = (heightH t1) `compare` (heightH t2)


6 A greedy solution
===================

TODO: check if this is meant to be an and or an or
NOTES:
- why is it ab?
- are we sure ^ = &&

> optimal :: State -> Test -> Bool
> optimal (Pair u g) (TPair (a, b) (ab, 0))
>     = (2 * a + b <= p) && (u - 2 * a - b <= q)
>       where p = 3 ^ (t - 1)
>             q = (p - 1) `div` 2
>             t = ceiling (logBase 3 (fromIntegral (2 * u + k)))
>             k = if g == 0 then 2 else 1
> optimal (Triple l h g) (TTrip (a, b, c) (d, e, f))
>     = (a + e) `max` (b + d) `max` (l - a - d + h - b - e) <= p
>       where p = 3 ^ (t - 1)
>             t = ceiling (logBase 3 (fromIntegral (l + h)))

NOTE: we changed bestTests to return the optimal tests given a list
of tests for a State, not from the weighings as is written in the assignment.
This is the only way we have found it to work.
BUG: there's something wrong with bestTests or optimal, or both.

> bestTests :: State -> [Test]
> bestTests s = filter (\w -> optimal s w) $ tests s

We check the correctness of bestTests manually against our implementation in
previous sections (2,3,4). Obviously, if our implementations above are incorrect
then this would make our checks here meaningless but we take our chances.

Assuming a starting state (Pair 8 0).

The output of our bestTests is:
  bestTests = [TPair (2,0) (2,0),TPair (3,0) (3,0),TPair (4,0) (4,0)]
suggesting all tests in the list are optimal.

Our mktree (Pair 8 0) returns a single minimal tree, with Node TPair (2,0) (2,0)
so at least we know that the first in the list of bestTests is indeed a 'bestTest'.
Going back to our mktree implementation, the function uses minimumBy which returns
the **first** minimum element that it finds in the list.

We define mktrees, a modified version of mktree to return all trees that are minimum.
mktrees returns a list of Trees instead of a single one.

(TODO: maybe mktrees implementation can be improved below?)

> mktrees :: State -> [Tree]
> mktrees s
>     | final s = [Stop s]
>     | otherwise = filter (\x -> (height x) == h) allTrees
>       where
>         h = height $ minHeight $ allTrees
>         allTrees = map testToTree allTests
>         testToTree t = Node t $ map mktree $ outcomes s t
>         allTests = tests s

Note that we could also then remodify mktree to just become:
  mktree = head . mktrees

-- > map (height) mktrees (Pair 8 0)

--------------------------------------------------------

> mktreeG :: State -> TreeH
> mktreeG s
>     | final s = StopH s
>     | otherwise = nodeH optimalTest trees
>         where
>           optimalTest = head $ bestTests s
>           trees = map mktreeG $ outcomes s optimalTest

19. Define a function mktreesG :: State → [TreeH]

> mktreesG :: State -> [TreeH]
> mktreesG s = map (\t -> nodeH t (map mktreeG $ outcomes s t)) $ bestTests s

There is only one.
(Recall that Data.List.nub removes duplicates from a list. Hence, all those trees have height 3.) How many minimum-height decision trees are there for n = 12?

TODO: we have lots of treeCmp, maybe we want to create a separate
function for that

TEST:
------

> s4 = (Triple 2 2 4)
> w4 = head $ bestTests s4
> r4 = outcomes s4 w4

> choicesTest = choices 3 (2, 2, 2) == [(0,1,2),(0,2,1),(1,0,2),(1,1,1),(1,2,0),(2,0,1),(2,1,0)]
> weighingsTest1 = 5 == (length $ weighings (Triple 3 0 6))
> productiveTest = productive (Triple 3 0 6) (TTrip (0, 0, 3) (3, 0, 0)) == False
> outcomesTest1 = outcomes (Triple 3 0 6) (TTrip (0, 0, 3) (3, 0, 0)) `elem` [[Triple 0 0 9,Triple 0 0 9,Triple 3 0 6], [Invalid,Invalid,Triple 3 0 6]]
> outcomesTest2 = outcomes (Pair 12 0) (TPair (3,0) (3,0)) == [Triple 3 3 6,Pair 6 6,Triple 3 3 6]
> testsTest1 = 4 == (length $ tests(Triple 3 0 6))

==============================================================================

> testResultStr :: [Char] -> Bool -> [Char]
> testResultStr s b = (if b then  "✅ " ++ s ++ " passed." else "🚫 " ++ s  ++ " failed.") ++ "\n"

> runTests :: IO()
> runTests = do
>       putStr (testResultStr "choicesTest    " choicesTest)
>       putStr (testResultStr "weighingsTest1 " weighingsTest1)
>       putStr (testResultStr "outcomesTest1  " outcomesTest1)
>       putStr (testResultStr "outcomesTest2  " outcomesTest2)
>       putStr (testResultStr "productiveTest " productiveTest)
>       putStr (testResultStr "testsTest1     " testsTest1)

==============================================================================


TODO: refactor to have on efunction for the maktee for
all 3 of them (a parametrized one)

Solution from the book
-----------------------

Solution

The decision tree in Figure 4.101 presents an algorithm that solvesthe fake-coin puzzle for 12 coins in three weighings.
In this tree the coins arenumbered from 1 to 12.
Internal nodes indicate weighings, with the coins beingweighted listed inside the node.
For example, the root corresponds to the firstweighing in which coins 1, 2, 3, 4 and coins 5, 6, 7, 8 are put on the left and rightpan of the scale,
 respectively.
Edges to a node’s children are marked according tothe node’s weighing outcome:<means that the left pan’s weight is smaller thanthat of the right’s pan,
=means that the weights are equal,
 and>means that theleft pan’s weight is larger than that of the right pan.
Leaves indicate final outcomes:=means that all the coins are genuine,
 and a number followed by+or−meansthat the coin with that number is heavier or lighter, respectively.
A list above aninternal node indicates the outcomes that are still possible before the weighing indicated inside the node.
For example, before the first weighing either all the coinsare genuine (=) or each coin is either heavier (+) or lighter (−).



Talking to myself

Thurs 14 March:
---------------

So the issue I am trying to solve is why (Pair 3 0) has no solution;

> w1 = (Pair 3 0)
> ww1 = head $ weighings w1

ww1 = TPair (1,0) (1,0)

If I run:

> o1 = outcomes w1 ww1

I get: [Triple 1 1 1,Pair 1 0,Triple 1 1 1]

The first question is, why is that wrong?
