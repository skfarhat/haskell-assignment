> import Data.List (minimumBy)
> import Data.List (elemIndex) -- imported by non-essential functions
> import Debug.Trace

1 Introduction
===============

This assignment is about a famous puzzle. It is called “Twelve Coins” in the
excellent book Algorithmic Puzzles by Anany and Maria Levitin (Oxford University
Press, 2011, Puzzle 142), and described as follows (I’ve made minor changes):
There are n > 2 coins, identical in appearance; either all are genuine,
or exactly one of them is fake. It is unknown whether the fake coin is
lighter or heavier than a genuine one. You have a two-pan balance
scale, without weights. The problem is to find whether all the coins are
genuine and, if not, to find the fake coin and to establish whether it is
lighter or heavier than the genuine ones. Design an algorithm to solve
the problem, in the minimum number of weighings.
Of course, with n = 0 there are no coins; with n = 1 you can’t weigh anything; and

with n = 2 you couldn’t distinguish a fake coin from a genuine one. So we assume
n > 2; the problem is usually presented with n = 12.
According to Algorithmic Puzzles, the puzzle first appeared in 1945, and it
has been alleged that this puzzle “diverted so much war-time scientific effort that
there was serious consideration of a proposal to inflict compensating damage by
dropping it in enemy territory”. I hope you find it fun!
My answers use a couple of functions from the standard libraries:

import Data.List (minimumBy, nub)
import Data.Ord (comparing)


2 States and tests
==================

The essence of our approach is to simulate a physical solution to the problem
that maintains up to four piles of coins:
pile U, of coins whose status is unknown;
pile G, of coins known to be genuine;
pile L, of coins that are possibly light (but
known not to be heavy);
and pile H, of coins that are possibly heavy (but known not to be light).

Initially, all the coins are in pile U; at the end, pile U is empty,
piles L and H have either zero or one coin together, and all the other coins are in
pile G. So if piles L and H are both empty, then all the coins are genuine; otherwise,
one of those piles is empty, the other has precisely one coin, that coin is fake, and
which pile it is in tells you whether it is light or heavy. The challenge now is to
find the best way of getting from the initial state to a final state.

However, we can be a bit more precise than just saying that there are four piles,
some empty, because the physical solution will go through two distinct phases. In
the first phase, we don’t know whether any coin is fake; it turns out that we need
consider only piles U and G.

Initially, all coins are in U. If the two groups balance the scales, we move 2k coins
from pile U to pile G and continue. If the two groups don’t balance, then one of those
2k coins must be fake; we move the k coins on the lighter pan of the scales to pile L,
the k coins on the heavier pan to pile H, and all the remaining coins in pile U to pile G.
We are now in the second phase, knowing that there is a fake coin; from this point, pile
U remains empty, and we need consider only piles L, H and G.

We therefore model the state of the simulation by the datatype State:

> data State = Pair Int Int | Triple Int Int Int
>   deriving (Eq, Show)

A state Pair u g represents there being u coins in pile U and g coins in pile G (and
piles L and H being empty). A state Triple l h g represents there being l coins in
pile L, h coins in pile H, and g coins in pile G (and pile U being empty). Moreover,
we only get into a state Triple l h g in the second phase, having deduced that there
is a fake coin; therefore l + h > 0 remains true.

The simulation proceeds by conducting ‘tests’, which consist of weighing one
group of k coins against another group of k coins. Because there are two kinds of
state, there are two kinds of test:

> data Test = TPair (Int, Int) (Int, Int) | TTrip (Int, Int, Int) (Int, Int, Int)
>     deriving (Eq, Show)

SAMI: I'm curious as to why we can't use 'Pair' and 'Triple' types as part of the signatures
of Test. Check if that works, and consider suggesting it in the assignment.

Each kind of test denotes how many coins to take, from which piles, for the left
and the right pan of the scales:
TPair (a, b) (c, d) denotes weighing a coins from pile U plus b coins from pile G against c
coins from pile U plus d coins from pile G;
TTrip (a, b, c) (d, e, f ) denotes weighing a + b + c coins from piles L,H,G
respectively against d, e, f coins from piles L,H,G.

For example, in the initial state Pair 12 0 for the n = 12 instance of the problem,
we can weigh 3 coins from pile U against 3 more coins from the same pile, represented
by the test TPair (3, 0) (3, 0). As the names suggest, a TPair test is only supposed to
be conducted in a Pair state, and a TTrip test in a Triple state. Moreover, in each test,
the number of coins should be the same in each pan of the scales (you learn nothing from
weighing 3 coins against 4). And finally, there must be sufficiently many coins in the various
piles for the test (you can’t use 7 coins from pile U when there are only 5 coins
left in it).

The below validTest function returns True if the provided Test type satisfies all below:
  - all of its elements are positive
  - the sum of elements on the right of the scale is equal to the that of the elements on the left of the scale

> countState (Pair a b) = sum [a,b]
> countState (Triple a b c) = sum [a,b,c]
> countTest (TPair (a,b) (c,d)) = sum [a,b,c,d]
> countTest (TTrip (a,b,c) (d,e,f)) = sum [a,b,c,d,e,f]

> validTest :: Test -> Bool
> validTest (TPair (a,b) (c,d)) = sum [a, b] == sum [c, d] && all (>=0) [a, b, c, d]
> validTest (TTrip (a,b,c) (d,e,f)) = sum [a, b, c] == sum [d, e, f] && all (>=0) [a, b, c, d, e, f]

The below validState function returns True if the provided State type satisfies all below:
  - all buckets have non-negative number of coins

> validState :: State -> Bool
> validState (Pair u g) = all (>=0) [u, g]
> validState (Triple l g h) = all (>=0) [l, g, h]

1. Define a function to determine whether a given test is valid in a given state, according to the
above criteria. For example, valid (Pair 12 0) (TPair (3, 0) (3, 0)) = True.

> valid :: State -> Test -> Bool
> valid (Pair _ _) (TTrip _ _) = False
> valid (Triple _ _ _) (TPair _ _) = False
> valid s t  = validState s && validTest t && countTest t <= countState s

TODO: do we need an otherwise at the last one above?


3 Choosing and conducting a test
================================

For each state s and test t such that valid s t = True, we now work out the possible
outcomes of test t in state s. There are always three possible outcomes, depending
on whether the coins in the left pan of the scales are lighter than, the same weight
as, or heavier than those in the right pan.
For example, conducting test TPair (3, 0) (3, 0) in state Pair 12 0 can go three
ways. If the 3 coins in the left pan are lighter than the 3 coins in the right pan, then
we know there is a fake coin among those 6 coins; we move the 3 coins in the left
pan to pile L, the 3 coins in the right pan to pile H, and the remaining 6 coins to
pile G, ending up in state Triple 3 3 6. Symmetrically, if the 3 coins in the left pan
are heavier than those in the right, we move the 3 coins in the left pan to pile H,
those in the right pan to pile L, and again the remaining 6 coins to pile G, again
ending up in state Triple 3 3 6. But if the pans balance, we know those 6 coins are
all genuine; so we move all 6 to pile G, and end up in state Pair 6 6.

2. We represent the three outcomes of a test as a list. Define a function

> outcomes :: State -> Test -> [State]
> outcomes (Pair u g) (TPair (a,b) (c,d))
>       | valid (Pair u g) (TPair (a,b) (c,d)) = [
> 													Triple a c (g+gs+u-us),
> 													Pair (u-us) (g+us+gs),
> 													Triple c a (g+gs+u-us)
> 												 ]
>       | otherwise = []
> 		where
> 				us = a + c
> 				gs = b + d
> outcomes (Triple l h g) (TTrip (a,b,c) (d,e,f))
> 		| valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = [		Triple (l'+a) (h'+e) 	(g'+b+c+d+f),		-- left < right
>																Triple (l'  ) (h')		(g'+a+b+c+d+e+f), 	-- left == right
>																Triple (l'+d) (h'+b)	(g'+a+c+e+f)		-- left > right
> 															]
> 		| otherwise = []
> 		where
> 			l' = l - a - d
> 			h' = h - b - e
> 			g' = g - c - f

For the Triple case, either

left < right: 										[ Triple (l' + a, 	h' + e, 	g' + (c+f)) ]
right > left: 										[ Triple (l' + d, 	h' + b, 	g' + (c+f)) ]
left = right: all move to genuine 					[ Triple (l', 		h', 		g' + (a+d+b+e+c+f)) ]

to compute the three outcomes of a valid test. For example,
outcomes (Pair 12 0) (TPair (3, 0) (3, 0))
= [Triple 3 3 6, Pair 6 6, Triple 3 3 6]

We now consider how to determine the tests that are both valid and sensible
in a given state. What do we mean by ‘sensible’? For one thing, there is no virtue
in having coins known to be genuine in both pans at once, because those coins
are known to have the same weight. For example, we can ignore tests of the form
TPair (a, b) (c, d) in which both b, d > 0: supposing b > d, it suffices to consider
just the test TPair (a, b − d) (c, 0) instead. Similarly, we can ignore tests of the
form TTrip (a, b, c) (d, e, f ) with c, f > 0.

Secondly, the scales are symmetric; so we don’t need to consider both the tests
TPair (a, b) (c, d) and TPair (c, d) (a, b). We can break the tie between these two
by picking the lexically ordered one, that is, with (a, b) <= (c, d) (remember that
pairs are ordered!). And similarly for TTrip tests.

A third criterion is that the test must be guaranteed to increase our knowledge
about the coins. For example, consider state Triple 3 0 6 and test TTrip (0, 0, 3) (3, 0, 0),
for which the three outcomes are [Triple 0 0 9, Triple 0 0 9, Triple 3 0 6]. The
third outcome is the same as the state we started with! In that case, we learned
nothing from the test; to avoid getting stuck in a loop, we want to avoid such
tests. (In fact, the outcome of this test is predetermined. The first two of these
three outcomes are actually impossible: the left pan contains three genuine coins,
the right pan contains three coins one of which is known to be light—because
it contains all the coins not known to be genuine—and so the left pan must be
heavier than the right pan. But this is hard to spot.)
We will define a function
weighings :: State -> [Test]
to generate the sensible tests according to the first two criteria in the first instance;
we will handle the third criterion after that.

3. In a state Pair u g, we want to generate tests TPair (a, b) (c, d) such that:
a + b = c + d     same number of coins per pan
a + b > 0         no point in weighing only air
b × d = 0         don’t put genuine coins in both pans
a + c <= u        enough unknown coins
b + d <= g        enough genuine coins
(a, b) <= (c, d)  symmetry breaker

The third equation above requires one of b, d to be 0; if we take b = 0 then
the last condition is satisfiable only if d = 0 too (why?), so instead we take
d = 0. That means that we’re looking for pairs (a, b) and (a + b, 0) such that
a + b != 0, 2a <= u, and b <= g. Complete the definition of the Pair clause of
weighings:
weighings (Pair u g) = [TPair (a, b) (a + b, 0) | ...]
For example,
∗) weighings (Pair 3 3)
[TPair (0, 1) (1, 0), TPair (0, 2) (2, 0), TPair (0, 3) (3, 0),
TPair (1, 0) (1, 0), TPair (1, 1) (2, 0)]

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
>  									   c + f <= g,
>                                      a + d <= l,
>                                      a + b + c == d + e + f,
>  									   c * f == 0,
>                                      show (a,b,c) <= show (d,e,f)
> 								]
>
>     where
>           krange = (l+h+g) `div` 2


> weighings' :: State -> [Test]
> weighings' (Triple l h g) = [TTrip (k,k,k) (k,k,k) | k <- [1..krange]]
> 		where
> 			krange = (l + h + g) `div` 2

ANSWER:
-------
(why?):
If we take b = 0, then we have a = c + d according to condition (1)
With d != 0, we have c < a, but if c < a then (a,b) > (c,d) which violates condition (6)
Hence d == 0.


4. The Triple case is a bit trickier. One approach is to define a subsidiary func-
tion choices such that choices k (l, h, g) returns all valid selections (i, j, k−i−j)
of k coins. That means 0 <= i <= l, 0 <= j <= h, and 0 <= k − i − j <= g.
choices :: Int → (Int, Int, Int) → [(Int, Int, Int)]
For example:
∗i choices 3 (2, 2, 2)
[(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 1, 1), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
Define choices.

> choices :: Int -> (Int, Int, Int) -> [(Int, Int, Int)]
> choices k (l, h, g) = [(i,j,k-i-j) | i <- [0..l], j <- [0..h], (k-i-j) <= g && (k-i-j) >= 0]

5. Now, in a state Triple l h g, we want to generate tests TTrip (a, b, c) (d, e, f )
such that:
a + b + c = d + e + f       same number of coins per pan
a + b + c > 0               no point in weighing only air
c × f = 0                   don’t put genuine coins in both pans
a + d <= l                  enough light coins
b + e <= h                  enough heavy coins
c + f <= g                  enough genuine coins
(a, b, c) <= (d, e, f )     symmetry breaker

We use choices to pick valid numbers of coin for each pan; suitable values
of k range from 1 to (l + h + g) ‘div‘ 2 (we have to have at least one coin in
each pan, and can’t have more than half the coins). Then for each suitable
k, we choose k coins (a, b, c) from (l, h, g) for the left pan, another k coins
(d, e, f ) from what’s left for the right pan, and make sure that c × f = 0 and
(a, b, c) <= (d, e, f ). Hence complete the Triple clause of weighings:
weighings (Triple l h g) = [TTrip (a, b, c) (d, e, f ) | ...]


6. Now for the third criterion, about making progress. We model this in terms
of a special-purpose ordering on states: s <s0 when state s gives strictly more
information about the coins than state s0. Because the number of coins is pre-
served, it generally suffices to do the comparison by the number of genuine
coins: two Pair states and two Triple states are ordered by their G compo-
nent (of course, more known-genuine coins means more information). We
say that a Triple state always gives more information than a Pair state (since
it represents progress, from the first to the second phase), and conversely
a Pair state never gives more information than a Triple state. Complete the
definition of the ordering on State.

TODO: check if there is a neater way to do the below:

> instance Ord State where
>         compare (Pair _ _) (Triple _ _ _) 		= GT
>         compare (Triple _ _ _) (Pair _ _) 		= LT
>         compare (Pair _ g1) (Pair _ g2) 			= compare g2 g1
>         compare (Triple _ _ g1) (Triple _ _ g2) 	= compare g2 g1


7. Define a predicate productive on states and tests such that productive s t
determines whether test t is guaranteed to make progress in state s, i.e.
every possible outcome is a state providing more information according to
the ordering above.

> productive :: State -> Test -> Bool
> productive s t = all (<s) $ outcomes s t

In particular, productive (Triple 3 0 6) (TTrip (0, 0, 3) (3, 0, 0) = False, as we
saw above.

8. Finally, we fulfill the third criterion by keeping only the productive tests
among the possible weighings; define the function tests to do this.

> tests :: State -> [Test]
> tests s = filter (\w -> productive s w) $ weighings s

We can also define tests using list comprehension as below:

tests :: State -> [Test]
tests s = [ w | w <- weighings s, productive s w]

For example, state Triple 3 0 6 admits 5 weighings, but one of these is
TTrip (0, 0, 3) (3, 0, 0), which is unproductive, so tests returns only 4 produc-
tive weighings.

4 Decision trees
================
Now we can set about running the simulation of the weighing process. From a
given start State, we build a decision tree of Tests, with final States at the leaves.
This is the type of tree we will start with:

> data Tree = Stop State | Node Test [Tree]
> 		deriving Show

Each Node will have precisely three children, for the three possible outcomes of
that test. We want to build a tree of minimum height—that is, which minimizes
the length of the longest path from the root to any leaf—because that minimizes
the number of tests we have to conduct. For example, the minimum height tree
for n = 8 coins is:

(Each circled nodes shows a test, showing the number of coins drawn from the
two or three active piles for each pan of the scales. The branching is for whether
the outcome is that the left pan is lighter than, the same weight as, or heavier
than the right pan. Each leaf shows a final state, with the number of coins in each
active pile. For example, the middle leaf shows the final state with all 8 coins in
pile G; immediately to its right is a final state with one coin in pile L.)
This three demonstrates that three tests are sufficient for n = 8; also, three
tests are necessary, because there are 17 distinct final states (any one of the 8
coins could be light, or heavy, or they could all be genuine), and a ternary tree of
height k has at most 3k leaves.

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

final (Pair u g) 		= g > 1 && u == 0
final (Triple l h g) 	= g > 1 && (l + h == 1) && (l * h == 0)

to determine whether a State is final—that is, whether it has determined
either that all coins or genuine, or that one coin is fake, and in the latter case
which coin and whether it is light or heavy.

10. Define a function

data Tree = Stop State | Node Test [Tree]
	deriving Show


> height :: Tree -> Int
> height (Stop _) = 0
> height (Node _ nodes) = 1 + (maximum $ map height nodes)

to compute the height of a tree (such that the tree above has height 3).

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

> traceIt1 s = trace ("--> " ++ show s ++ "\n=================\n")

> mktree' :: State -> Tree
> mktree' s
> 		| final s 	= Stop s
> 		| otherwise = (traceIt s) $ (minHeight $ map (\t -> (Node t $ newTrees t)) allTests)
> 			where
> 				allTests = tests s
> 				newTrees t = map mktree' $ outcomes s t
> 				traceIt s = trace ("--> " ++ show s ++ "\n=================\n")
> 				-- newTrees ::  State -> Test -> [Tree]

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


to build a minimum-height decision tree of tests from a given start state s:
Stop if s is final, and otherwise generate all possible productive tests with
tests s, recursively build trees from the outcomes of each such test, and then
pick the one that yields the best tree overall.

5 Caching heights
==================
The program in the previous section works, but it is rather slow. It takes about 10
seconds on my (old) desktop to compute the minimum-height tree shown above
for n = 8, and I gave up waiting with n = 12. One small source of inefficiency is
that it is continually recomputing the heights of trees; it would be better to label
every tree with its height, so that the height can then be looked up in constant
time. To that end, we define the datatype
data TreeH = StopH State | NodeH Int Test [TreeH ]
deriving Show
with the intention that the label h in a tree NodeH h t ts is the height of the tree,
so that height can be computed in one step:
heightH :: TreeH → Int
heightH (StopH s)
 = 0
heightH (NodeH h t ts) = h
13. Define a function
treeH 2tree :: TreeH → Tree
to convert a labelled TreeH back to the corresponding Tree.
14. Define a ‘smart constructor’
nodeH :: Test → [TreeH ] → TreeH
that assembles a test and a 3-list of trees into a single tree, without recom-
puting heights from scratch.
15. Hence define a function
tree2treeH :: Tree → TreeH
as an inverse to treeH 2tree. Convince yourself that
heightH · tree2treeH = height
16. Now repeat Question 12, but for building a TreeH rather than a Tree.
mktreeH :: State → TreeH
Sadly, the results are disappointing—caching the heights in this way does not
actually save much time:
∗i : set + s
∗i mktree (Pair 8 0)
(9.34 secs, 3, 648, 121, 496 bytes)
∗i mktreeH (Pair 8 0)
(9.23 secs, 3, 578, 513, 216 bytes)

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

> mktreeH :: State -> TreeH
> mktreeH s
>     | final s = StopH s
>     | otherwise = traceIt1 s $ minimumBy treeCmp $ map testToTree allTests
>         where
>           allTests = tests s
>           testToTree t = nodeH t (map mktreeH $ outcomes s t)
>           treeCmp t1 t2 = (heightH t1) `compare` (heightH t2)


6 A greedy solution
===================
The inefficiency in our tree-building functions is not primarily down to recomput-
ing heights; more fundamentally, we try too many possible tests. It turns out that
a greedy algorithm is possible: that is, one that makes a simple local choice at
each step, while still ending up with an optimal solution overall. The details are
a bit messy, so I will simply present them here—I will provide a hint about where
they come from in the assessment reports.
The bottom line is that it is possible to identify a predicate optimal that takes
a state s and a valid test t for s and determines whether t is optimal:
optimal :: State → Test → Bool
optimal (Pair u g) (TPair (a, b) (ab, 0))
= (2 × a + b 6 p) ∧ (u − 2 × a − b 6 q)
where p = 3ˆ(t − 1)
q = (p − 1) ‘div‘ 2
t = ceiling (logBase 3 (fromIntegral (2 × u + k)))
k = if g == 0 then 2 else 1
optimal (Triple l h g) (TTrip (a, b, c) (d, e, f ))
= (a + e) ‘max‘ (b + d) ‘max‘ (l − a − d + h − b − e) 6 p
where p = 3ˆ(t − 1)
t = ceiling (logBase 3 (fromIntegral (l + h)))
17. Define a function
bestTests :: State → [Test ]
that returns only the optimal tests among the valid weighings for a state.
18. Hence define a function
mktreeG :: State → TreeH
to build a TreeH greedily, using only optimal tests. Since they are optimal,
you can pick any of them—for example, just pick the first—and don’t need
to try them all and choose the best. This is much better:
∗i mktreeG (Pair 8 0)
(0.01 secs, 782, 792 bytes)
∗i mktreeG (Pair 12 0)
(0.01 secs, 1, 387, 368 bytes)

19. Define a function
mktreesG :: State → [TreeH ]
that explores all possible optimal tests, returning a list of trees. You can
check that they do indeed all have minimum height:
∗i nub (map heightH (mktreesG (Pair 12 0)))
[3]
(Recall that Data.List.nub removes duplicates from a list. Hence, all those
trees have height 3.) How many minimum-height decision trees are there for
n = 12?

7 Guidance
===========
The purpose of the assignment is for you to demonstrate your understanding of
functional programming. In principle, you can do that without solving all of the
questions above; and there is no need for you to avail yourself of any of the hints,
if you can see a better way to do it. But if you’re not sure, I advise following the
steps above.
You may be able to find partial solutions to the problems on the web. You are
advised not to use them, or at least, don’t rely on them: they are often of dubious
quality, they are likely to implement slightly different specifications, they typically
won’t help your critical review, and most importantly they won’t help you learn
about functional programming. Whatever you do, do make sure you make clear
the source and the extent of any derivative material.
Your answer should take the form of a literate Haskell script (or several such
scripts, if you want to use modules). You should submit the code and commentary
interleaved, in the same file: the commentary should take the form of an essay,
with the code and examples as illustrations (like the course practicals, and this
assignment itself). Submit the literate script in two formats: as plain ASCII text,
so that it can be run, and as PDF, so that it is easy to print. You may use fancy
formatting in the PDF if you wish, but there is no need to do so—straightforward
conversion from ASCII to PDF is fine. If you do want to use fancy formatting, I
recommend using pandoc—see below. Please do make sure that the two formats
contain equivalent content, so that there is no need for me to compare them before
marking them.
Finally, please structure the PDF file so that there is a cover sheet which contains
only your name, the subject and date, and a note of the total number of pages.
Do not put any answer material on the cover sheet; begin your answer on a fresh
page. Avoid putting your name on any page except the cover page. Please number
the pages and sections.
8 Pandoc
I use L A TEX to format my teaching materials (like this assignment), and I recommend
it for complex documents like your dissertation. But it’s rather a sledgehammer for
a simpler document such as this assignment, and for such purposes I recommend
a tool called pandoc. This is an open-source set of translators between different
document formats, including Markdown, HTML, Word, and L A TEX. Moreover, it is
written in Haskell! In particular, you could write your assignment using Markdown
format, which is simultaneously valid (and legible) literate Haskell; and generate
the PDF for submission directly from this. I will make an example available on
SSTL.


9 Assessment criteria
The assignment is intended to determine, in order of decreasing importance:
• have you understood the fundamental tools of functional programming:
algebraic data types, pattern matching, higher-order functions, parametric
polymorphism, and lazy evaluation?
• have you demonstrated an ability to apply these fundamental tools and ac-
companying techniques to a particular case study?
• do you have the ability to present clear arguments supporting design deci-
sions and discussing trade-offs, concisely and precisely?
• how fluent is your expression in Haskell, and how elegant is the resulting
code?



Solution
The puzzle can be solved in two weighings.Start by taking aside one coin if n is odd and two coins if n is even. After that,
divide the remaining even number of coins into two equal-size groups and put them on the opposite pans of the scale. If they weigh the same,
 all these coins are genuine and the fake coin is among the coins set aside. So we can weigh the set-aside group of one or two coins against the same
 number of genuine coins: if the former weighs less,
 the fake coin is lighter; otherwise,
 it is heavier.If the first weighing does not result in a balance,
 take the lighter group and,
 if the number of coins in it is odd,
 add to it one of the coins initially set aside (which must be genuine). Divide all these coins into two equal-size groups and weigh them.If they weigh the same,
 all these coins are genuine and therefore the fake coin is heavier; otherwise,
 they contain the fake,
 which is lighter.Since the puzzle cannot,
 obviously,
 be solved in one weighing, the above algorithm solves it in the minimum possible number of weighings.



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
