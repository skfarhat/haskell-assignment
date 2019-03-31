
* TODO: the lines cut in the pdf output - need to prevent that.
* TODO: be consistent as to whether there are spaces betwen the pluses
* TODO: be consistent with usage of pan and bucket
* TODO: we have lots of treeCmp, maybe we want to create a separate
function for that
* TODO: refactor to have on efunction for the maktee for
all 3 of them (a parametrized one)

> module CoinProblem where
> import Data.List (minimumBy, elemIndex)
> import Debug.Trace

2. States and tests
===================

> data State = Pair Int Int | Triple Int Int Int | Invalid
>   deriving (Eq, Show)

> data Test = TPair (Int, Int) (Int, Int) | TTrip (Int, Int, Int) (Int, Int, Int)
>   deriving (Eq, Show)

The 'valid' function below returns True only when its arguments are of types
- Pair and TPair
- Triple and TTrip

and when all below booleans are true:

- allPositive : all integers in Pair, Triple, TPair, TTrip instances are positive.
- sufficientCoins:  for both State-Test combinations, there must be at least as many coins
                    of each type in the State than there are in the Test.
- equalPans: the provided test must have an equal number of coins on both sides of the scale
- nonZero: the number of coins in each pan of the test is non-zero, since you also
            "learn nothing from weighing zero with zero".
            Note that it is sufficient to check sum[a,b] == 0 without sum[c,d] == 0
            because we have equalPans that enforces the latter (same for Triple case).

> valid :: State -> Test -> Bool
> valid (Pair u g) (TPair (a,b) (c,d)) = allPositive && equalPans && sufficientCoins && nonZero
>   where
>     allPositive = all (>=0) [u,g,a,b,c,d]
>     equalPans = sum[a,b] == sum[c,d]
>     sufficientCoins = sum[a,c] <= u && sum[b,d] <= g
>     nonZero = sum[a,b] /= 0
>
> valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = allPositive && equalPans && sufficientCoins && nonZero
>   where
>     allPositive = all (>=0) [l,h,g,a,b,c,d,e,f]
>     equalPans = sum[a,b,c] == sum[d,e,f]
>     sufficientCoins = sum[a,d] <= l && sum[b,e] <= h && sum[c,f] <= g
>     nonZero = sum[a,b,c] /= 0
>
> valid _ _ = False


3. Choosing and conducting a test
================================

Working through the coin problem, it is evident that some states are impossible to reach
and confirmation of this can be found in the coversheet section discussing the outcomes of
State=(Triple 3 0 6) with Test=(TTrip (0, 0, 3) (3, 0, 0)) which are [Triple 0 0 9,Triple 0 0 9,Triple 3 0 6].

First, let us discuss why the first two outcomes are invalid:

- The leftmost outcome occurs when the 3 genuine coins weighed less than the 3 coins that were once in a light pan (0,0,3) < (3,0,0).
  This outcome is impossible because in a TTrip test, a pan containing all genuine coins cannot weigh less than a pan with
  no suspect-heavy coins. Genuine coins are on the lighter side of the scale when weighed against
    (a) unknown coins in a TPair test
    (b) suspect-heavy coins in a TTrip test
- The middle outcome occurs if the pan with 3 genuines balances with the pan with 3 suspect-lights (0,0,3) == (3,0,0)
  Normally, it is possible for genuines to balance with suspects but in this case a balance implies all coins are genuine,
  which is impossible in a Triple state. We have already seen the scales tip to one end in our of the earlier tests,
  so how are you telling me that all are genuine?


MkTriple
--------

Following on from the above, it is impossible to have a state (Triple 0 0 x) because that would imply all are genuine.

We create a function mkTriple to wrap around the Triple constructor.
The function checks the 'l' and 'h' parameters; if both are zero it returns an Invalid state instead of an invalid Triple state.
Hence, mkTriple (0 0 9) = Invalid.

Going forward, there should be no bare Triple constructors, instead mkTriple is employed.

> mkTriple :: Int -> Int -> Int -> State
> mkTriple l h g
>   | l == 0 && h == 0 = Invalid
>   | otherwise = Triple l h g


Outcomes
--------

Outcome is the critical function to get right in this problem.

We will first outline the unbreakable ground-rules before proceeding to other details.

For both state-test combinations (Pair-TPair and Triple-TTrip):

(1) An empty list is returned if the state-test combination is invalid according to our definition of 'valid'
(2) The genuine coins used in both pans of the test end up in the genuine bucket of the outcomes.
    For instance, in a TPair (a,b) (c,d) both b and d will end up in the genuine bucket of all outcome states,
    and for TTrip (a,b,c) (d,e,f), both c and f end up in the genuine bucket of all outcome states.
(3) Each of the outcomes must have the same number of coins in total as the starting state (of course!).
    We will compute this sum in our explanation to showcase that this invariant is held - but also for sanity
    checking our implementation.

The signature of outcomes is:

> outcomes :: State -> Test -> [State]

For the Pair-TPair case:

- If the pans balance (middle outcome), then we know that all coins on the scale are genuines.
  The unknowns ('a' and 'c') join the rest of the genuines, so we remove (us=a+c) from the unknowns and add them
  to the genuines (g+us)
- When the scale tips to one side, we know there's a counterfeit
  but we don't know if the counterfeit is heavier or lighter,
  so we move all those unknown on the heavy side to the
  suspect-heavy bucket ('h') and all those unknown on the
  light side to the suspect-light bucket ('l').
  As per (1) all genuines go back to the genuine pile.
  When (a,b) < (c,d), we move
    - 'a' to the light bucket 'l'
    - 'c' to the heavy bucket 'h'
    - all remaining unknowns (u-us) to the genuine bucket 'g'
  ending up with Triple a c (g+u-us)

  It is vice versa when (a,b) > (c,d), we get Triple c a (g+u-us)

  I'm sure we all get it. Super.

> outcomes (Pair u g) (TPair (a,b) (c,d))
>   | valid (Pair u g) (TPair (a,b) (c,d)) = [
>       mkTriple  a c (g+u-us),
>       Pair    (u-us) (g+us),
>       mkTriple  c a (g+u-us)
>     ]
>   | otherwise = []
>   where us = a + c

For the Triple-TTrip case, things are a little more complicated:

- When the pans balance (middle outcome = (a,b,c) = (d,e,f))
  we know that all coins on both sides of the scale are genuine,
  so we move all suspect-lights ('a' and 'd') and all suspect-heavies
  ('b' and 'e') to the genuine pile, ending up with
    - l - (a + d) in the light bucket
    - h - (b + e) in the heavy bucket
    - g + (a + d + b + e)
  Note, that c and f are not mentioned because we sort of did
  g - (c + f) + (c + f) = g, when we brought them back.
- When the left pan is ligher than the right pan (left outcome = (a,b,c) < (d,e,f))
    - all suspect-lights from the left pan 'a' go to the light bucket
    - all suspect-heavies from the right pan 'e' go the heavy bucket
    - the rest, and I mean *all the rest* goes to the genuine bucket.
      This means, (l-a) which is all of what remains of the suspect-lights,
      (h-e) which is all of what remains from the suspect-heavies
      end up in the genuines --> g = g + (l - a) + (h - e)
- When the right pan is heavier than the left pan (right outcomes = (a,b,c) > (d,e,f))
  It is essentially vice versa, but I'll go through it anyway.
      - all suspect-lights from the right pan 'd' go to the light bucket
      - all suspect-heavies from the left pan 'b' go the the heavy bucket
      - the rest goes to the genuine bucket. That is, g = g + (l - d) + (h - b)

TODO: figure out how best to neaten this up

> outcomes (Triple l h g) (TTrip (a,b,c) (d,e,f))
>   | valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = [
>       mkTriple a      e      $ g+(l-a)+(h-e),
>       mkTriple (l-l') (h-h') $ g+l'+h',
>       mkTriple d      b      $ g+(l-d)+(h-b)
>     ]
>   | otherwise = []
>   where
>     l' = a + d
>     h' = b + e


Weighings
---------

Next, we define the function weighings returning all sensible weighing
possiblities given a number of coins.

For a Pair-TPair test, we have the following contraints:

1. Both pans must have the same number of coins: a + b = c + d
2. One of the pans must not have genuine coins: b * d = 0
3. Only the lexically smaller of symmetrical weighings is returned
   e.g. return the former from TPair (0,1) (1,0) and TPair (1,0) (0,1)

The above can only be satisfied if d = 0, why?
Proof by contradiction, assume d /= 0.
From (2), we have b = 0 and (1) becomes a = c + d which means a > c
because d > 0 (remember d cannot be negative), but this contradicts (3).
So d cannot be non-zero, hence d is zero.

From the above, we have a + b = c and TPair (a,b) (c,d) becomes TPair (a,b) (a+b,0)

We can generate all combinations using list comprehension while ensuring the
below conditions remain satisfied:

- a + b /= 0
- 2a + b <= u
- b <= g

The highest possible value possible for 'a' is m = u `div` 2.
We can prove this by contradiction, assume a = m + 1
Then when u is even
```
  a = m + 1
  a = u/2 + 1
  2a = u + 2
  2a > u        (contradiction)
```
when u is odd,
```
  m = (u-1)/2
  m+1 = (u-1)/2 + 1
  a = (u+1)/2
  2a = u+1
  2a > u        (contradiction)
```
To be clear, not all combinations of a <- [0..m] and b <- [0..g] are valid,
we still need to filter out weighings where 2a + b > u or a + b = 0

As an example, we don't want `TPair (0,0) (0,0) or TPair (2,1) (3,0)`
in the output of `weighings (Pair 4 1)`.

> weighings :: State -> [Test]
> weighings (Pair u g) = [
>     TPair (a, b) (a+b, 0)
>       | a <- [0..m],
>         b <- [0..g],
>         a+b /= 0,
>         2*a+b <= u
>     ]
>   where m = u `div` 2

The Triple case is trickier and requires the subsidiary choices (defined further below).
We perform the cartesian product of the set `choices k (l,h,g)` with itself and
then filter TTrip combinations that do not satisfy the below conditions:

- c*f = 0
- a+b+c == d+e+f
- b+e <= h
- c+f <= g
- a+d <= l
- and the lexical ordering using (a,b,c) <= show (d,e,f)

Note that the set `choices k (l, h, g)` is generated once only and stored in 'ch', avoiding
repeated computations and saving time. TODO: perhaps mention that this saves xx% time.

> weighings (Triple l h g) = [
>     TTrip (a,b,c) (d,e,f)
>       | k <- [1..kr],
>         let ch = choices k (l, h, g),
>         (a,b,c) <- ch,
>         (d,e,f) <- ch,
>         c*f == 0,
>         a+b+c == d+e+f,
>         b+e <= h,
>         c+f <= g,
>         a+d <= l,
>         show (a,b,c) <= show (d,e,f)
>     ]
>     where kr = (l+h+g) `div` 2

> choices :: Int -> (Int, Int, Int) -> [(Int, Int, Int)]
> choices k (l, h, g) = [
>   (i,j,k-i-j)
>     | i <- [0..l],
>       j <- [0..h],
>       0 <= k-i-j && k-i-j <= g
>   ]


Ordering
--------

> instance Ord State where
>   compare Invalid         _                 = LT
>   compare _               Invalid           = GT
>   compare (Triple _ _ _)  (Pair _ _)        = LT
>   compare (Pair _ _) (    Triple _ _ _)     = GT
>   compare (Pair _ g1)     (Pair _ g2)       = compare g2 g1
>   compare (Triple _ _ g1) (Triple _ _ g2)   = compare g2 g1

We implement the function compare on our State datatype to allow
the implementation to judge whether certain tests help to progress towards a solution.

- Triple provides more information than Pair thus
  (Triple `compare` Pair = LT and Pair `compare` Triple = GT)
- Invalid is a terminal state, it provides ample information hence it is
  always the less than the other operand (Invalid `compare` _ = LT) and (_ `compare` Invalid = GT)
- When comparing two instances of Pair, the one with more genuine coins provides more information
  and should be the lesser of the two. The result of comparing 2 Pairs is the opposite of comparing their
  genuine coins, hence Pair u1 g1 `compare` Pair u2 g2 = g2 `compare` g1
- Same as above but for comparing a pair of Triples. The Triple with most genuines is
  closer to the solution, thus Triple _ _ g1 `compare` Triple _ _ g2 = compare g2 g1


Productive
----------

The function productive returns True when all outcomes from a Test on a State move us closer
to the solution.

To implement this, we generate the list of outcomes of the State-Test pair
and check whether all state outcomes are strictly less than the original state.

We use the higher-order function `all` from Prelude which takes in a function (a->Bool) and a list,
and applies the function on each element of the list producing a boolean. If all returned booleans are
true `all` returns True, otherwise it returns False.

The function applied to each outcome is `(<s)` shorthand for `(\x -> x < s)`.

> productive :: State -> Test -> Bool
> productive s t = all (<s) $ outcomes s t


Tests
-----

Tests returns a list of all productive weighings for a State s.
With `weighings` as well as `productive` implemented, this function
becomes trivial: we simply get all weighings then filter out all those
deemed unproductive.

> tests :: State -> [Test]
> tests s = filter (productive s) $ weighings s


4. Decision trees
=================

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
> height (Node _ nodes) = 1 + maximum (map height nodes)


11. Define a function

> minHeight :: [Tree] -> Tree
> minHeight trees = minimumBy treeCmp trees
> 		where
> 			treeCmp t1 t2 = height t1 `compare` height t2

An alternative definition (TODO: check why elemIndex is failing)

> -- minHeight' :: [Tree] -> Tree
> -- minHeight' trees = trees !! elemIndex smallest
> -- 		where smallest = minimum $ map height trees

that returns the tree of minimum height from a non-empty list of trees.

12. Hence define a function

> s1 = Pair 12 0
> tt = tests s1
> newTrees t = map mktree $ outcomes s1 t
> f1 t = Node t $ newTrees t

> minHeightOrMe :: Tree -> [Tree] -> Tree
> minHeightOrMe t [] = t
> minHeightOrMe _ s = minHeight s

Used for debugging

> traceIt s = trace ("->" ++ show s)
> traceIt1 s = trace ("--> " ++ show s ++ "\n=================\n")

> mktreeDebug :: State -> Tree
> mktreeDebug s
>     | final s || (length allTests == 0) = Stop s
>     | otherwise = traceIt s $ minHeight $ map testToTree allTests
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
>           treeCmp t1 t2 = heightH t1 `compare` heightH t2

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
>           treeCmp t1 t2 = heightH t1 `compare` heightH t2


6. A greedy solution
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
>     | otherwise = filter (\x -> height x == h) allTrees
>       where
>         h = height $ minHeight allTrees
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

