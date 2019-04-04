
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
- When the left pan is lighter than the right pan (left outcome = (a,b,c) < (d,e,f))
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
possibilities given a number of coins.

For a Pair-TPair test, we have the following constraints:

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
We perform the Cartesian product of the set `choices k (l,h,g)` with itself and
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

TODO: mention that we can do this because of currying.
Was it currying? Check.

4. Decision trees
=================


> data Tree = Stop State | Node Test [Tree]
> 		deriving Show


Final
-----

In this coin problem, we set out to identify the counterfeit coin (if it were present) and determine whether it was lighter or heavier than the remaining genuine coins. Our final states are:

* (Pair 0 x): no counterfeit coins were found. Zero unknowns and the rest genuines
* (Triple 1 0 x): we found a single light counterfeit coin
* (Triple 0 1 x): we found a single heavy counterfeit coin

From the above, we can define the function `final` to return True if we reach a final state.

> final :: State -> Bool
> final Invalid         = True
> final (Pair u _)      = u == 0
> final (Triple l h _)  = foundSingleFake || allGenuine
>   where
>     foundSingleFake   = (l + h == 1) && (l * h == 0)
>     allGenuine        = l == 0 && h == 0

As our `final` function ignores the number of genuine coins provided merely checking the unknowns in a Pair state,
and the lights and heavies in the Triple state, it may return odd results when presented with invalid States, such as
`(Pair 0 0)` for which it will return `True`, `Triple (1 0 1)` for which it will return `True` and any state with invalid
number of genuine coins. This is understood and expected.

Height
------

To return the height of the tree, we simply return 1 + the maximum height of each of its child subtrees.
So we,

1) apply the function height on each of the node's subtrees: map height children
2) return 1 + the maximum of height returned from the children: 1 + maximum (map height children)

As with all recursive functions, we need a base case to terminate at, this happens when we reach a Stop node
whose height is zero.

> height :: Tree -> Int
> height (Stop _) = 0
> height (Node _ children) = 1 + maximum (map height children)


MinHeight
---------

Next we define a function `minHeight` to return the tree with the minimum height.

We use the higher-order function `minimumBy` which accepts a comparator function
telling it how to compare two elements, and a list of elements from which the minimum
will be returned.

Our where function defines the comparator `treeCmp` which given two tree instances,
returns LT, EQ, or GT based on which has the shorter/longer height.

> minHeight :: [Tree] -> Tree
> minHeight trees = minimumBy treeCmp trees
> 		where treeCmp t1 t2 = height t1 `compare` height t2

We could have defined minimumBy ourselves:

TODO: explain what our own implementation is.

> -- minHeight' :: [Tree] -> Tree
> -- minHeight' trees = trees !! (fromJust $ elemIndex smallest)
> -- 		where smallest = minimum $ map height trees

that returns the tree of minimum height from a non-empty list of trees.

MkTree
------

> mktree :: State -> Tree
> mktree s
>     | final s = Stop s
>     | otherwise = minHeight $ map test2Tree testList
>       where
>         testList = tests s
>         test2Tree t = Node t $ map mktree $ outcomes s t


The function can be implemented by taking each segment from the statement
and writing the functional code addressing it:

_Stop if s is final_
Our guard statement
| final s = Stop s
handles this. This is the base case for the recursive `mktree` function.

_otherwise generate all possible productive tests with tests s_
`testList = tests s`

_recursively build trees from the outcomes of each such test_
We create a function test2Tree which, given a test `t` and the state s
  (through the scope) constructs and returns a node with arguments:
  1. the test `t`
  2. a list of trees each built from one of the outcomes of test `t` on state `s`.
    We apply the function `mktree` (recursively) on each outcome ending up with:
    `map mktree $ outcomes s t`
And the overall function `test2Tree t = Node t $ map mktree $ outcomes s t`

_pick the one that yields the best tree overall._
Finally we glue the different components together@
  - apply `test2Tree` to each test in testList, this returns a list
  - return the tree with the shortest height from the above list


5 Caching heights
==================

> data TreeH = StopH State | NodeH Int Test [TreeH]
>     deriving Show

> heightH :: TreeH -> Int
> heightH (StopH s) = 0
> heightH (NodeH h t ts) = h


TreeH2tree
----------

> treeH2tree :: TreeH -> Tree
> treeH2tree (StopH s) = Stop s
> treeH2tree (NodeH h t ts) = Node t $ map treeH2tree ts

TODO: check whether it is node-type/instance?

We use pattern matching to detect the node type here.

For a StopH node, we return the equivalent Stop node (they both have the same state),
so `treeH2tree (StopH s) = Stop s`

For a NodeH node, we convert it to Node dropping the cached height,
and then calling treeH2tree on each of its child nodes:
`treeH2tree (NodeH h t ts) = Node t $ map treeH2tree ts`


NodeH
------

> nodeH :: Test -> [TreeH] -> TreeH
> nodeH t children = NodeH h t children
>   where h = 1 + (maximum $ map heightH children)

This is the crucial differentiator between Tree and TreeH.
When creating a NodeH, we label it with its height to avoid
repetitive computations later on.

The height of a node is one plus the maximum height of it children
`h = 1 + maximum $ map heightH children`.


Tree2treeH
----------

> tree2treeH :: Tree -> TreeH
> tree2treeH (Stop s) = StopH s
> tree2treeH (Node t children) = nodeH t $ map tree2treeH children

Again we use pattern matching to detect the node type here.

For a Stop node, we return the equivalent StopH node with the same state.

For a (Node t children), we apply the function `tree2treeH` on all of its children (recursion)
and the result is a list of TreeHs. At this point we just call our smart-constructor passing
the test `t` and the list of TreeHs. The smart-constructor takes care of computing the height and
returning a NodeH. That's the point of 'smart-constructor' it does the dirty-work of this function.

TODO: convince yourself that heightH . tree2treeH = height

```
height (Stop s) = 0
(heightH . tree2treeH) $ Stop s = heightH (tree2treeH $ Stop s)
                                = heightH (StopH s)
                                = 0                             -- matches the pattern in heightH)
```

```
(heightH . tree2treeH) $ Node t children
= heightH (tree2treeH $ Node t [N1, N2, N3])                                  -- tree2treeH applied on (Node t children)
= heightH (nodeH t $ map tree2treeH [N1, N2, N3])                             -- unwind the function tree2treeH
= heightH (NodeH (1 + maximum $ map heightH [N1, N2, N3])                     -- unwind the function nodeH
= heightH (NodeH (1 + maximum $ [(heightH N1), (heightH N2), (heightH N3)])   -- apply map to each element in the list

Since (heightH (NodeH h t c)) = h
the above simplifies to

= (1 + maximum [(heightH N1), (heightH N2), (heightH N3)])
```

which is effectively the same as the implementation of height, which when unwound
becomes:

```
= (1 + maximum [(height N1), (height N2), (height N3)])
```


MkTreeH
-------

With the function `tree2treeH` we can very simply implement `mktreeH` as the composition of
`tree2treeH` with `mktree`.

> mktreeH :: State -> TreeH
> mktreeH = tree2treeH . mktree

It is also possible to implement mktreeH similarly to `mktree` replacing:

* Stop with StopH
* height with heightH
* Node constructor with the smart-constructor `nodeH`

Conceptually, `mktreeH'` below should perform better than `mktreeH` since the latter,
builds an entire Tree and then converts it to TreeH, whereas the former just builds
it once. Testing the performance difference however does not yield sufficiently
convincing improvements:

: set +s
: mktreeH  (Pair 8 0) --> (7.25 secs, 5,331,468,040 bytes)
: mktreeH' (Pair 8 0) --> (7.02 secs, 5,263,940,664 bytes)

: mktreeH  (Pair 9 0) --> (41.80 secs, 31,342,052,720 bytes)
: mktreeH'  (Pair 9 0) --> (41.24 secs, 30,946,184,648 bytes)

Additionally, as has been pointed out in the course, program performance is
not an evaluation criteria.

> mktreeH' s
>   | final s = StopH s
>   | otherwise = minHeightH $ map testToTree allTests
>     where
>       allTests = tests s
>       testToTree t = nodeH t (map mktreeH' $ outcomes s t)
>       minHeightH = minimumBy (\t1 t2 -> heightH t1 `compare` heightH t2)


6. A greedy solution
====================

TODO: check if this is meant to be an and or an or
NOTES:
- why is it ab?

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

