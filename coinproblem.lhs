> module CoinProblem where
> import Data.List (minimumBy, elemIndex)

2. States and tests
===================

> data State = Pair Int Int | Triple Int Int Int | Invalid
>   deriving (Eq, Show)

> data Test = TPair (Int, Int) (Int, Int)
>           | TTrip (Int, Int, Int) (Int, Int, Int)
>   deriving (Eq, Show)

Valid
-----

The function returns true only when its arguments match the pattern (Pair-TPair)
or (Triple-TTrip), and when all conditions below are true:

- `allPositive`     : all integers in Pair, Triple, TPair, TTrip are positive.
- `equalPans`       : same number of coins on the left and right pans of the scale.
- `sufficientCoins` : there must be a sufficient number of coins for each pile in the test as
                      there are in the state.
- `nonZero`         : we're not weighing zero with zero, since we learn nothing from that
                      Note that it is sufficient to check sum[a,b] == 0 without sum[c,d] == 0
                      because we have equalPans that enforces the latter (same for Triple case).

The `valid _ _ = False` at the bottom of the function matches any patterns that were not
(Pair-TPair) or (Triple-TTrip) and returns false for them.

> valid :: State -> Test -> Bool
> valid (Pair u g) (TPair (a,b) (c,d))
>     = allPositive && equalPans && sufficientCoins && nonZero
>   where
>     allPositive     = all (>=0) [u,g,a,b,c,d]
>     equalPans       = sum[a,b] == sum[c,d]
>     sufficientCoins = sum[a,c] <= u && sum[b,d] <= g
>     nonZero         = sum[a,b] /= 0
>
> valid (Triple l h g) (TTrip (a,b,c) (d,e,f))
>     = allPositive && equalPans && sufficientCoins && nonZero
>   where
>     allPositive     = all (>=0) [l,h,g,a,b,c,d,e,f]
>     equalPans       = sum[a,b,c] == sum[d,e,f]
>     sufficientCoins = sum[a,d] <= l && sum[b,e] <= h && sum[c,f] <= g
>     nonZero         = sum[a,b,c] /= 0
>
> valid _ _ = False


3. Choosing and conducting a test
================================

Working through the coin problem, it is evident that some states are impossible to
reach and confirmation of this can be found in the coversheet section discussing the
outcomes of state `Triple 3 0 6` with test `TTrip (0, 0, 3) (3, 0, 0)`
which are `[Triple 0 0 9,Triple 0 0 9,Triple 3 0 6]`.

First, let us discuss the intuition behind why two of those outcomes are invalid.

- The left outcome would be the result of the 3 genuine coins on the left weighing less
  than the 3 suspect-light coins on the right `(0,0,3) < (3,0,0)`.
  This outcome is impossible because in a TTrip test, an all genuine pan cannot weigh
  less than one with no suspect-heavy coins. An all genuine can only be on the lighter
  side of the scale when weighed against:
    (a) Unknown coins in a TPair test
    (b) Suspect-heavy coins in a TTrip test
- The middle outcome would be the result of the 3 genuine coins balancing with
  the 3 suspect-lights: `(0,0,3) == (3,0,0)`. It is not invalid for genuines to balance with
  suspect-lights (or heavies) but their balancing here implies all suspect-lights are
  genuine, which in turn implies all coins are genuine. This is impossible because
  we are in a Triple state and we know that the scale tipped to one side on one of our earlier
  tests so there is a counterfeit coin.

Any state `Triple 0 0 x` is an invalid state because it implies the absence of counterfeit
coins which violates the Triple state's existence. We create a smart-constructor for our
Triple states below.

MkTriple
--------

The function wraps around the Triple constructor checking the 'l' and 'h' parameters:
  - if both are zero it returns an Invalid value (see data declaration of State)
  - otherwise return a Triple state.
Hence, mkTriple (0 0 9) = Invalid.

Going forward, there should be no bare Triple constructors, instead
mkTriple is employed.

> mkTriple :: Int -> Int -> Int -> State
> mkTriple l h g
>   | l == 0 && h == 0 = Invalid
>   | otherwise = Triple l h g


Outcomes
--------

This function is arguably the most critical. First, we outline some rules/conditions
that must be maintained in both (Pair-TPair) and (Triple-TTrip) combinations.

(1) The outcome of an invalid state-test combination (according to our definition
    of valid above) is an empty list.
(2) Genuine coins used in a test always go back to the genuine pile in the outcome
    state. Hence, in a `TPair (a,b) (c,d)` both `b` and `d` return to the
    genuine pile of all outcome states, and the same for `c` and `f` in
    the TTrip (a,b,c) (d,e,f) test.
    Perhaps the above is evident but it helps to clearly outline it.
(3) The total number of coins is unchanged between a state and its outcomes.
    Again, obvious, but this will in sanity checking our implementation.

The signature of outcomes is:

> outcomes :: State -> Test -> [State]

For the Pair-TPair case:

> outcomes (Pair u g) (TPair (a,b) (c,d))
>   | valid (Pair u g) (TPair (a,b) (c,d)) = [
>       mkTriple  a       c   (g + u - us),
>       Pair      (u - us)    (g + us),
>       mkTriple  c       a   (g + u - us)
>     ]
>   | otherwise = []
>   where us = a + c

When the pans balance (middle outcome), we know that all coins currently on
the scale are genuine. The previously unknown `a` and `c` are now genuine.
Hence the remaining number of unknown coins is the original `u` minus `us=(a+c)`,
and the total number of genuine coins increases by us `g+us`.

When the scale tips to one side (left and right outcomes), the next state is
a Triple, hence the use of `mkTriple`. We know there's a counterfeit coin but
whether heavy or light is yet to be determined. We move all previously unknown
coins on the heavy side of the scale to the suspect-heavy pile `h` and
all previously unknown coins on the light side of the scale to the suspect-light
pile `l`. As per (2) all genuine coins return to the genuine pile.
Concretely, in the left outcome `(a,b) < (c,d)`, we move:

  - `a` to the light pile `l`
  - `c` to the heavy pile `h`
  - all unknown coins that did not take part in the test to the genuine
    pile leaving us with `Triple a c (g+u-us)`

The right outcome `(a,b) > (c,d)` is symmetric to the left one with `a` and `c`
swapping places: `Triple c a (g+u-us)`

**Sanity check**
The total number of coins in the left and right outcomes is:
`a + c + g + u - (a + c) = g + u` which matches the number in the original state.
Same for the middle outcome: `u - (a + c) + (g + (a + c)) = g + u`

The Triple-TTrip case is slightly trickier:

> outcomes (Triple l h g) (TTrip (a,b,c) (d,e,f))
>   | valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = [
>       mkTriple a        e         $ g + (l - a) + (h - e),
>       mkTriple (l - l') (h - h')  $ g + l' + h',
>       mkTriple d        b         $ g + (l - d) + (h - b)
>     ]
>   | otherwise = []
>   where
>     l' = a + d
>     h' = b + e

TODO: figure out how best to neaten this up

When the pans balance, all coins in the test go to the genuine pile. The `l` and
`h` piles shrink by `l' = a + d` and `h' = b + e` respectively, and the genuine
pile grows by the same amount. The known genuine coins `c` and `f` are not present in
this equation because following from (2) above they return to the genuine pile.
In summary:

  - Light pile: `l - (a + d)`
  - Heavy pile: `h - (b + e)`
  - Genuine pile: `g + (a + d + b + e)`

When the left pan is lighter than the right pan `(a,b,c) < (d,e,f)`

  - All suspect-lights in the left pan `a` end up in the light pile
  - All suspect-heavies in the right pan `e` end up in the heavy pile
  - All other coins end up in the genuine pile including all suspect-lights
    that did not take part in the test or that were on the heavy side of the scale
    `(l-a)`, and all suspect-heavies that were not in the test or that were
    on the light side of the scale `(h-e)`. The genuine pile becomes:
    `g = g + (l - a) + (h - e)`

The case where the left pan is heavier than the right one `(a,b,c) > (d,e,f)`
is vice versa of the above. In summary:

  - All suspect-lights in the right pan `d` end up in the light pile
  - All suspect-heavies in the left pan `b` end up in the heavy pile.
  - All other coins end up in the genuine pile: `g = g + (l - d) + (h - b)`


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
>     TPair (a, b) (a + b, 0)
>       | a <- [0..m],
>         b <- [0..g],
>         a + b /= 0,
>         2 * a + b <= u
>     ]
>   where m = u `div` 2

The Triple case is trickier and requires the subsidiary choices (defined
further below). We perform the Cartesian product of the set
`choices k (l,h,g)` with itself and then filter TTrip combinations that
do not satisfy the below conditions:

- c * f     = 0
- a + b + c == d+e+f
- b + e     <= h
- c + f     <= g
- a + d     <= l
- and the lexical ordering using `show (a,b,c) <= show (d,e,f)`

Note that the set `choices k (l, h, g)` is generated once only and stored
in 'ch', avoiding repeated computations and saving time.
TODO: perhaps mention that this saves xx% time.

> weighings (Triple l h g) = [
>     TTrip (a,b,c) (d,e,f)
>       | k <- [1..kr],
>         let ch = choices k (l, h, g),
>         (a,b,c) <- ch,
>         (d,e,f) <- ch,
>         c * f         == 0,
>         a + b + c     == d + e + f,
>         b + e         <= h,
>         c + f         <= g,
>         a + d         <= l,
>         show (a,b,c)  <= show (d,e,f)
>     ]
>     where kr = (l + h + g) `div` 2

> choices :: Int -> (Int, Int, Int) -> [(Int, Int, Int)]
> choices k (l, h, g) = [
>   (i, j, r)
>     | i <- [0..l],
>       j <- [0..h],
>       let r = k - i - j,
>       0 <= r && r <= g
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

We implement the function compare on our State data type to allow
the implementation to judge whether certain tests help to progress towards a solution.

- Triple provides more information than Pair thus
  (Triple `compare` Pair = LT and Pair `compare` Triple = GT)
- Invalid is a terminal state, it provides ample information hence it is
  always the less than the other operand (Invalid `compare` _ = LT)
  and (_ `compare` Invalid = GT)
- When comparing two instances of Pair, the one with more genuine coins provides
  more information and should be the lesser of the two. The result of comparing
  2 Pairs is the opposite of comparing their genuine coins,
  hence Pair u1 g1 `compare` Pair u2 g2 = g2 `compare` g1
- Same as above but for comparing a pair of Triples. The Triple with most genuines is
  closer to the solution, thus Triple _ _ g1 `compare` Triple _ _ g2 = compare g2 g1


Productive
----------

The function productive returns True when all outcomes from a Test on a State
move us closer to the solution. To implement this, we generate the list of
outcomes of the State-Test pair and check whether all state outcomes are
strictly less than the original state.

We use the higher-order function `all` from Prelude which takes in a function
(a->Bool) and a list, and applies the function on each element of the
list producing a boolean. If all returned booleans are true `all` returns True,
otherwise it returns False. The function applied to each outcome is
`(<s)` shorthand for `(\x -> x < s)`.

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

In this coin problem, we set out to identify the counterfeit coin (if it were present)
and determine whether it was lighter or heavier than the remaining genuine coins. Our
final states are:

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

As our `final` function ignores the number of genuine coins provided merely
checking the unknowns in a Pair state, and the lights and heavies in the
Triple state, it may return odd results when presented with invalid States, such as
`(Pair 0 0)` for which it will return `True`, `Triple (1 0 1)` for which it
will return `True` and any state with invalid number of genuine coins.
This is understood and expected.

Height
------

To return the height of the tree, we simply return 1 + the maximum height
of each of its child subtrees. So we,

1) apply the function height on each of the node's subtrees: map height children
2) return 1 + the maximum of height returned from the children:
`1 + maximum (map height children)`.

As with all recursive functions, we need a base case to terminate at,
this happens when we reach a Stop node whose height is zero.

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
> minHeight = minimumBy treeCmp
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


5. Caching heights
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
>   where h = 1 + maximum (map heightH children)

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

For a (Node t children), we apply the function `tree2treeH` on all of its children
(recursion) and the result is a list of TreeHs. At this point we just call our
smart-constructor passing the test `t` and the list of TreeHs. The smart-constructor
takes care of computing the height and returning a NodeH.
That's the point of 'smart-constructor' it does the dirty-work of this function.

TODO: convince yourself that heightH . tree2treeH = height

```
height (Stop s) = 0
(heightH . tree2treeH) $ Stop s = heightH (tree2treeH $ Stop s)
                                = heightH (StopH s)
                                = 0         -- matches the pattern in heightH)
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

With the function `tree2treeH` we can very simply implement `mktreeH` as
the composition of `tree2treeH` with `mktree`.

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
>   | otherwise = minHeightH $ map test2Tree allTests
>     where
>       allTests = tests s
>       test2Tree t = nodeH t (map mktreeH' $ outcomes s t)
>       minHeightH = minimumBy (\t1 t2 -> heightH t1 `compare` heightH t2)


6. A greedy solution
====================

Optimal copied from the coversheet.

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


BestTests
---------

> bestTests :: State -> [Test]
> bestTests s = filter (optimal s) $ weighings s

The function `bestTests` filters out all non-optimal weighings for the provided
state `s`. It generates the list `weighings s` (see right end of the function)
and applies the function `(optimal s)` on each element in the list keeping only
the optimal ones (those for which `optimal s w = True`).

Note that `optimal s` can have been written in lambda terms which would
be more readable for the non-seasoned readers:
`filter (\w -> optimal s w) $ weighings s`

but `optimal s` is prettier and we stick with it.

Since the exact implementation of `optimal` is not as well understood, it is
difficult to postulate its correctness; we can however compare its returned results
with those obtained from functions implemented in the higher up sections.

Evidently, if our earlier functions are wrong then our checks below mean nothing.

We would check whether all elements in `bestTests (Pair 8 0)` are actually the roots
of minimum trees generated by `mktree `or `mktreeH`. The obstacle to this is that
`mktree` will return one of the minimum height trees (more specifically the
first such min tree), but we would like the entire list of such trees.

We can create `mktrees`:

(TODO: maybe mktrees implementation can be improved below?)

> mktrees :: State -> [Tree]
> mktrees s
>   | final s = [Stop s]
>   | otherwise = filter (\t -> h == height t) allTrees
>     where
>       h = height $ minHeight allTrees
>       allTrees = map test2Tree (tests s)
>       test2Tree t = Node t $ map mktree $ outcomes s t

We also write a function that allows us to extract a test from a tree node.
Note that the function call will fail if it is provided a Stop node.

> getTest :: Tree -> Test
> getTest (Node t _) = t

> getTestH :: TreeH -> Test
> getTestH (NodeH _ t _) = t


We can then run:

s3 = Pair 8 0
map getTest (mktrees s3) == bestTests s3

which returns True.

Of course this does not prove the correctness of anything, but helps increase
confidence. A final note, if mktrees was somehow deemed useful and needed
to be kept in the implementation, we could reimplement mktree with mktree':

> mktree' = head . mktrees

--------------------------------------------------------

MkTreeG
--------

> mktreeG :: State -> TreeH
> mktreeG s
>   | final s = StopH s
>   | otherwise = nodeH bestTest trees
>     where
>       bestTest = head $ bestTests s
>       trees = map mktreeG $ outcomes s bestTest

The structure of our function `mktreeG` is not too dissimilar to that of `mktree`.

For a given list of tests, generate the outcomes and create tree nodes from
those outcomes. The difference here is that `bestTest` returns optimal tests
(ones that are guaranteed to lead to short trees) whereas in `mktree` we had
to generate all trees, compute their heights and pick the shortest.
Since `bestTests` returns a list of optimal tests, we can pick whichever and
create a decision tree from it (we pick the first using `head`).

To quickly go through the function again:

1) If the state is final, generate a leaf: StopH
2) otherwise, create a nodeH using our smart-constructor.
   The smart constructor takes in
   a) a test which is `bestTest`: the first optimal test we find
   b) a list of child nodes, which are all roots to decision trees representing
      the outcome states that resulted from `outcomes s bestTest`
      These child decision trees are created recursively (`mktreeG`) call
      on each outcome state.

MktreesG
--------

> mktreesG :: State -> [TreeH]
> mktreesG s = map test2Tree $ bestTests s
>   where test2Tree t = nodeH t (map mktreeG $ outcomes s t)

The above `mktreesG`, creates a tree for each optimal test coming out of
`bestTests s`: it is clear since `mktreesG` merely applies test2Tree to each
element in `bestTests s`. The function `test2Tree` creates a node from the
provided test `t`: to create a tree we pass the test to the smart-constructor
nodeH, then create a tree from each outcome of that test on the state `s`.

(Recall that Data.List.nub removes duplicates from a list. Hence, all those
trees have height 3.) How many minimum-height decision trees are there for n = 12?

One only:
CoinProblem> length $ mktreesG (Pair 12 0)
1

CoinProblem> mktreesG (Pair 12 0)
[NodeH 3 (TPair (4,0) (4,0)) [
  NodeH 2 (TTrip (0,2,1) (1,2,0))
    [
    NodeH 1 (TTrip (0,0,1) (0,1,0)) [StopH (Triple 0 1 11),StopH (Triple 0 1 11),StopH Invalid],
    NodeH 1 (TTrip (1,0,0) (1,0,0)) [StopH (Triple 1 0 11),StopH (Triple 1 0 11),StopH (Triple 1 0 11)],
    NodeH 1 (TTrip (0,1,0) (0,1,0)) [StopH (Triple 0 1 11),StopH (Triple 1 0 11),StopH (Triple 0 1 11)]
    ],
  NodeH 2 (TPair (0,3) (3,0))
    [
    NodeH 1 (TTrip (0,1,0) (0,1,0)) [StopH (Triple 0 1 11),StopH (Triple 0 1 11),StopH (Triple 0 1 11)],
    NodeH 1 (TPair (0,1) (1,0)) [StopH (Triple 0 1 11),StopH (Pair 0 12),StopH (Triple 1 0 11)],
    NodeH 1 (TTrip (1,0,0) (1,0,0)) [StopH (Triple 1 0 11),StopH (Triple 1 0 11),StopH (Triple 1 0 11)]
    ],
  NodeH 2 (TTrip (0,2,1) (1,2,0))
    [
    NodeH 1 (TTrip (0,0,1) (0,1,0)) [StopH (Triple 0 1 11),StopH (Triple 0 1 11),StopH Invalid],
    NodeH 1 (TTrip (1,0,0) (1,0,0)) [StopH (Triple 1 0 11),StopH (Triple 1 0 11),StopH (Triple 1 0 11)],
    NodeH 1 (TTrip (0,1,0) (0,1,0)) [StopH (Triple 0 1 11),StopH (Triple 1 0 11),StopH (Triple 0 1 11)]
    ]
  ]
]


CoinProblem> map getTestH $ mktreesG (Pair 8 0)
[TPair (2,0) (2,0),TPair (3,0) (3,0),TPair (4,0) (4,0)]

CoinProblem> map getTestH $ mktreesG (Pair 12 0)
[TPair (4,0) (4,0)]

CoinProblem> (map getTest $ mktrees (Pair 8 0 )) == (map getTestH $ mktreesG (Pair 8 0))
True


* TODO: consistent plus/minuses in the writeup
* TODO: be consistent with usage of pan and bucket