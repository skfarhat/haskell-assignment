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

The function returns true only when its arguments match the pattern Pair-TPair
or Triple-TTrip and when all below conditions are true:

- `allPositive`: all integers in Pair, Triple, TPair, TTrip are positive
- `equalPans`  : same number of coins on the left and right pans of the scale
- `enoughCoins`: no pile will have more coins in the test than there are in the state
- `nonZero`    : we're not weighing zero with zero, since we learn nothing
                 from that. Note that it is sufficient to check
                 `sum[a,b] == 0` without `sum[c,d] == 0` because we have
                 `equalPans` which enforces the latter (same for Triple
                 case)

The `valid _ _ = False` at the bottom of the function matches any patterns
that were not (Pair-TPair) or (Triple-TTrip) and returns false for them.

> valid :: State -> Test -> Bool
> valid (Pair u g) (TPair (a,b) (c,d))
>     = allPositive && equalPans && enoughCoins && nonZero
>   where
>     allPositive     = all (>=0) [u,g,a,b,c,d]
>     equalPans       = sum[a,b] == sum[c,d]
>     enoughCoins = sum[a,c] <= u && sum[b,d] <= g
>     nonZero         = sum[a,b] /= 0
>
> valid (Triple l h g) (TTrip (a,b,c) (d,e,f))
>     = allPositive && equalPans && enoughCoins && nonZero
>   where
>     allPositive     = all (>=0) [l,h,g,a,b,c,d,e,f]
>     equalPans       = sum[a,b,c] == sum[d,e,f]
>     enoughCoins = sum[a,d] <= l && sum[b,e] <= h && sum[c,f] <= g
>     nonZero         = sum[a,b,c] /= 0
>
> valid _ _ = False


3. Choosing and conducting a test
=================================

Working through the coin problem, it is evident that some states are
impossible to reach and confirmation of this can be found in the coversheet
section discussing the outcomes of state `Triple 3 0 6` with test
`TTrip (0,0,3) (3,0,0)` which are `[Triple 0 0 9,Triple 0 0 9,Triple 3 0 6]`.

First, let us discuss the intuition behind why two of those outcomes are
invalid.

- The left outcome would be the result of the 3 genuine coins on the left
  weighing less than the 3 suspect-light coins on the right
  `(0,0,3) < (3,0,0)`. This outcome is impossible because in a TTrip test,
  an all genuine pan cannot weigh less than one with no suspect-heavy coins.
  An all genuine can only be on the lighter side of the scale when weighed
  against:
    (a) Unknown coins in a TPair test
    (b) Suspect-heavy coins in a TTrip test
- The middle outcome would be the result of the 3 genuine coins balancing
  with the 3 suspect-lights: `(0,0,3) == (3,0,0)`. It is not invalid for
  genuines to balance with suspect-lights (or heavies) but their balancing
  here implies all suspect-lights are genuine, which in turn implies all
  coins are genuine.
  This is impossible because we are in a Triple state and we know that the
  scale tipped to one side on one of our earlier tests so there is a
  counterfeit coin.

Any state `Triple 0 0 x` is an invalid state because it implies the absence
of counterfeit coins which violates the Triple state's existence. We create
a smart-constructor for our Triple states below.

MkTriple
--------

The function wraps around the Triple constructor returning an Invalid if
both `l` and `h` parameters are zero, otherwise a Triple value is returned.
As such, `mkTriple (0 0 9) = Invalid`.

Going forward, there should be no bare Triple constructors, instead
mkTriple is employed.

> mkTriple :: Int -> Int -> Int -> State
> mkTriple l h g
>   | l == 0 && h == 0 = Invalid
>   | otherwise = Triple l h g


Outcomes
--------

This function is arguably the most critical. First, we outline some
rules/conditions that must be maintained in both (Pair-TPair) and
(Triple-TTrip) combinations.

(1) The outcome of an invalid state-test combination (according to our
    definition of valid above) is an empty list.
(2) Genuine coins used in a test always go back to the genuine pile in the
    outcome state. Hence, in a `TPair (a,b) (c,d)` both `b` and `d` return
    to the genuine pile of all outcome states, and the same for `c` and `f`
    in the TTrip (a,b,c) (d,e,f) test. Perhaps the above is evident but
    it helps to clearly outline it.
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

When the pans balance (middle outcome), we know that all coins currently
on the scale are genuine. The previously unknown `a` and `c` are now
genuine. Hence the remaining number of unknown coins is the original
`u` minus `us = a + c`, and the total number of genuine coins increases
by us `g + us`.

When the scale tips to one side (left and right outcomes), the next state
is a Triple, hence the use of `mkTriple`. We know there's a counterfeit
coin  but whether heavy or light is yet to be determined. We move all
previously  unknown coins on the heavy side of the scale to the
suspect-heavy pile `h`  and all previously unknown coins on the light side
of the scale to the suspect-light pile `l`. As per (2) all genuine coins
return to the genuine pile. Concretely, in the left outcome `(a,b) < (c,d)`,
we move:

  - `a` to the light pile `l`
  - `c` to the heavy pile `h`
  - all unknown coins that did not take part in the test to the genuine
    pile leaving us with `Triple a c (g + u - us)`

The right outcome `(a,b) > (c,d)` is symmetric to the left one with `a`
and `c` swapping places: `Triple c a (g + u - us)`

**Sanity check**

The total number of coins in the left and right outcomes is:
`a + c + g + u - (a + c) = g + u` which matches the number in the original
state. Same for the middle outcome: `u - (a + c) + (g + (a + c)) = g + u`

The Triple-TTrip case is slightly trickier:

> outcomes (Triple l h g) (TTrip (a,b,c) (d,e,f))
>   | valid (Triple l h g) (TTrip (a,b,c) (d,e,f)) = [
>       mkTriple   (a)      (e)     $ g + (l - a) + (h - e),
>       mkTriple (l - l') (h - h')  $ g + l' + h'          ,
>       mkTriple   (d)      (b)     $ g + (l - d) + (h - b)
>     ]
>   | otherwise = []
>   where
>     l' = a + d
>     h' = b + e

When the pans balance, all coins in the test go to the genuine pile.
The `l` and `h` piles shrink by `l' = a + d` and `h' = b + e` respectively,
and the genuine pile grows by the same amount. The known genuine coins `c`
and `f` are not present in this equation because following from (2) above
they return to the genuine pile. In summary:

  - Light pile: `l - (a + d)`
  - Heavy pile: `h - (b + e)`
  - Genuine pile: `g + (a + d + b + e)`

When the left pan is lighter than the right pan `(a,b,c) < (d,e,f)`

  - All suspect-lights in the left pan `a` end up in the light pile
  - All suspect-heavies in the right pan `e` end up in the heavy pile
  - All other coins end up in the genuine pile including all suspect-lights
    that did not take part in the test or that were on the heavy side of
    the scale `(l-a)`, and all suspect-heavies that were not in the test
    or that were on the light side of the scale `(h-e)`. The genuine pile
    becomes: `g = g + (l - a) + (h - e)`

The case where the left pan is heavier than the right one
`(a,b,c) > (d,e,f)` is vice versa of the above. In summary:

  - All suspect-lights in the right pan `d` end up in the light pile
  - All suspect-heavies in the left pan `b` end up in the heavy pile.
  - All other coins end up in the genuine pile: `g = g + (l - d) + (h - b)`


Weighings
---------

> weighings :: State -> [Test]

__Pair Case__

> weighings (Pair u g) = [
>     TPair (a, b) (a + b, 0)
>       | a <- [0..m],
>         b <- [0..g],
>         a + b /= 0,
>         2 * a + b <= u
>     ]
>   where m = u `div` 2

We have the following constraints:

1) Both pans must have the same number of coins: `a + b = c + d`
2) One of the pans must not have genuine coins: `b * d = 0`
3) Only the lexically smaller of symmetrical weighings is returned
   e.g. return the former of `TPair (0,1) (1,0)` and `TPair (1,0) (0,1)`

__The conditions are only satisfied if `d == 0`. Why?__

It can be proven through contradiction, let us assume `d /= 0`.
From (2), we have `b = 0` and (1) becomes `a = c + d` implying `a > c`
because `d > 0` (remember d cannot be negative), but this contradicts (3)
therefore d is not non-zero, `d` is zero.
Consequently, `a + b = c` and `TPair (a,b) (c,d)` simplifies to
`TPair (a,b) (a + b,0)`. The implementation boils down to a list
comprehension that filters out candidates violating any of the below
conditions:

- `a + b /= 0`
- `2a + b <= u`
- `b <= g`

For the range of `a`, we can show that it its upper bound
is `m= u div 2` by contradiction. Assume `a = m + 1`.

When u is even, `u div 2 = u / 2`:
```
  a  = m + 1
  a  = u / 2 + 1
  2a = u + 2
  2a > u        (impossible)
```

When u is odd, `u div 2 = (u-1)/2`:
```
  m     = (u - 1) / 2
  m + 1 = (u - 1) / 2 + 1
  a     = (u + 1) / 2
  2a    = u + 1
  2a    > u        (impossible)
```

__Triple Case__

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

This case is trickier and requires the subsidiary `choices` defined
further below. (ghci does not allow us to intersperse `weighings` and
`choices` definitions). We perform the Cartesian product of the set
`choices k (l,h,g)` with itself filtering out TTrip combinations that
do not satisfy the below conditions:

- `c * f        = 0`
- `a + b + c    == d + e + f`
- `b + e        <= h`
- `c + f        <= g`
- `a + d        <= l`
- `show (a,b,c) <= show (d,e,f)`

Note that the set `choices k (l, h, g)` is generated once only and stored
in 'ch' to avoid redundant calls.

Choices
-------

The function returns all possible combinations of `l, h, g` given a number
of coins `k`.

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
>   compare (Triple _ _ _ ) (Pair _ _)        = LT
>   compare (Pair _ _     ) (Triple _ _ _)    = GT
>   compare (Pair _ g1    ) (Pair _ g2)       = compare g2 g1
>   compare (Triple _ _ g1) (Triple _ _ g2)   = compare g2 g1

The `compare` function is overridden for our State datatype to allow for
judging the proximity of a state to the final solution.

- Triple provides more information than Pair hence
  `Triple compare Pair = LT` and `Pair compare Triple = GT`
- Invalid is a terminal state hence it is considered less than
   all other states `Invalid compare _ = LT` and `_ compare Invalid = GT`.
- The result of comparing 2 instances of Pair is equal to the opposite
  of comparing their genuine coins: the instances with **more** genuine
  coins is considered **less** than the other:
  `(Pair u1 g1) compare (Pair u2 g2) = g2 compare g1`.
- The Triple case is similar to the Pair case in this regard, the Triple
  with more genuine coins is the lesser of the two instances:
  `Triple _ _ g1 compare Triple _ _ g2 = compare g2 g1`


Productive
----------

> productive :: State -> Test -> Bool
> productive s t = all (<s) $ outcomes s t

The function returns true when all outcomes of test on a state move us
closer to the final solution. We generate the list of outcomes of the
state-test combination and check whether all resulting state outcomes
are strictly less than the original state (closer to the final solution).

We use the higher-order function `all` from Prelude which accepts a
function (a->Bool)  and a list, and applies the function on every element
of the list.  If all returned booleans are true `all` returns True,
otherwise it returns False. The function applied to each outcome is
`(<s)` shorthand for `(\x -> x < s)`.


Tests
-----

> tests :: State -> [Test]
> tests s = filter (productive s) $ weighings s

The function returns a list of all productive weighings for a State s.
It is straightforward to implement given `productive` and `weighings`
above; we simply generate all weighings for the state s then filter out
all those deemed unproductive using the function `productive`.

Function currying allows us to simplify
`filter (\w -> productive s w) $ weighings s` to the above.


4. Decision trees
=================


> data Tree = Stop State | Node Test [Tree]
> 		deriving Show


Final
-----

> final :: State -> Bool
> final Invalid         = True
> final (Pair u _)      = u == 0
> final (Triple l h _)  = foundSingleFake || allGenuine
>   where
>     foundSingleFake   = (l + h == 1) && (l * h == 0)
>     allGenuine        = l == 0 && h == 0

Final states are ones where no more progress can be done. They are:

* `Pair 0 x`: no counterfeit was found, u=0
* `Triple 1 0 x`: we found a single light counterfeit coin `l=1,h=0`
* `Triple 0 1 x`: we found a single heavy counterfeit coin `l=0,h=1`
* Invalid: invalid state, no where to go from here

_Note on behaviour:_ our `final` function ignores the number of genuine
coins `g` and only checks lights, heavies and unknowns. It is therefore
expected that outright wrong states such as `(Pair 0 0)`
and `Triple (1 0 1)` return true even when they are wrong.

Height
------

> height :: Tree -> Int
> height (Stop _) = 0
> height (Node _ children) = 1 + maximum (map height children)

Trees are recursive data-structures in nature, hence it is unsurprising
that most functions that operate on them are also recursive.

To calculate the height of a Node, we add one to the maximum height from
the heights of child nodes. To compute the heights of child nodes we
apply height on each using the standard `map` function. As with all
recursive functions, we define the base case to be height zero for
leaf nodes: `Stop`.


MinHeight
---------

> minHeight :: [Tree] -> Tree
> minHeight = minimumBy treeCmp
>     where treeCmp t1 t2 = height t1 `compare` height t2

Given a list of trees, the function `minHeight` returns the tree with
the shortest height. The function is easily implemented using `minimumBy`
(imported from `Data.List`) which accepts a comparator function telling it
how to compare two Tree objects. We define our tree comparison function
in the _where_ clause. Comparing two trees is essentially comparing their
heights hence the implementation.


MkTree
------

> mktree :: State -> Tree
> mktree s
>     | final s = Stop s
>     | otherwise = minHeight $ map test2Tree testList
>       where
>         testList = tests s
>         test2Tree t = Node t $ map mktree $ outcomes s t

We describe our implementation of the function `mkTree` by addressing each
sentence from the coversheet question separately.

__"Stop if s is final"__

The base case for our recursive function, handled on the first line of
the guard statement:`final s = Stop s`

__"Otherwise generate all possible productive tests with tests s"__

`testList = tests s`

__"Recursively build trees from the outcomes of each such test"__

We create a function test2Tree which, given a test `t` and the state `s`
(through the scope) constructs and returns a node with arguments:

1) the test `t`
2) a list of trees, each built from one of the outcomes of the test `t`
on state `s`. The building of those sub-trees is accomplished by applying
`mktree` on each outcome: `map mktree $ outcomes s t`.
Hence, `test2Tree = Node t $ map mktree $ outcomes s t`

__"Pick the one that yields the best tree overall"__

This where all components are combined. We extract the
minimum-height from the list resulting from `test2Tree` being applied
to each test in `testList`.


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
> treeH2tree (NodeH _ t ts) = Node t $ map treeH2tree ts

We handle each TreeH instance separately. A `StopH` node is straightforwardly
converted to a `Stop` node; they have the same arguments, so not much to
be said here. The height value in `NodeH` is dropped from
the `Node` (see `_` on third line). We construct a `Node` passing to
it the test `t` from `NodeH` then by  by recrusively converting each
of its children `ts` to a Tree using `map`:
`treeH2tree (NodeH h t ts) = Node t $ map treeH2tree ts`

TODO: check whether it is node-type/instance?


NodeH
------

> nodeH :: Test -> [TreeH] -> TreeH
> nodeH t ts = NodeH h t ts
>   where h = 1 + maximum (map heightH ts)

The smart-constructor `nodeH` allows us to create a `NodeH` by passing
the test `t` and its child nodes `ts` without worrying about computing
the height of the node ourselves. As such, the smart-constructor will
compute the height once upon creation. The height of a node is one plus
the maximum height of it children `ts` `h = 1 + maximum $ map heightH ts`.


Tree2treeH
----------

> tree2treeH :: Tree -> TreeH
> tree2treeH (Stop s) = StopH s
> tree2treeH (Node t ts) = nodeH t $ map tree2treeH ts

Again we use pattern matching to detect the node type here.

For a (Stop s) node, we return the equivalent StopH node with the same
state.

For a (Node t ts), we apply the function `tree2treeH` on all of its
children (recursion) and the result is a list of TreeHs. At this point
we just call our smart-constructor passing the test `t` and the list of
TreeHs. The smart-constructor takes care of computing the height and
returning a NodeH. The smart constructor is most useful here as it
simplifies the implementation of `tree2treeH`.


__"Convince yourself that heightH . tree2treeH = height"__


For (Stop s):

```haskell

height (Stop s) = 0

```

and

```haskell

(heightH . tree2treeH) $ Stop s
  -- apply tree2treeH to (Stop s)
  = heightH (tree2treeH $ Stop s)
  -- matches pattern in tree2treeH
  = heightH (StopH s)
  -- matches pattern in heightH
  = 0
```

For (Node t ts):

```haskell

(heightH . tree2treeH) $ Node t ts
-- tree2treeH applied on (Node t ts)
= heightH (tree2treeH $ Node t [n1, n2, n3])

-- unwind the function tree2treeH
= heightH (nodeH t $ map tree2treeH [n1, n2, n3])

-- unwind the function nodeH
= heightH (NodeH (1 + maximum $ map heightH [n1, n2, n3])

-- apply map to each element in the list
= heightH (NodeH (1 + maximum $ [(heightH n1), (heightH n2), (heightH n3)])

-- since (heightH (NodeH h t c)) = h, the above simplifies to
= (1 + maximum [(heightH n1), (heightH n2), (heightH n3)])

```

which is effectively the same as the implementation of height, which
when unwound becomes:

```
= (1 + maximum [(height N1), (height N2), (height N3)])
```


MkTreeH
-------

> mktreeH :: State -> TreeH
> mktreeH = tree2treeH . mktree

The function is merely the composition of `tree2treeH` with `mktree`.
The latter is first applied returning a `Tree`, and the former converts
that `Tree` to a `TreeH`.

We can also implement mktreeH from the ground up as we did `mktree`
replacing:

- Stop with StopH
- height with heightH
- Node constructor with the smart-constructor `nodeH`

> mktreeH' s
>   | final s = StopH s
>   | otherwise = minHeightH $ map test2Tree allTests
>     where
>       allTests = tests s
>       test2Tree t = nodeH t (map mktreeH' $ outcomes s t)
>       minHeightH = minimumBy (\t1 t2 -> heightH t1 `compare` heightH t2)

We expect `mktreeH'` to generate the tree quicker than `mktreeH` since
the latter builds an entire Tree before fully converting it to a
`TreeH`, whereas the former builds it on its first pass once.
However, performance testing does not show significant improvements
of `mktreeH'` over `mktreeH`:

```haskell

: set +s
: mktreeH  (Pair 8 0) --> (7.25 secs, 5,331,468,040 bytes)
: mktreeH' (Pair 8 0) --> (7.02 secs, 5,263,940,664 bytes)

: mktreeH  (Pair 9 0) --> (41.80 secs, 31,342,052,720 bytes)
: mktreeH'  (Pair 9 0) --> (41.24 secs, 30,946,184,648 bytes)

```


6. A greedy solution
====================

Optimal copied from the coversheet:

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

We generate the best tests for state s by filtering out all non-optimal
weighings of `s` using the `filter` function. The curried function
`optimal s` is applied to each weighing and when the result is true,
the weighing is kept and returned in the final list.


Mktrees
-------

As the implementation of `optimal` is not well understood, it is
difficult to prove or test for the correctness of `bestTests`. We can,
however, compare its results to those returned by our other `mktree`
functions defined in previous sections assuming, of course, they are
correct. The impediment to this is that our `mktree` functions return
one of many optimal trees, instead of the full list of optimal trees.

Hence we define `mktrees` below, inspired by `mktree`. The function
computes the full list of trees, determines the minimum-height tree and
then filters the list for all trees matching that minimum height `h`.

> mktrees :: State -> [Tree]
> mktrees s
>   | final s = [Stop s]
>   | otherwise = filter (\t -> h == height t) allTrees
>     where
>       h = height $ minHeight allTrees
>       allTrees = map test2Tree (tests s)
>       test2Tree t = Node t $ map mktree $ outcomes s t

(TODO: maybe mktrees implementation can be improved below?)

We also write a getter function to extract a test from a Tree node.
Note that the function call will fail if it is provided a Stop node.

> getTest :: Tree -> Test
> getTest (Node t _) = t

> getTestH :: TreeH -> Test
> getTestH (NodeH _ t _) = t


We then run the below equality check which _suggests_ `bestTests` does
return optimal trees.

```haskell

st = Pair 8 0
map getTest (mktrees st) == bestTests st

```

With `mktrees` defined, it is possible to simplify the definition of
`mktree`:

> mktree' = head . mktrees


MkTreeG
--------

> mktreeG :: State -> TreeH
> mktreeG s
>   | final s = StopH s
>   | otherwise = nodeH bestTest trees
>     where
>       bestTest = head $ bestTests s
>       trees = map mktreeG $ outcomes s bestTest

The structure of our function `mktreeG` is not too dissimilar to that of
`mktree`.

For a given list of tests, generate the outcomes and create tree nodes
from those outcomes. The difference here is that `bestTest` returns
optimal tests from the outset (ones that are guaranteed to lead to the
shortest trees) whereas `mktree` computed the trees for all productive
tests before picking the shortest. Since `bestTests` returns a list of
optimal tests, we pick any element in the list e.g. `head`.

In summary the function is structured as follows:

1) If the state is final, generate and return a leaf `StopH`
2) Otherwise, create a nodeH using our smart-constructor accepting:
  a) The first optimal test returned from `bestTests`: `bestTest`
  b) A list of trees constructed by applying `mktreeG` on the state
     outcomes resulting from `bestTest` applied on the state `s`.

MktreesG
--------

> mktreesG :: State -> [TreeH]
> mktreesG s = map test2Tree $ bestTests s
>   where test2Tree t = nodeH t (map mktreeG $ outcomes s t)

Contrasted with `mktreeG`, this function returns the full list of optimal
trees without cherry-picking the first optimal test in `bestTests`. It
creates a `TreeH` using `mktreeG` from every outcome of every optimal
test on the state `s`.

__"How many minimum-height decision trees are there for n = 12?"__


```haskell

One only:
CoinProblem> length $ mktreesG (Pair 12 0)
1

```

```haskell

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

```

* TODO: consider being harsher on the 80 chars rule (maybe there's an online tool?)