import CoinProblem

-- ==============================================================================
pair = (Pair 8 0)
triple = (Triple 3 3 9)
tpair = TPair (3,0)(3,0)
ttrip = TTrip (3,0,0) (0,0,3)

-- ==============================================================================
-- Test: valid

validTest1 = (valid Invalid ttrip) == False
validTest2 = (valid Invalid tpair) == False
validTest3 = (valid pair ttrip) == False
validTest4 = (valid triple tpair) == False
validTest5 = (valid pair tpair) == True
validTest6 = (valid triple ttrip) == True
validTest7 = (valid (Pair 8 0) (TPair (0,0) (0,0))) == False -- Check that false is returned when the test has no coins
validTest8 = (valid (Triple 3 3 6) (TTrip (0,0,0) (0,0,0))) == False -- Check that false is returned when the test has no coins

validTests = all (==True) [ validTest1, validTest2, validTest3, validTest4, validTest5, validTest6, validTest7, validTest8 ]

-- ==============================================================================
-- Test: outcomes



-- ==============================================================================

-- Below is a test of the tree presented in the assignment.

mrr = Node (TTrip (1,0,0) (1,0,0)) [Stop (Triple 1 0 7), Stop (Triple 0 1 7), Stop (Triple 1 0 7)]
rr = Node (TTrip (0,0,1) (0,1,0)) [Stop (Triple 0 1 7), mrr, Stop (Triple 0 0 0)]
rmr = Node (TTrip (1,0,0) (1,0,0)) (replicate 3 (Stop (Triple 1 0 7)))
mmr = Node (TPair (0,1) (1,0)) [Stop (Triple 0 1 7), Stop (Pair 0 8), Stop (Triple 1 0 7)]
lmr = Node (TTrip (0,1,0) (0,1,0)) (replicate 3 (Stop (Triple 0 1 7)))
mr = Node (TPair (3,0) (3,0)) [lmr, mmr, rmr]
mlr = Node (TTrip (1,0,0) (1,0,0)) [Stop (Triple 1 0 7), Stop (Triple 0 1 7), Stop (Triple 1 0 7)]
lr = Node (TTrip (0,0,1) (0,1,0)) [ Stop (Triple 0 1 7) , mlr, Stop (Triple 0 0 0) ] -- the Triple 0 0 0 means invalid case
root = Node (TPair (2,0) (2,0)) [ lr, mr ]
testHeight = height root

-- ==============================================================================

s4 = (Triple 2 2 4)
w4 = head $ bestTests s4
r4 = outcomes s4 w4

choicesTest = choices 3 (2, 2, 2) == [(0,1,2),(0,2,1),(1,0,2),(1,1,1),(1,2,0),(2,0,1),(2,1,0)]
weighingsTest1 = 5 == (length $ weighings (Triple 3 0 6))
productiveTest = productive (Triple 3 0 6) (TTrip (0, 0, 3) (3, 0, 0)) == False
outcomesTest1 = outcomes (Triple 3 0 6) (TTrip (0, 0, 3) (3, 0, 0)) `elem` [[Triple 0 0 9,Triple 0 0 9,Triple 3 0 6], [Invalid,Invalid,Triple 3 0 6]]
outcomesTest2 = outcomes (Pair 12 0) (TPair (3,0) (3,0)) == [Triple 3 3 6,Pair 6 6,Triple 3 3 6]
testsTest1 = 4 == (length $ tests(Triple 3 0 6))

-- ==============================================================================

testResultStr :: [Char] -> Bool -> [Char]
testResultStr s b = (if b then  "✅ " ++ s ++ " passed." else "🚫 " ++ s  ++ " failed.") ++ "\n"

runTests :: IO()
runTests = do
  putStr (testResultStr "choicesTest    " choicesTest)
  putStr (testResultStr "weighingsTest1 " weighingsTest1)
  putStr (testResultStr "outcomesTest1  " outcomesTest1)
  putStr (testResultStr "outcomesTest2  " outcomesTest2)
  putStr (testResultStr "productiveTest " productiveTest)
  putStr (testResultStr "testsTest1     " testsTest1)

-- ==============================================================================



-- Found this lying around, not sure if useful, check later.

s1 = Pair 12 0
tt = tests s1
newTrees t = map mktree $ outcomes s1 t
f1 t = Node t $ newTrees t

minHeightOrMe :: Tree -> [Tree] -> Tree
minHeightOrMe t [] = t
minHeightOrMe _ s = minHeight s

-- Used for debugging

traceIt s = trace ("->" ++ show s)
traceIt1 s = trace ("--> " ++ show s ++ "\n=================\n")

mktreeDebug :: State -> Tree
mktreeDebug s
    | final s || (length allTests == 0) = Stop s
    | otherwise = traceIt s $ minHeight $ map testToTree allTests
      where
        allTests = tests s
        testToTree t = Node t $ map mktreeDebug $ outcomes s t
