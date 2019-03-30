import CoinProblem

pair = (Pair 8 0)
triple = (Triple 3 3 9)
tpair = TPair (3,0)(3,0)
ttrip = TTrip (3,0,0) (0,0,3)

validTest1 = (valid Invalid ttrip) == False
validTest2 = (valid Invalid tpair) == False
validTest3 = (valid pair ttrip) == False
validTest4 = (valid triple tpair) == False
validTest5 = (valid pair tpair) == True
validTest6 = (valid triple ttrip) == True

validTests = all (==True) [ validTest1, validTest2, validTest3, validTest4, validTest5 ]