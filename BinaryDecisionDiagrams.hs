import Data.List
import Data.Tuple

type Index = Int

data BExp = Prim Bool
            | IdRef Index
            | Not BExp
            | And BExp BExp
            | Or BExp BExp deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode =  (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I

-- Pre: The item is in the given table
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp _ [] = error "Can't look up an empty tuple"
lookUp x ((y,ys):tail)
  | x == y = ys
  | otherwise  = lookUp x tail

checkSat :: BDD -> Env -> Bool
checkSat (x,xs) env = case x of
  0 -> False
  1 -> True
  x -> let (is,f,t) = lookUp x xs in
        if lookUp is env then checkSat (t,xs) env
        else checkSat (f,xs) env

-- Tail-recursive ;)
getSat :: Env -> BDD -> [Env] -> [Env]
getSat env (x,xs) acc = case x of
  0 -> acc
  1 -> env:acc
  x -> let (is,f,t) = lookUp x xs in
          getSat ((is,False):env) (f,xs)
            (getSat ((is,True):env) (t,xs) acc)

sat :: BDD -> [Env]
sat (x,xs) = getSat [] (x,xs) []
------------------------------------------------------
-- PART II

simplify :: BExp -> BExp
simplify expr = case expr of
  And (Prim x) (Prim y) -> Prim (x && y)
  And _ (Prim False) -> Prim False
  And (Prim False) _ -> Prim False
  And (Prim True) x -> x
  And x (Prim True) -> x
  Or (Prim x) (Prim y) -> Prim (x || y)
  Or (Prim True) _ -> Prim True
  Or _ (Prim True) -> Prim True
  Or (Prim False) x -> x
  Or x (Prim False) -> x
  Not (Prim x) -> Prim (not x)
  x -> x

-- Point 2
restrict :: BExp -> Index -> Bool -> BExp
restrict expr id b = case expr of
  Prim x -> Prim x
  IdRef x | x == id -> Prim b
  IdRef x -> IdRef x
  Not x -> simplify (Not (restrict x id b))
  And x y -> simplify (And (restrict x id b) (restrict y id b))
  Or x y -> simplify (Or (restrict x id b) (restrict y id b))

------------------------------------------------------
-- PART III
boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0

getNodes :: BExp -> [Index] -> NodeId -> [BDDNode]
getNodes expr [] id = []
getNodes expr (n:ns) id =
  let t = restrict expr n True
      f = restrict expr n False
  in case (f,t) of
    (Prim x, Prim y) -> [(id, (n, boolToInt x, boolToInt y))]
    _ -> [(id, (n, id*2, id*2+1))] ++ getNodes f ns (id*2) ++ getNodes t ns (id*2+1)

buildBDD :: BExp -> [Index] -> BDD
buildBDD expr index = case index of
  []    -> case expr of
        Prim x  -> (boolToInt x, [])
        _       -> error "Incorrect BExp"
  x:xs  -> (2, getNodes expr (x:xs) 2)


-----------------------------------------------------
-- PART IV

-- Pre: Each variable index in the BExp appears exactly once
--      in the Index list; there are no other elements
removeNode :: [BDDNode] -> (NodeId,NodeId) -> [BDDNode]
removeNode [] _ = []
removeNode (n@(id,(is,f,t)):tail) (x,y)
  | f == x = removeNode ((id,(is,y,t)):tail) (x,y)
  | t == x = removeNode ((id,(is,f,y)):tail) (x,y)
  | id == x = removeNode tail (x,y)
  | otherwise = n:removeNode tail (x,y)

uselessNodes :: [BDDNode] -> [(NodeId,NodeId)]
uselessNodes [] = []
uselessNodes ((id,(is,f,t)):tail)
  | f == t = (id, f):uselessNodes tail
  | otherwise = uselessNodes tail

opt :: [BDDNode] -> [(NodeId,NodeId)] -> [BDDNode]
opt nodes [] = nodes
opt nodes ids = foldl removeNode nodes ids

validDelete :: [BDDNode] -> (NodeId,NodeId) -> Bool
validDelete [] _ = False
validDelete ((id,(is,f,t)):tail) (x,y)
  | id == y = True
  | otherwise = validDelete tail (x,y)

groupAlike :: BDDNode -> [BDDNode] -> [(NodeId,NodeId)]
groupAlike (id,(is,f,t)) =
  map (swap . (,) id . fst) . filter (\(id1,(is1,f1,t1)) -> id /= id1 && f == f1 && t == t1)

opt2' :: [BDDNode] -> [(NodeId,NodeId)] -> [BDDNode]
opt2' nodes [] = nodes
opt2' nodes (x:xs)
  | validDelete nodes x = opt2' (removeNode nodes x) xs
  | otherwise = opt2' nodes xs

opt2 :: [BDDNode] -> [BDDNode]
opt2 nodes =
  let indeces = concatMap (`groupAlike` nodes) nodes
  in opt2' nodes indeces

optimize :: [BDDNode] -> Int -> [BDDNode]
optimize ns 0 = ns
optimize ns n =
  let o2 = opt2 ns
      o1 = opt o2 $ uselessNodes o2
  in optimize o1 (n - 1)

buildROBDD :: BExp -> [Index] -> BDD
buildROBDD expr index =
  let (root,nodes) = buildBDD expr index
  in (root, optimize nodes (length index))

lengthBDD :: BDD -> Int
lengthBDD (x,xs) = length xs

-- bestROBDD :: BExp -> [Index] -> [BDD]
bestROBDD expr index =
  let indeces = permutations index
  in  snd
      . head
      . sortOn fst
      $ map ((\x -> (length x,x)) . buildROBDD expr) indeces
------------------------------------------------------
-- Examples for testing...

b1, b2, b3, b4, b5, b6, b7, b8 :: BExp
b1 = Prim False
b2 = Not (And (IdRef 1) (Or (Prim False) (IdRef 2)))
b3 = And (IdRef 1) (Prim True)
b4 = And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3)))
b5 = Not (And (IdRef 7) (Or (IdRef 2) (Not (IdRef 3))))
b6 = Or (And (IdRef 1) (IdRef 2)) (And (IdRef 3) (IdRef 4))
b7 = Or (Not (IdRef 3)) (Or (IdRef 2) (Not (IdRef 9)))
b8 = Or (IdRef 1) (Not (IdRef 1))

bdd1, bdd2, bdd3, bdd4, bdd5, bdd6, bdd7, bdd8 :: BDD
bdd1 = (0,[])
bdd2 = (2,[(4,(2,1,1)),(5,(2,1,0)),(2,(1,4,5))])
bdd3 = (5,[(5,(1,0,1))])
bdd4 = (2,[(2,(2,4,5)),(4,(3,8,9)),(8,(7,0,1)),(9,(7,0,0)),
           (5,(3,10,11)),(10,(7,0,1)),(11,(7,0,1))])
bdd5 = (3,[(4,(3,8,9)),(3,(2,4,5)),(8,(7,1,0)),(9,(7,1,1)),
           (5,(3,10,11)),(10,(7,1,0)),(11,(7,1,0))])
bdd6 = (2,[(2,(1,4,5)),(4,(2,8,9)),(8,(3,16,17)),(16,(4,0,0)),(17,(4,0,1)),(9,(3,18,19)),(18,(4,0,0)),(19,(4,0,1)),(5,(2,10,11)),(10,(3,20,21)),(20,(4,0,0)),(21,(4,0,1)),(11,(3,22,23)),(22,(4,1,1)),(23,(4,1,1))])
bdd7 = (6,[(6,(2,4,5)),(4,(3,8,9)),(8,(9,1,1)),(9,(9,1,0)),(5,(3,10,11)),(10,(9,1,1)),(11,(9,1,1))])
bdd8 = (2,[(2,(1,1,1))])

