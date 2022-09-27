import Data.List
import Data.Tuple
import Distribution.Simple.Utils (xargs)

type Index = Int

data BExp
  = Prim Bool
  | IdRef Index
  | Not BExp
  | And BExp BExp
  | Or BExp BExp
  deriving (Eq, Ord, Show)

type Env = [(Index, Bool)]

type NodeId = Int

type BDDNode = (NodeId, (Index, NodeId, NodeId))

type BDD = (NodeId, [BDDNode])

------------------------------------------------------
-- PART I
-- Regulat recursive find
lookUp :: Eq a => a -> [(a, b)] -> b
lookUp _ [] = error "Not Found"
lookUp x ((y, ys) : tail)
  | x == y = ys
  | otherwise = lookUp x tail

-- Filter the list, pull out the snd values and return the first one
lookUp' :: Eq a => a -> [(a, b)] -> b
lookUp' x xs
  | null ls = error "Not found"
  | otherwise = head ls
  where
    ls = map snd $ filter ((==) x . fst) xs

-- Recursively traverse the tree and check
checkSat :: BDD -> Env -> Bool
checkSat (x, xs) env
  | x == 0 = False
  | x == 1 = True
  | lookUp is env = checkSat (t, xs) env
  | otherwise = checkSat (f, xs) env
  where
    (is, f, t) = lookUp x xs

-- Helper function, basically keep tracl of your path, if it works out append it to the answer.
getSat :: Env -> BDD -> [Env]
getSat env (x, xs)
  | x == 0 = []
  | x == 1 = [env]
  | otherwise =
    getSat ((is, False) : env) (f, xs)
      ++ getSat ((is, True) : env) (t, xs)
  where
    (is, f, t) = lookUp x xs

sat :: BDD -> [Env]
sat (x, xs) = getSat [] (x, xs)

-- A more challenging, but more fun solution. Make up all possible Environments
allEnvs :: Int -> [Env]
allEnvs k =
  map (zip [1 ..]) $
    nub $
      filter ((k ==) . length) $
        subsequences $
          concat $
            replicate k [False, True]

log2 :: Int -> Int
log2 x
  | x < 2 = 0
  | otherwise = 1 + log2 (x `div` 2)

sat' :: BDD -> [Env]
sat' (x, xs) = filter ((x, xs) `checkSat`) $ allEnvs power
  where
    power = log2 (length xs + 1)

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
getNodes expr (n : ns) id = case (f, t) of
  (Prim x, Prim y) -> [(id, (n, boolToInt x, boolToInt y))]
  _ ->
    [(id, (n, id * 2, id * 2 + 1))]
      ++ getNodes f ns (id * 2)
      ++ getNodes t ns (id * 2 + 1)
  where
    t = restrict expr n True
    f = restrict expr n False

buildBDD :: BExp -> [Index] -> BDD
buildBDD (Prim x) [] = (boolToInt x, [])
buildBDD _ [] = error "Incorrect BExp"
buildBDD expr ls = (2, getNodes expr ls 2)

-----------------------------------------------------
-- PART IV
buildROBDD :: BExp -> [Index] -> BDD
buildROBDD expr index =
  let (root, nodes) = buildBDD expr index
   in (root, optimize nodes (length index))

optimize :: [BDDNode] -> Int -> [BDDNode]
optimize ns 0 = ns
optimize ns n =
  let a = deleteNodesList ns $ nodesToDelete ns
   in optimize a (n - 1)

deleteNodesList :: [BDDNode] -> [(NodeId, NodeId)] -> [BDDNode]
deleteNodesList nodes [] = nodes
deleteNodesList nodes (x : xs)
  | validDelete nodes x = deleteNodesList (removeNode nodes x) xs
  | otherwise = deleteNodesList nodes xs
  where
    validDelete ls (x, y) =
      any ((\id -> id == x || y == 1 || y == 0) . fst) ls

removeNode :: [BDDNode] -> (NodeId, NodeId) -> [BDDNode]
removeNode [] _ = []
removeNode (n@(id, (is, f, t)) : tail) (x, y)
  | f == x = removeNode ((id, (is, y, t)) : tail) (x, y)
  | t == x = removeNode ((id, (is, f, y)) : tail) (x, y)
  | id == x = removeNode tail (x, y)
  | otherwise = n : removeNode tail (x, y)

findSameTree :: BDDNode -> [BDDNode] -> [(NodeId, NodeId)]
findSameTree (id, (is, f, t)) =
  map (swap . (,) id . fst)
    . filter
      ( \(id1, (is1, f1, t1)) ->
          id /= id1 && f1 == f && t == t1
      )

nodesToDelete :: [BDDNode] -> [(NodeId, NodeId)]
nodesToDelete [] = []
nodesToDelete (n@(id, (is, f, t)) : tail)
  | f == t = (id, f) : nodesToDelete tail ++ sim
  | otherwise = sim ++ nodesToDelete tail
  where
    sim = findSameTree n tail

lengthBDD :: BDD -> Int
lengthBDD (x, xs) = length xs

bestROBDD :: BExp -> [Index] -> BDD
bestROBDD expr index =
  snd . head
    . sortOn fst
    $ map ((\x -> (length x, x)) . buildROBDD expr) indeces
  where
    indeces = permutations index

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
bdd1 = (0, [])
bdd2 = (2, [(4, (2, 1, 1)), (5, (2, 1, 0)), (2, (1, 4, 5))])
bdd3 = (5, [(5, (1, 0, 1))])
bdd4 =
  ( 2,
    [ (2, (2, 4, 5)),
      (4, (3, 8, 9)),
      (8, (7, 0, 1)),
      (9, (7, 0, 0)),
      (5, (3, 10, 11)),
      (10, (7, 0, 1)),
      (11, (7, 0, 1))
    ]
  )
bdd5 =
  ( 3,
    [ (4, (3, 8, 9)),
      (3, (2, 4, 5)),
      (8, (7, 1, 0)),
      (9, (7, 1, 1)),
      (5, (3, 10, 11)),
      (10, (7, 1, 0)),
      (11, (7, 1, 0))
    ]
  )
bdd6 =
  ( 2,
    [ (2, (1, 4, 5)),
      (4, (2, 8, 9)),
      (8, (3, 16, 17)),
      (16, (4, 0, 0)),
      (17, (4, 0, 1)),
      (9, (3, 18, 19)),
      (18, (4, 0, 0)),
      (19, (4, 0, 1)),
      (5, (2, 10, 11)),
      (10, (3, 20, 21)),
      (20, (4, 0, 0)),
      (21, (4, 0, 1)),
      (11, (3, 22, 23)),
      (22, (4, 1, 1)),
      (23, (4, 1, 1))
    ]
  )
bdd7 =
  ( 6,
    [ (6, (2, 4, 5)),
      (4, (3, 8, 9)),
      (8, (9, 1, 1)),
      (9, (9, 1, 0)),
      (5, (3, 10, 11)),
      (10, (9, 1, 1)),
      (11, (9, 1, 1))
    ]
  )
bdd8 = (2, [(2, (1, 1, 1))])
