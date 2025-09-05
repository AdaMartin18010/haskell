# 3.3 Advanced Data Structures

## 3.3.1 Mathematical Foundation

### 3.3.1.1 Advanced Data Structure Definition

An **advanced data structure** is a composite data organization that provides efficient operations for specific use cases. Mathematically, an advanced data structure $D$ is defined by:

- A set of elements $\mathcal{E}_D$
- A set of operations $\mathcal{O}_D = \{op_1, op_2, \ldots, op_n\}$
- Time complexity bounds $\mathcal{T}_D$ for each operation
- Space complexity bounds $\mathcal{S}_D$

### 3.3.1.2 Complexity Analysis

For a data structure $D$ with $n$ elements:

- **Time Complexity:** $T(n)$ - number of operations required
- **Space Complexity:** $S(n)$ - memory usage
- **Amortized Complexity:** $\frac{\sum_{i=1}^{n} T(i)}{n}$ - average cost per operation

## 3.3.2 Balanced Trees

### 3.3.2.1 AVL Trees

**AVL trees** are self-balancing binary search trees where the heights of the two child subtrees of any node differ by at most one.

```haskell
-- AVL Tree definition
data AVLTree a = Empty | Node (AVLTree a) a (AVLTree a) Int

-- Height calculation
height :: AVLTree a -> Int
height Empty = 0
height (Node _ _ _ h) = h

-- Balance factor
balanceFactor :: AVLTree a -> Int
balanceFactor Empty = 0
balanceFactor (Node left _ right _) = height left - height right

-- AVL tree operations
insertAVL :: Ord a => a -> AVLTree a -> AVLTree a
insertAVL x Empty = Node Empty x Empty 1
insertAVL x (Node left val right h)
    | x < val = balance (insertAVL x left) val right
    | x > val = balance left val (insertAVL x right)
    | otherwise = Node left val right h

-- Balancing operations
balance :: AVLTree a -> a -> AVLTree a -> AVLTree a
balance left val right
    | bf > 1 && balanceFactor left > 0 = rotateRight left val right
    | bf > 1 && balanceFactor left < 0 = rotateLeftRight left val right
    | bf < -1 && balanceFactor right < 0 = rotateLeft left val right
    | bf < -1 && balanceFactor right > 0 = rotateRightLeft left val right
    | otherwise = Node left val right (max (height left) (height right) + 1)
    where bf = balanceFactor (Node left val right 0)

-- Rotation operations
rotateRight :: AVLTree a -> a -> AVLTree a -> AVLTree a
rotateRight (Node a x b _) y c = Node a x (Node b y c h2) h1
    where h1 = max (height a) (height b) + 1
          h2 = max h1 (height c) + 1

rotateLeft :: AVLTree a -> a -> AVLTree a -> AVLTree a
rotateLeft a x (Node b y c _) = Node (Node a x b h1) y c h2
    where h1 = max (height a) (height b) + 1
          h2 = max h1 (height c) + 1

rotateLeftRight :: AVLTree a -> a -> AVLTree a -> AVLTree a
rotateLeftRight left val right = rotateRight (rotateLeft left val Empty) val right

rotateRightLeft :: AVLTree a -> a -> AVLTree a -> AVLTree a
rotateRightLeft left val right = rotateLeft left val (rotateRight Empty val right)
```

### 3.3.2.2 Red-Black Trees

**Red-Black trees** are self-balancing binary search trees with the following properties:

1. Every node is either red or black
2. The root is black
3. All leaves (NIL) are black
4. Red nodes cannot have red children
5. Every path from root to leaves has the same number of black nodes

```haskell
-- Red-Black Tree definition
data Color = Red | Black
data RBTree a = RBEmpty | RBNode Color (RBTree a) a (RBTree a)

-- Red-Black tree operations
insertRB :: Ord a => a -> RBTree a -> RBTree a
insertRB x tree = makeBlack (insertRB' x tree)
    where
        insertRB' x RBEmpty = RBNode Red RBEmpty x RBEmpty
        insertRB' x (RBNode color left val right)
            | x < val = balance color (insertRB' x left) val right
            | x > val = balance color left val (insertRB' x right)
            | otherwise = RBNode color left val right

-- Balancing Red-Black tree
balance :: Color -> RBTree a -> a -> RBTree a -> RBTree a
balance Black (RBNode Red (RBNode Red a x b) y c) z d = 
    RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black (RBNode Red a x (RBNode Red b y c)) z d = 
    RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black a x (RBNode Red b y (RBNode Red c z d)) = 
    RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance Black a x (RBNode Red (RBNode Red b y c) z d) = 
    RBNode Red (RBNode Black a x b) y (RBNode Black c z d)
balance color left val right = RBNode color left val right

-- Make root black
makeBlack :: RBTree a -> RBTree a
makeBlack RBEmpty = RBEmpty
makeBlack (RBNode _ left val right) = RBNode Black left val right
```

## 3.3.3 Heaps and Priority Queues

### 3.3.3.1 Binary Heaps

A **binary heap** is a complete binary tree that satisfies the heap property:

- **Max Heap:** Parent ≥ Children
- **Min Heap:** Parent ≤ Children

```haskell
-- Binary Heap definition
data BinaryHeap a = EmptyHeap | Heap Int [a] deriving Show

-- Heap operations
emptyHeap :: BinaryHeap a
emptyHeap = Heap 0 []

isEmpty :: BinaryHeap a -> Bool
isEmpty EmptyHeap = True
isEmpty (Heap 0 _) = True
isEmpty _ = False

-- Insert operation
insert :: Ord a => a -> BinaryHeap a -> BinaryHeap a
insert x EmptyHeap = Heap 1 [x]
insert x (Heap n xs) = Heap (n + 1) (bubbleUp (n + 1) (x:xs))

-- Bubble up operation
bubbleUp :: Ord a => Int -> [a] -> [a]
bubbleUp 1 xs = xs
bubbleUp i xs
    | parentVal > currentVal = xs
    | otherwise = bubbleUp parent (swap parent i xs)
    where
        currentVal = xs !! (i - 1)
        parent = i `div` 2
        parentVal = xs !! (parent - 1)

-- Swap elements
swap :: Int -> Int -> [a] -> [a]
swap i j xs = take (i-1) xs ++ [xs !! (j-1)] ++ take (j-i-1) (drop i xs) ++ [xs !! (i-1)] ++ drop j xs

-- Extract maximum
extractMax :: Ord a => BinaryHeap a -> (a, BinaryHeap a)
extractMax EmptyHeap = error "Empty heap"
extractMax (Heap 1 [x]) = (x, EmptyHeap)
extractMax (Heap n (x:xs)) = (x, Heap (n-1) (bubbleDown 1 (last xs : init xs)))

-- Bubble down operation
bubbleDown :: Ord a => Int -> [a] -> [a]
bubbleDown i xs
    | leftChild > n = xs
    | rightChild > n = if currentVal < leftVal then swap i leftChild xs else xs
    | currentVal >= max leftVal rightVal = xs
    | leftVal >= rightVal = bubbleDown leftChild (swap i leftChild xs)
    | otherwise = bubbleDown rightChild (swap i rightChild xs)
    where
        n = length xs
        currentVal = xs !! (i - 1)
        leftChild = 2 * i
        rightChild = 2 * i + 1
        leftVal = if leftChild <= n then xs !! (leftChild - 1) else minBound
        rightVal = if rightChild <= n then xs !! (rightChild - 1) else minBound

-- Heapify operation
heapify :: Ord a => [a] -> BinaryHeap a
heapify xs = Heap (length xs) (heapify' xs)
    where
        heapify' [] = []
        heapify' xs = foldr insert [] xs
```

### 3.3.3.2 Fibonacci Heaps

**Fibonacci heaps** are a collection of trees that satisfy the min-heap property, providing amortized $O(1)$ insert and decrease-key operations.

```haskell
-- Fibonacci Heap definition
data FibHeap a = FibHeap [FibTree a] deriving Show

data FibTree a = FibNode a [FibTree a] deriving Show

-- Fibonacci heap operations
emptyFibHeap :: FibHeap a
emptyFibHeap = FibHeap []

insertFib :: Ord a => a -> FibHeap a -> FibHeap a
insertFib x (FibHeap trees) = FibHeap (FibNode x [] : trees)

-- Find minimum
findMin :: Ord a => FibHeap a -> Maybe a
findMin (FibHeap []) = Nothing
findMin (FibHeap trees) = Just (minimum [rootValue t | t <- trees])
    where rootValue (FibNode x _) = x

-- Extract minimum
extractMin :: Ord a => FibHeap a -> (Maybe a, FibHeap a)
extractMin (FibHeap []) = (Nothing, FibHeap [])
extractMin (FibHeap trees) = (Just minVal, consolidate remainingTrees)
    where
        minTree = minimumBy (\t1 t2 -> compare (rootValue t1) (rootValue t2)) trees
        minVal = rootValue minTree
        remainingTrees = filter (/= minTree) trees ++ children minTree
        rootValue (FibNode x _) = x
        children (FibNode _ cs) = cs

-- Consolidate operation
consolidate :: Ord a => [FibTree a] -> FibHeap a
consolidate trees = FibHeap (consolidate' trees [])
    where
        consolidate' [] acc = acc
        consolidate' (t:ts) acc = consolidate' ts (merge t acc)

-- Merge trees
merge :: Ord a => FibTree a -> [FibTree a] -> [FibTree a]
merge t [] = [t]
merge t (t':ts)
    | degree t == degree t' = merge (link t t') ts
    | otherwise = t : merge t' ts
    where
        degree (FibNode _ children) = length children
        link t1@(FibNode x1 c1) t2@(FibNode x2 c2)
            | x1 <= x2 = FibNode x1 (t2 : c1)
            | otherwise = FibNode x2 (t1 : c2)
```

## 3.3.4 Tries and Prefix Trees

### 3.3.4.1 Trie Data Structure

A **trie** (prefix tree) is a tree-like data structure used to store strings, where each node represents a character.

```haskell
-- Trie definition
data Trie = TrieNode Bool (Map Char Trie) deriving Show

-- Empty trie
emptyTrie :: Trie
emptyTrie = TrieNode False Map.empty

-- Insert string into trie
insertTrie :: String -> Trie -> Trie
insertTrie [] (TrieNode _ children) = TrieNode True children
insertTrie (c:cs) (TrieNode isEnd children) = 
    TrieNode isEnd (Map.insert c (insertTrie cs child) children)
    where
        child = Map.findWithDefault emptyTrie c children

-- Search string in trie
searchTrie :: String -> Trie -> Bool
searchTrie [] (TrieNode isEnd _) = isEnd
searchTrie (c:cs) (TrieNode _ children) = 
    case Map.lookup c children of
        Just child -> searchTrie cs child
        Nothing -> False

-- Check if string is prefix
startsWith :: String -> Trie -> Bool
startsWith [] _ = True
startsWith (c:cs) (TrieNode _ children) = 
    case Map.lookup c children of
        Just child -> startsWith cs child
        Nothing -> False

-- Get all strings with given prefix
getPrefixStrings :: String -> Trie -> [String]
getPrefixStrings prefix trie = 
    case findPrefixNode prefix trie of
        Just node -> getAllStrings node
        Nothing -> []
    where
        findPrefixNode [] node = Just node
        findPrefixNode (c:cs) (TrieNode _ children) = 
            case Map.lookup c children of
                Just child -> findPrefixNode cs child
                Nothing -> Nothing

        getAllStrings :: Trie -> [String]
        getAllStrings (TrieNode isEnd children) = 
            (if isEnd then [""] else []) ++ 
            concat [map (c:) (getAllStrings child) | (c, child) <- Map.toList children]
```

### 3.3.4.2 Compressed Trie

A **compressed trie** (radix tree) compresses chains of single-child nodes into single edges.

```haskell
-- Compressed Trie definition
data CompressedTrie = CompressedNode String Bool [CompressedTrie] deriving Show

-- Empty compressed trie
emptyCompressedTrie :: CompressedTrie
emptyCompressedTrie = CompressedNode "" False []

-- Insert into compressed trie
insertCompressedTrie :: String -> CompressedTrie -> CompressedTrie
insertCompressedTrie [] (CompressedNode prefix isEnd children) = 
    CompressedNode prefix True children
insertCompressedTrie str (CompressedNode prefix isEnd children) = 
    case findCommonPrefix str prefix of
        (common, strSuffix, prefixSuffix)
            | null strSuffix && null prefixSuffix -> 
                CompressedNode common True children
            | null strSuffix -> 
                CompressedNode common True [CompressedNode prefixSuffix isEnd children]
            | null prefixSuffix -> 
                CompressedNode common isEnd (insertCompressedTrie strSuffix children)
            | otherwise -> 
                CompressedNode common False [
                    CompressedNode strSuffix True [],
                    CompressedNode prefixSuffix isEnd children
                ]

-- Find common prefix
findCommonPrefix :: String -> String -> (String, String, String)
findCommonPrefix [] ys = ("", [], ys)
findCommonPrefix xs [] = ("", xs, [])
findCommonPrefix (x:xs) (y:ys)
    | x == y = let (common, xs', ys') = findCommonPrefix xs ys
               in (x:common, xs', ys')
    | otherwise = ("", x:xs, y:ys)
```

## 3.3.5 Skip Lists

### 3.3.5.1 Skip List Definition

A **skip list** is a probabilistic data structure that allows fast search within an ordered sequence of elements.

```haskell
-- Skip List definition
data SkipList a = SkipList Int (SkipNode a) deriving Show

data SkipNode a = SkipNode a [SkipNode a] | Nil deriving Show

-- Empty skip list
emptySkipList :: SkipList a
emptySkipList = SkipList 0 Nil

-- Random level generation
randomLevel :: IO Int
randomLevel = do
    r <- randomRIO (0, 1)
    if r < 0.5 then return 0 else (+1) <$> randomLevel

-- Insert into skip list
insertSkipList :: Ord a => a -> SkipList a -> IO (SkipList a)
insertSkipList x (SkipList maxLevel head) = do
    level <- randomLevel
    let newLevel = min level maxLevel
    newHead <- insertAtLevel x newLevel head
    return (SkipList (max maxLevel newLevel) newHead)

-- Insert at specific level
insertAtLevel :: Ord a => a -> Int -> SkipNode a -> IO (SkipNode a)
insertAtLevel x level Nil = SkipNode x (replicate (level + 1) Nil)
insertAtLevel x level (SkipNode val nexts)
    | x < val = do
        newNode <- SkipNode x <$> replicateM (level + 1) (return Nil)
        return (updateNexts newNode level (SkipNode val nexts))
    | otherwise = do
        newNexts <- mapM (insertAtLevel x level) nexts
        return (SkipNode val newNexts)

-- Update next pointers
updateNexts :: SkipNode a -> Int -> SkipNode a -> SkipNode a
updateNexts newNode level (SkipNode val nexts) = 
    SkipNode val (take level nexts ++ [newNode] ++ drop (level + 1) nexts)

-- Search in skip list
searchSkipList :: Ord a => a -> SkipList a -> Bool
searchSkipList x (SkipList _ head) = searchNode x head

searchNode :: Ord a => a -> SkipNode a -> Bool
searchNode _ Nil = False
searchNode x (SkipNode val nexts)
    | x == val = True
    | x < val = False
    | otherwise = any (searchNode x) nexts
```

## 3.3.6 B-Trees

### 3.3.6.1 B-Tree Definition

A **B-tree** is a self-balancing tree data structure that maintains sorted data and allows searches, sequential access, insertions, and deletions in logarithmic time.

```haskell
-- B-Tree definition
data BTree a = BEmpty | BNode [a] [BTree a] deriving Show

-- B-Tree operations
insertBTree :: Ord a => a -> BTree a -> BTree a
insertBTree x BEmpty = BNode [x] []
insertBTree x (BNode keys children) = 
    case insertNonFull x (BNode keys children) of
        Just tree -> tree
        Nothing -> splitRoot (BNode keys children)

-- Insert into non-full node
insertNonFull :: Ord a => a -> BTree a -> Maybe (BTree a)
insertNonFull x (BNode keys []) = 
    let newKeys = insertSorted x keys
    in if length newKeys <= 3 then Just (BNode newKeys []) else Nothing
insertNonFull x (BNode keys children) = 
    let (childIndex, child) = findChild x keys children
        newChild = insertNonFull x child
    in case newChild of
        Just c -> Just (BNode keys (updateChild childIndex c children))
        Nothing -> Nothing

-- Insert sorted
insertSorted :: Ord a => a -> [a] -> [a]
insertSorted x [] = [x]
insertSorted x (y:ys)
    | x <= y = x:y:ys
    | otherwise = y:insertSorted x ys

-- Find child for insertion
findChild :: Ord a => a -> [a] -> [BTree a] -> (Int, BTree a)
findChild x keys children = 
    let index = length (takeWhile (< x) keys)
    in (index, children !! index)

-- Update child
updateChild :: Int -> BTree a -> [BTree a] -> [BTree a]
updateChild i newChild children = 
    take i children ++ [newChild] ++ drop (i + 1) children

-- Split root
splitRoot :: BTree a -> BTree a
splitRoot (BNode keys children) = 
    let mid = length keys `div` 2
        (leftKeys, midKey:rightKeys) = splitAt mid keys
        (leftChildren, rightChildren) = splitAt (mid + 1) children
    in BNode [midKey] [
        BNode leftKeys leftChildren,
        BNode rightKeys rightChildren
    ]
```

## 3.3.7 Advanced Tree Structures

### 3.3.7.1 Splay Trees

**Splay trees** are self-adjusting binary search trees that move recently accessed elements to the root.

```haskell
-- Splay Tree definition
data SplayTree a = SEmpty | SNode (SplayTree a) a (SplayTree a) deriving Show

-- Splay operation
splay :: Ord a => a -> SplayTree a -> SplayTree a
splay x SEmpty = SEmpty
splay x (SNode left val right)
    | x == val = SNode left val right
    | x < val = splayLeft x left val right
    | otherwise = splayRight x left val right

-- Splay left
splayLeft :: Ord a => a -> SplayTree a -> a -> SplayTree a -> SplayTree a
splayLeft x SEmpty val right = SNode SEmpty val right
splayLeft x (SNode a y b) val right
    | x == y = SNode a y (SNode b val right)
    | x < y = case a of
        SEmpty -> SNode SEmpty y (SNode b val right)
        SNode a1 z a2 -> SNode (splay x (SNode a1 z a2)) y (SNode b val right)
    | otherwise = case b of
        SEmpty -> SNode (SNode a y SEmpty) val right
        SNode b1 z b2 -> SNode (SNode a y b1) z (splay x (SNode b2 val right))

-- Splay right
splayRight :: Ord a => a -> SplayTree a -> a -> SplayTree a -> SplayTree a
splayRight x left val SEmpty = SNode left val SEmpty
splayRight x left val (SNode b y c)
    | x == y = SNode (SNode left val b) y c
    | x < y = case b of
        SEmpty -> SNode left val (SNode SEmpty y c)
        SNode b1 z b2 -> SNode (SNode left val b1) z (splay x (SNode b2 y c))
    | otherwise = case c of
        SEmpty -> SNode (SNode left val b) y SEmpty
        SNode c1 z c2 -> SNode (SNode (SNode left val b) y c1) z (splay x c2)

-- Insert into splay tree
insertSplay :: Ord a => a -> SplayTree a -> SplayTree a
insertSplay x SEmpty = SNode SEmpty x SEmpty
insertSplay x tree = 
    let splayed = splay x tree
    in case splayed of
        SNode left val right
            | x < val -> SNode left x (SNode SEmpty val right)
            | x > val -> SNode (SNode left val SEmpty) x right
            | otherwise -> splayed
        _ -> splayed
```

### 3.3.7.2 Treaps

A **treap** is a binary search tree where each node has both a key and a priority, and the tree satisfies both the binary search tree property and the heap property.

```haskell
-- Treap definition
data Treap a = TEmpty | TNode (Treap a) a Int (Treap a) deriving Show

-- Insert into treap
insertTreap :: Ord a => a -> Treap a -> Treap a
insertTreap x TEmpty = TNode TEmpty x (randomPriority) TEmpty
insertTreap x (TNode left val priority right)
    | x < val = rotateRight (TNode (insertTreap x left) val priority right)
    | x > val = rotateLeft (TNode left val priority (insertTreap x right))
    | otherwise = TNode left val priority right

-- Random priority (simplified)
randomPriority :: Int
randomPriority = 42  -- In practice, use proper random number generation

-- Rotate right
rotateRight :: Treap a -> Treap a
rotateRight TEmpty = TEmpty
rotateRight (TNode (TNode a x px b) y py c) = 
    TNode a x px (TNode b y py c)
rotateRight t = t

-- Rotate left
rotateLeft :: Treap a -> Treap a
rotateLeft TEmpty = TEmpty
rotateLeft (TNode a x px (TNode b y py c)) = 
    TNode (TNode a x px b) y py c
rotateLeft t = t
```

## 3.3.8 Performance Analysis

### 3.3.8.1 Time Complexity Comparison

```haskell
-- Time complexity analysis
data Complexity = O1 | OLogN | ON | ONLogN | ON2 deriving Show

-- Operation complexity table
complexityTable :: [(String, Complexity, Complexity, Complexity)]
complexityTable = [
    ("AVL Tree", OLogN, OLogN, OLogN),
    ("Red-Black Tree", OLogN, OLogN, OLogN),
    ("Binary Heap", OLogN, O1, OLogN),
    ("Fibonacci Heap", O1, OLogN, OLogN),
    ("Trie", O(m), O(m), O(m)),
    ("Skip List", OLogN, OLogN, OLogN),
    ("B-Tree", OLogN, OLogN, OLogN),
    ("Splay Tree", OLogN, OLogN, OLogN),
    ("Treap", OLogN, OLogN, OLogN)
    ]
    where m = length of string
```

### 3.3.8.2 Space Complexity Analysis

```haskell
-- Space complexity analysis
spaceComplexity :: [(String, Complexity)]
spaceComplexity = [
    ("AVL Tree", ON),
    ("Red-Black Tree", ON),
    ("Binary Heap", ON),
    ("Fibonacci Heap", ON),
    ("Trie", O(m * n)),
    ("Skip List", ON),
    ("B-Tree", ON),
    ("Splay Tree", ON),
    ("Treap", ON)
    ]
    where m = average string length, n = number of strings
```

## 3.3.9 References

- [3.1 Data Structures Overview](01-Data-Structures-Overview.md)
- [3.2 Basic Data Structures](02-Basic-Data-Structures.md)
- [4.1 Sorting Algorithms](../04-Algorithms/01-Sorting-Algorithms.md)
- [2.2 Algebraic Data Types](../02-Type-System/02-Algebraic-Data-Types.md)

---

**Next:** [3.4 Persistent Data Structures](04-Persistent-Data-Structures.md)
