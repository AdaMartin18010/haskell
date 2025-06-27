# 3.4 Persistent Data Structures

## 3.4.1 Mathematical Foundation

### 3.4.1.1 Persistence Definition

A **persistent data structure** is a data structure that preserves its previous versions when modified. Mathematically, a persistent data structure $D$ with operations $\mathcal{O}$ satisfies:

- **Immutability:** $D_i \neq D_j$ for $i \neq j$
- **Version Preservation:** $\forall v \in \mathcal{V}, D_v$ remains accessible
- **Efficient Sharing:** Common substructures are shared between versions

### 3.4.1.2 Persistence Types

1. **Partially Persistent:** Only the latest version can be modified
2. **Fully Persistent:** Any version can be modified
3. **Confluently Persistent:** Versions can be merged

### 3.4.1.3 Complexity Analysis

For a persistent data structure with $n$ operations:

- **Time Complexity:** $T(n)$ per operation
- **Space Complexity:** $S(n)$ total space
- **Version Access:** $O(\log n)$ for version tree traversal

## 3.4.2 Persistent Lists

### 3.4.2.1 Persistent List Implementation

```haskell
-- Persistent list with versioning
data PersistentList a = Empty | Cons a (PersistentList a) deriving Show

-- List operations that preserve previous versions
emptyList :: PersistentList a
emptyList = Empty

isEmpty :: PersistentList a -> Bool
isEmpty Empty = True
isEmpty _ = False

-- Cons operation (creates new version)
cons :: a -> PersistentList a -> PersistentList a
cons x xs = Cons x xs

-- Head operation
head' :: PersistentList a -> Maybe a
head' Empty = Nothing
head' (Cons x _) = Just x

-- Tail operation
tail' :: PersistentList a -> Maybe (PersistentList a)
tail' Empty = Nothing
tail' (Cons _ xs) = Just xs

-- Length operation
length' :: PersistentList a -> Int
length' Empty = 0
length' (Cons _ xs) = 1 + length' xs

-- Append operation (creates new version)
append :: PersistentList a -> PersistentList a -> PersistentList a
append Empty ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

-- Reverse operation (creates new version)
reverse' :: PersistentList a -> PersistentList a
reverse' xs = reverseAcc xs Empty
    where
        reverseAcc Empty acc = acc
        reverseAcc (Cons x xs) acc = reverseAcc xs (Cons x acc)

-- Map operation (creates new version)
map' :: (a -> b) -> PersistentList a -> PersistentList b
map' _ Empty = Empty
map' f (Cons x xs) = Cons (f x) (map' f xs)

-- Filter operation (creates new version)
filter' :: (a -> Bool) -> PersistentList a -> PersistentList a
filter' _ Empty = Empty
filter' p (Cons x xs)
    | p x = Cons x (filter' p xs)
    | otherwise = filter' p xs
```

### 3.4.2.2 Persistent List with Versioning

```haskell
-- Versioned persistent list
data VersionedList a = VersionedList {
    current :: PersistentList a,
    history :: [PersistentList a]
} deriving Show

-- Create new versioned list
newVersionedList :: VersionedList a
newVersionedList = VersionedList Empty []

-- Add element (creates new version)
addElement :: a -> VersionedList a -> VersionedList a
addElement x (VersionedList current history) = 
    let newCurrent = Cons x current
    in VersionedList newCurrent (current : history)

-- Undo operation
undo :: VersionedList a -> Maybe (VersionedList a)
undo (VersionedList _ []) = Nothing
undo (VersionedList current (prev:history)) = 
    Just (VersionedList prev history)

-- Redo operation
redo :: VersionedList a -> Maybe (VersionedList a)
redo (VersionedList current []) = Nothing
redo (VersionedList current history) = 
    Just (VersionedList (head history) (current : tail history))

-- Get version at index
getVersion :: Int -> VersionedList a -> Maybe (PersistentList a)
getVersion 0 (VersionedList current _) = Just current
getVersion n (VersionedList _ history)
    | n > 0 && n <= length history = Just (history !! (n - 1))
    | otherwise = Nothing
```

## 3.4.3 Persistent Trees

### 3.4.3.1 Persistent Binary Search Tree

```haskell
-- Persistent binary search tree
data PersistentBST a = Empty | Node (PersistentBST a) a (PersistentBST a) deriving Show

-- Insert operation (creates new version)
insertP :: Ord a => a -> PersistentBST a -> PersistentBST a
insertP x Empty = Node Empty x Empty
insertP x (Node left val right)
    | x < val = Node (insertP x left) val right
    | x > val = Node left val (insertP x right)
    | otherwise = Node left val right

-- Search operation
searchP :: Ord a => a -> PersistentBST a -> Bool
searchP _ Empty = False
searchP x (Node left val right)
    | x == val = True
    | x < val = searchP x left
    | otherwise = searchP x right

-- Delete operation (creates new version)
deleteP :: Ord a => a -> PersistentBST a -> PersistentBST a
deleteP _ Empty = Empty
deleteP x (Node left val right)
    | x < val = Node (deleteP x left) val right
    | x > val = Node left val (deleteP x right)
    | otherwise = deleteNode left right

-- Helper function for deletion
deleteNode :: Ord a => PersistentBST a -> PersistentBST a -> PersistentBST a
deleteNode Empty right = right
deleteNode left Empty = left
deleteNode left right = 
    let minVal = findMin right
        newRight = deleteP minVal right
    in Node left minVal newRight

-- Find minimum value
findMin :: PersistentBST a -> a
findMin (Node Empty val _) = val
findMin (Node left _ _) = findMin left

-- Inorder traversal
inorder :: PersistentBST a -> [a]
inorder Empty = []
inorder (Node left val right) = inorder left ++ [val] ++ inorder right
```

### 3.4.3.2 Persistent AVL Tree

```haskell
-- Persistent AVL tree
data PersistentAVL a = PEmpty | PNode (PersistentAVL a) a (PersistentAVL a) Int deriving Show

-- Height calculation
heightP :: PersistentAVL a -> Int
heightP PEmpty = 0
heightP (PNode _ _ _ h) = h

-- Balance factor
balanceFactorP :: PersistentAVL a -> Int
balanceFactorP PEmpty = 0
balanceFactorP (PNode left _ right _) = heightP left - heightP right

-- Insert operation (creates new version)
insertPAVL :: Ord a => a -> PersistentAVL a -> PersistentAVL a
insertPAVL x PEmpty = PNode PEmpty x PEmpty 1
insertPAVL x (PNode left val right h)
    | x < val = balanceP (insertPAVL x left) val right
    | x > val = balanceP left val (insertPAVL x right)
    | otherwise = PNode left val right h

-- Balancing operation
balanceP :: PersistentAVL a -> a -> PersistentAVL a -> PersistentAVL a
balanceP left val right
    | bf > 1 && balanceFactorP left > 0 = rotateRightP left val right
    | bf > 1 && balanceFactorP left < 0 = rotateLeftRightP left val right
    | bf < -1 && balanceFactorP right < 0 = rotateLeftP left val right
    | bf < -1 && balanceFactorP right > 0 = rotateRightLeftP left val right
    | otherwise = PNode left val right (max (heightP left) (heightP right) + 1)
    where bf = balanceFactorP (PNode left val right 0)

-- Rotation operations
rotateRightP :: PersistentAVL a -> a -> PersistentAVL a -> PersistentAVL a
rotateRightP (PNode a x b _) y c = 
    PNode a x (PNode b y c h2) h1
    where h1 = max (heightP a) (heightP b) + 1
          h2 = max h1 (heightP c) + 1

rotateLeftP :: PersistentAVL a -> a -> PersistentAVL a -> PersistentAVL a
rotateLeftP a x (PNode b y c _) = 
    PNode (PNode a x b h1) y c h2
    where h1 = max (heightP a) (heightP b) + 1
          h2 = max h1 (heightP c) + 1

rotateLeftRightP :: PersistentAVL a -> a -> PersistentAVL a -> PersistentAVL a
rotateLeftRightP left val right = 
    rotateRightP (rotateLeftP left val PEmpty) val right

rotateRightLeftP :: PersistentAVL a -> a -> PersistentAVL a -> PersistentAVL a
rotateRightLeftP left val right = 
    rotateLeftP left val (rotateRightP PEmpty val right)
```

## 3.4.4 Persistent Arrays

### 3.4.4.1 Persistent Array Implementation

```haskell
-- Persistent array using binary tree
data PersistentArray a = PArray {
    size :: Int,
    tree :: PersistentArrayTree a
} deriving Show

data PersistentArrayTree a = 
    PLeaf a | 
    PNode (PersistentArrayTree a) (PersistentArrayTree a) deriving Show

-- Create persistent array
newPersistentArray :: Int -> a -> PersistentArray a
newPersistentArray n defaultValue = PArray n (buildTree n defaultValue)
    where
        buildTree 1 val = PLeaf val
        buildTree n val = 
            let half = n `div` 2
            in PNode (buildTree half val) (buildTree (n - half) val)

-- Get element at index
getP :: Int -> PersistentArray a -> a
getP i (PArray size tree) 
    | i < 0 || i >= size = error "Index out of bounds"
    | otherwise = getFromTree i tree
    where
        getFromTree 0 (PLeaf val) = val
        getFromTree i (PNode left right)
            | i < size `div` 2 = getFromTree i left
            | otherwise = getFromTree (i - size `div` 2) right
        getFromTree _ _ = error "Invalid tree structure"

-- Set element at index (creates new version)
setP :: Int -> a -> PersistentArray a -> PersistentArray a
setP i val (PArray size tree)
    | i < 0 || i >= size = error "Index out of bounds"
    | otherwise = PArray size (setInTree i val tree)
    where
        setInTree 0 _ (PLeaf _) = PLeaf val
        setInTree i val (PNode left right)
            | i < size `div` 2 = PNode (setInTree i val left) right
            | otherwise = PNode left (setInTree (i - size `div` 2) val right)
        setInTree _ _ _ = error "Invalid tree structure"
```

### 3.4.4.2 Persistent Array with Path Copying

```haskell
-- Persistent array with path copying optimization
data PathCopyArray a = PathCopyArray {
    arraySize :: Int,
    root :: PathCopyNode a
} deriving Show

data PathCopyNode a = 
    PathLeaf a | 
    PathNode (PathCopyNode a) (PathCopyNode a) deriving Show

-- Create path copy array
newPathCopyArray :: Int -> a -> PathCopyArray a
newPathCopyArray n defaultValue = PathCopyArray n (buildPathTree n defaultValue)
    where
        buildPathTree 1 val = PathLeaf val
        buildPathTree n val = 
            let half = n `div` 2
            in PathNode (buildPathTree half val) (buildPathTree (n - half) val)

-- Get element with path copying
getPathCopy :: Int -> PathCopyArray a -> a
getPathCopy i (PathCopyArray size root) 
    | i < 0 || i >= size = error "Index out of bounds"
    | otherwise = getFromPathTree i root
    where
        getFromPathTree 0 (PathLeaf val) = val
        getFromPathTree i (PathNode left right)
            | i < size `div` 2 = getFromPathTree i left
            | otherwise = getFromPathTree (i - size `div` 2) right
        getFromPathTree _ _ = error "Invalid tree structure"

-- Set element with path copying (creates new version)
setPathCopy :: Int -> a -> PathCopyArray a -> PathCopyArray a
setPathCopy i val (PathCopyArray size root)
    | i < 0 || i >= size = error "Index out of bounds"
    | otherwise = PathCopyArray size (setInPathTree i val root)
    where
        setInPathTree 0 _ (PathLeaf _) = PathLeaf val
        setInPathTree i val (PathNode left right)
            | i < size `div` 2 = PathNode (setInPathTree i val left) right
            | otherwise = PathNode left (setInPathTree (i - size `div` 2) val right)
        setInPathTree _ _ _ = error "Invalid tree structure"
```

## 3.4.5 Persistent Maps

### 3.4.5.1 Persistent Map Implementation

```haskell
-- Persistent map using binary search tree
data PersistentMap k v = PMEmpty | PMNode (PersistentMap k v) k v (PersistentMap k v) deriving Show

-- Empty map
emptyPMap :: PersistentMap k v
emptyPMap = PMEmpty

-- Insert operation (creates new version)
insertPMap :: Ord k => k -> v -> PersistentMap k v -> PersistentMap k v
insertPMap key val PMEmpty = PMNode PMEmpty key val PMEmpty
insertPMap key val (PMNode left k v right)
    | key < k = PMNode (insertPMap key val left) k v right
    | key > k = PMNode left k v (insertPMap key val right)
    | otherwise = PMNode left key val right

-- Lookup operation
lookupPMap :: Ord k => k -> PersistentMap k v -> Maybe v
lookupPMap _ PMEmpty = Nothing
lookupPMap key (PMNode left k v right)
    | key == k = Just v
    | key < k = lookupPMap key left
    | otherwise = lookupPMap key right

-- Delete operation (creates new version)
deletePMap :: Ord k => k -> PersistentMap k v -> PersistentMap k v
deletePMap _ PMEmpty = PMEmpty
deletePMap key (PMNode left k v right)
    | key < k = PMNode (deletePMap key left) k v right
    | key > k = PMNode left k v (deletePMap key right)
    | otherwise = deletePMapNode left right

-- Helper function for deletion
deletePMapNode :: PersistentMap k v -> PersistentMap k v -> PersistentMap k v
deletePMapNode PMEmpty right = right
deletePMapNode left PMEmpty = left
deletePMapNode left right = 
    let (minKey, minVal) = findMinPMap right
        newRight = deletePMap minKey right
    in PMNode left minKey minVal newRight

-- Find minimum key-value pair
findMinPMap :: PersistentMap k v -> (k, v)
findMinPMap (PMNode PMEmpty k v _) = (k, v)
findMinPMap (PMNode left _ _ _) = findMinPMap left

-- Map size
sizePMap :: PersistentMap k v -> Int
sizePMap PMEmpty = 0
sizePMap (PMNode left _ _ right) = 1 + sizePMap left + sizePMap right

-- Convert to list
toListPMap :: PersistentMap k v -> [(k, v)]
toListPMap PMEmpty = []
toListPMap (PMNode left k v right) = 
    toListPMap left ++ [(k, v)] ++ toListPMap right
```

### 3.4.5.2 Persistent Hash Map

```haskell
-- Persistent hash map using persistent arrays
data PersistentHashMap k v = PersistentHashMap {
    buckets :: PersistentArray [(k, v)],
    hashFunction :: k -> Int
} deriving Show

-- Create persistent hash map
newPersistentHashMap :: (k -> Int) -> Int -> PersistentHashMap k v
newPersistentHashMap hashFn size = 
    PersistentHashMap (newPersistentArray size []) hashFn

-- Insert operation (creates new version)
insertPHashMap :: (Eq k, Ord k) => k -> v -> PersistentHashMap k v -> PersistentHashMap k v
insertPHashMap key val (PersistentHashMap buckets hashFn) = 
    let index = hashFn key `mod` arraySize buckets
        bucket = getP index buckets
        newBucket = insertInBucket key val bucket
        newBuckets = setP index newBucket buckets
    in PersistentHashMap newBuckets hashFn
    where
        insertInBucket k v [] = [(k, v)]
        insertInBucket k v ((k', v'):rest)
            | k == k' = (k, v) : rest
            | otherwise = (k', v') : insertInBucket k v rest

-- Lookup operation
lookupPHashMap :: Eq k => k -> PersistentHashMap k v -> Maybe v
lookupPHashMap key (PersistentHashMap buckets hashFn) = 
    let index = hashFn key `mod` arraySize buckets
        bucket = getP index buckets
    in lookupInBucket key bucket
    where
        lookupInBucket _ [] = Nothing
        lookupInBucket k ((k', v):rest)
            | k == k' = Just v
            | otherwise = lookupInBucket k rest

-- Delete operation (creates new version)
deletePHashMap :: Eq k => k -> PersistentHashMap k v -> PersistentHashMap k v
deletePHashMap key (PersistentHashMap buckets hashFn) = 
    let index = hashFn key `mod` arraySize buckets
        bucket = getP index buckets
        newBucket = deleteFromBucket key bucket
        newBuckets = setP index newBucket buckets
    in PersistentHashMap newBuckets hashFn
    where
        deleteFromBucket _ [] = []
        deleteFromBucket k ((k', v):rest)
            | k == k' = rest
            | otherwise = (k', v) : deleteFromBucket k rest
```

## 3.4.6 Persistent Queues

### 3.4.6.1 Persistent Queue Implementation

```haskell
-- Persistent queue using two persistent lists
data PersistentQueue a = PersistentQueue {
    front :: PersistentList a,
    back :: PersistentList a
} deriving Show

-- Empty queue
emptyQueue :: PersistentQueue a
emptyQueue = PersistentQueue Empty Empty

-- Check if queue is empty
isEmptyQueue :: PersistentQueue a -> Bool
isEmptyQueue (PersistentQueue front back) = 
    isEmpty front && isEmpty back

-- Enqueue operation (creates new version)
enqueue :: a -> PersistentQueue a -> PersistentQueue a
enqueue x (PersistentQueue front back) = 
    PersistentQueue front (cons x back)

-- Dequeue operation (creates new version)
dequeue :: PersistentQueue a -> Maybe (a, PersistentQueue a)
dequeue (PersistentQueue Empty back) = 
    case reverse' back of
        Empty -> Nothing
        Cons x xs -> Just (x, PersistentQueue xs Empty)
dequeue (PersistentQueue (Cons x front') back) = 
    Just (x, PersistentQueue front' back)

-- Peek operation
peek :: PersistentQueue a -> Maybe a
peek (PersistentQueue Empty back) = 
    case reverse' back of
        Empty -> Nothing
        Cons x _ -> Just x
peek (PersistentQueue (Cons x _) _) = Just x

-- Queue size
sizeQueue :: PersistentQueue a -> Int
sizeQueue (PersistentQueue front back) = 
    length' front + length' back
```

### 3.4.6.2 Persistent Priority Queue

```haskell
-- Persistent priority queue using persistent heap
data PersistentPriorityQueue a = PersistentPriorityQueue {
    heap :: PersistentHeap a
} deriving Show

data PersistentHeap a = 
    PHeapEmpty | 
    PHeapNode a (PersistentHeap a) (PersistentHeap a) deriving Show

-- Empty priority queue
emptyPriorityQueue :: PersistentPriorityQueue a
emptyPriorityQueue = PersistentPriorityQueue PHeapEmpty

-- Check if priority queue is empty
isEmptyPriorityQueue :: PersistentPriorityQueue a -> Bool
isEmptyPriorityQueue (PersistentPriorityQueue PHeapEmpty) = True
isEmptyPriorityQueue _ = False

-- Insert operation (creates new version)
insertPriority :: Ord a => a -> PersistentPriorityQueue a -> PersistentPriorityQueue a
insertPriority x (PersistentPriorityQueue heap) = 
    PersistentPriorityQueue (insertHeap x heap)
    where
        insertHeap x PHeapEmpty = PHeapNode x PHeapEmpty PHeapEmpty
        insertHeap x (PHeapNode val left right)
            | x <= val = PHeapNode x (insertHeap val right) left
            | otherwise = PHeapNode val (insertHeap x right) left

-- Extract minimum (creates new version)
extractMin :: Ord a => PersistentPriorityQueue a -> Maybe (a, PersistentPriorityQueue a)
extractMin (PersistentPriorityQueue PHeapEmpty) = Nothing
extractMin (PersistentPriorityQueue (PHeapNode val left right)) = 
    Just (val, PersistentPriorityQueue (mergeHeaps left right))
    where
        mergeHeaps PHeapEmpty right = right
        mergeHeaps left PHeapEmpty = left
        mergeHeaps left@(PHeapNode lval lleft lright) right@(PHeapNode rval rleft rright)
            | lval <= rval = PHeapNode lval (mergeHeaps lleft lright) right
            | otherwise = PHeapNode rval left (mergeHeaps rleft rright)

-- Peek minimum
peekMin :: PersistentPriorityQueue a -> Maybe a
peekMin (PersistentPriorityQueue PHeapEmpty) = Nothing
peekMin (PersistentPriorityQueue (PHeapNode val _ _)) = Just val
```

## 3.4.7 Performance Analysis

### 3.4.7.1 Time Complexity Analysis

```haskell
-- Time complexity for persistent operations
persistentComplexity :: [(String, String, String, String)]
persistentComplexity = [
    ("Persistent List", "O(1)", "O(n)", "O(n)"),
    ("Persistent BST", "O(log n)", "O(log n)", "O(log n)"),
    ("Persistent AVL", "O(log n)", "O(log n)", "O(log n)"),
    ("Persistent Array", "O(log n)", "O(log n)", "O(log n)"),
    ("Persistent Map", "O(log n)", "O(log n)", "O(log n)"),
    ("Persistent Queue", "O(1)", "O(1)", "O(1)"),
    ("Persistent Priority Queue", "O(log n)", "O(log n)", "O(log n)")
    ]
    -- Columns: Data Structure, Access, Update, Space per operation
```

### 3.4.7.2 Space Complexity Analysis

```haskell
-- Space complexity analysis
persistentSpaceComplexity :: [(String, String, String)]
persistentSpaceComplexity = [
    ("Persistent List", "O(n)", "O(1) per operation"),
    ("Persistent BST", "O(n)", "O(log n) per operation"),
    ("Persistent AVL", "O(n)", "O(log n) per operation"),
    ("Persistent Array", "O(n)", "O(log n) per operation"),
    ("Persistent Map", "O(n)", "O(log n) per operation"),
    ("Persistent Queue", "O(n)", "O(1) per operation"),
    ("Persistent Priority Queue", "O(n)", "O(log n) per operation")
    ]
    -- Columns: Data Structure, Total Space, Space per Operation
```

### 3.4.7.3 Amortized Analysis

```haskell
-- Amortized complexity analysis
amortizedComplexity :: [(String, String, String)]
amortizedComplexity = [
    ("Persistent List", "O(1)", "O(1)"),
    ("Persistent BST", "O(log n)", "O(log n)"),
    ("Persistent AVL", "O(log n)", "O(log n)"),
    ("Persistent Array", "O(log n)", "O(log n)"),
    ("Persistent Map", "O(log n)", "O(log n)"),
    ("Persistent Queue", "O(1)", "O(1)"),
    ("Persistent Priority Queue", "O(log n)", "O(log n)")
    ]
    -- Columns: Data Structure, Amortized Time, Amortized Space
```

## 3.4.8 Applications and Use Cases

### 3.4.8.1 Version Control Systems

```haskell
-- Simple version control system using persistent data structures
data VersionControl a = VersionControl {
    versions :: PersistentMap Int a,
    currentVersion :: Int,
    nextVersion :: Int
} deriving Show

-- Create new version control system
newVersionControl :: VersionControl a
newVersionControl = VersionControl emptyPMap 0 1

-- Save version
saveVersion :: a -> VersionControl a -> VersionControl a
saveVersion data' (VersionControl versions current next) = 
    VersionControl (insertPMap next data') next (next + 1)

-- Load version
loadVersion :: Int -> VersionControl a -> Maybe a
loadVersion version (VersionControl versions _ _) = 
    lookupPMap version versions

-- Switch to version
switchVersion :: Int -> VersionControl a -> Maybe (VersionControl a)
switchVersion version vc@(VersionControl versions _ next) = 
    case lookupPMap version versions of
        Just _ -> Just vc { currentVersion = version }
        Nothing -> Nothing
```

### 3.4.8.2 Undo/Redo Systems

```haskell
-- Undo/Redo system using persistent data structures
data UndoRedo a = UndoRedo {
    current :: a,
    undoStack :: PersistentList a,
    redoStack :: PersistentList a
} deriving Show

-- Create undo/redo system
newUndoRedo :: a -> UndoRedo a
newUndoRedo initial = UndoRedo initial Empty Empty

-- Perform action
performAction :: (a -> a) -> UndoRedo a -> UndoRedo a
performAction f (UndoRedo current undo redo) = 
    UndoRedo (f current) (cons current undo) Empty

-- Undo action
undoAction :: UndoRedo a -> Maybe (UndoRedo a)
undoAction (UndoRedo current Empty _) = Nothing
undoAction (UndoRedo current (Cons prev undo) redo) = 
    Just (UndoRedo prev undo (cons current redo))

-- Redo action
redoAction :: UndoRedo a -> Maybe (UndoRedo a)
redoAction (UndoRedo current _ Empty) = Nothing
redoAction (UndoRedo current undo (Cons next redo)) = 
    Just (UndoRedo next (cons current undo) redo)
```

## 3.4.9 References

- [3.1 Data Structures Overview](01-Data-Structures-Overview.md)
- [3.2 Basic Data Structures](02-Basic-Data-Structures.md)
- [3.3 Advanced Data Structures](03-Advanced-Data-Structures.md)
- [2.2 Algebraic Data Types](../02-Type-System/02-Algebraic-Data-Types.md)

---

**Next:** [3.5 Functional Data Structures](05-Functional-Data-Structures.md)
