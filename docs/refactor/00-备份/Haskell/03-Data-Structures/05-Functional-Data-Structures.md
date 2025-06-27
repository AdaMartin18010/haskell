# 3.5 Functional Data Structures

## 3.5.1 Introduction and Mathematical Foundation

### 3.5.1.1 Definition

A **functional data structure** is a data structure designed for use in functional programming, emphasizing immutability, persistence, and efficient sharing of structure between versions.

- **Immutability:** No destructive updates; all operations yield new versions.
- **Persistence:** All previous versions remain accessible.
- **Structural Sharing:** Common substructures are reused to minimize copying.

### 3.5.1.2 Formal Properties

Let $D$ be a functional data structure with operations $\mathcal{O}_D$:

- $\forall op \in \mathcal{O}_D, D' = op(D)$, $D$ remains unchanged.
- $\exists$ efficient sharing: $\text{share}(D, D') \gg 0$.

## 3.5.2 Amortized Analysis and Efficiency

### 3.5.2.1 Amortized Complexity

Amortized analysis is used to show that the average cost per operation is low, even if some operations are expensive.

- **Banker's Method:** Assign credits to operations to pay for future work.
- **Physicist's Method:** Use potential functions to measure stored work.

#### Example: Amortized O(1) Queue

```haskell
-- Banker's Queue (Okasaki)
data Queue a = Q [a] [a]  -- front, rear

emptyQ :: Queue a
emptyQ = Q [] []

isEmptyQ :: Queue a -> Bool
isEmptyQ (Q [] []) = True
isEmptyQ _ = False

snoc :: a -> Queue a -> Queue a
snoc x (Q f r) = checkQ (Q f (x:r))

headQ :: Queue a -> a
headQ (Q [] _) = error "empty queue"
headQ (Q (x:_) _) = x

tailQ :: Queue a -> Queue a
tailQ (Q [] _) = error "empty queue"
tailQ (Q (_:f) r) = checkQ (Q f r)

checkQ :: Queue a -> Queue a
checkQ (Q [] r) = Q (reverse r) []
checkQ q = q
```

## 3.5.3 Persistent Lists and Trees

### 3.5.3.1 Persistent List (Cons List)

```haskell
-- Standard persistent list
data List a = Nil | Cons a (List a)

-- All operations (cons, head, tail, map, filter) are O(1) or O(n) and persistent
```

### 3.5.3.2 Finger Trees

Finger trees are general-purpose, purely functional data structures supporting amortized O(1) access at both ends and O(log n) concatenation and splitting.

```haskell
{-# LANGUAGE GADTs #-}
data FingerTree a = EmptyFT
                  | Single a
                  | Deep [a] (FingerTree [a]) [a]

-- Example operations (simplified):
emptyFT :: FingerTree a
emptyFT = EmptyFT

singletonFT :: a -> FingerTree a
singletonFT x = Single x

-- Insertion at front
consFT :: a -> FingerTree a -> FingerTree a
consFT x t = undefined  -- See Okasaki's "Purely Functional Data Structures"

-- Insertion at rear
snocFT :: FingerTree a -> a -> FingerTree a
snocFT t x = undefined
```

## 3.5.4 Functional Queues and Deques

### 3.5.4.1 Real-Time Queue

A real-time queue guarantees O(1) worst-case time per operation using lazy evaluation.

```haskell
-- Real-time queue (Okasaki)
data RTQueue a = RTQ [a] [a] [a]

emptyRTQ :: RTQueue a
emptyRTQ = RTQ [] [] []

isEmptyRTQ :: RTQueue a -> Bool
isEmptyRTQ (RTQ [] [] []) = True
isEmptyRTQ _ = False

snocRTQ :: a -> RTQueue a -> RTQueue a
snocRTQ x (RTQ f r s) = execRTQ f (x:r) s

headRTQ :: RTQueue a -> a
headRTQ (RTQ [] _ _) = error "empty queue"
headRTQ (RTQ (x:_) _ _) = x

tailRTQ :: RTQueue a -> RTQueue a
tailRTQ (RTQ [] _ _) = error "empty queue"
tailRTQ (RTQ (_:f) r s) = execRTQ f r s

execRTQ :: [a] -> [a] -> [a] -> RTQueue a
execRTQ f r [] = let f' = rotateRTQ f r [] in RTQ f' [] f'
execRTQ f r (_:s) = RTQ f r s

rotateRTQ :: [a] -> [a] -> [a] -> [a]
rotateRTQ [] (y:_) a = y:a
rotateRTQ (x:xs) (y:ys) a = x : rotateRTQ xs ys (y:a)
rotateRTQ _ _ _ = error "invalid state"
```

### 3.5.4.2 Deques (Double-Ended Queues)

```haskell
-- Banker's deque (simplified)
data Deque a = DQ [a] [a]

emptyDQ :: Deque a
emptyDQ = DQ [] []

pushFront :: a -> Deque a -> Deque a
pushFront x (DQ f r) = DQ (x:f) r

pushBack :: a -> Deque a -> Deque a
pushBack x (DQ f r) = DQ f (x:r)

popFront :: Deque a -> (a, Deque a)
popFront (DQ [] []) = error "empty deque"
popFront (DQ (x:f) r) = (x, DQ f r)
popFront (DQ [] r) = let (x:xs) = reverse r in (x, DQ xs [])

popBack :: Deque a -> (a, Deque a)
popBack (DQ [] []) = error "empty deque"
popBack (DQ f (x:r)) = (x, DQ f r)
popBack (DQ f []) = let (x:xs) = reverse f in (x, DQ [] xs)
```

## 3.5.5 Functional Heaps and Priority Queues

### 3.5.5.1 Binomial Heap

A binomial heap is a collection of binomial trees supporting O(log n) insertion, minimum, and deletion.

```haskell
-- Binomial heap (simplified)
data BinomialTree a = Node Int a [BinomialTree a]  -- rank, value, children
type BinomialHeap a = [BinomialTree a]

emptyBinHeap :: BinomialHeap a
emptyBinHeap = []

insertBinHeap :: Ord a => a -> BinomialHeap a -> BinomialHeap a
insertBinHeap x = mergeBinHeaps [Node 0 x []]

mergeBinHeaps :: Ord a => BinomialHeap a -> BinomialHeap a -> BinomialHeap a
mergeBinHeaps = undefined  -- See Okasaki for full implementation
```

### 3.5.5.2 Pairing Heap

A pairing heap is a simple, efficient, purely functional heap with good amortized bounds.

```haskell
-- Pairing heap
data PairingHeap a = EmptyPH | NodePH a [PairingHeap a]

emptyPH :: PairingHeap a
emptyPH = EmptyPH

insertPH :: Ord a => a -> PairingHeap a -> PairingHeap a
insertPH x h = mergePH (NodePH x []) h

mergePH :: Ord a => PairingHeap a -> PairingHeap a -> PairingHeap a
mergePH h EmptyPH = h
mergePH EmptyPH h = h
mergePH h1@(NodePH x hs1) h2@(NodePH y hs2)
    | x <= y    = NodePH x (h2:hs1)
    | otherwise = NodePH y (h1:hs2)
```

## 3.5.6 Functional Maps and Sets

### 3.5.6.1 Persistent Map (Association List)

```haskell
-- Association list (simple persistent map)
type AssocList k v = [(k, v)]

insertAssoc :: Eq k => k -> v -> AssocList k v -> AssocList k v
insertAssoc k v xs = (k, v) : filter ((/= k) . fst) xs

lookupAssoc :: Eq k => k -> AssocList k v -> Maybe v
lookupAssoc k = lookup k
```

### 3.5.6.2 Functional Set (as Map)

```haskell
-- Set as map with unit value
type Set a = AssocList a ()

insertSet :: Eq a => a -> Set a -> Set a
insertSet x = insertAssoc x ()

memberSet :: Eq a => a -> Set a -> Bool
memberSet x = any ((== x) . fst)
```

## 3.5.7 Advanced Functional Data Structures

### 3.5.7.1 Catenable Lists

Catenable lists support O(1) concatenation.

```haskell
-- Catenable list (simplified)
data CatList a = E | C a (CatList a) (CatList a)

emptyCat :: CatList a
emptyCat = E

singletonCat :: a -> CatList a
singletonCat x = C x E E

appendCat :: CatList a -> CatList a -> CatList a
appendCat E ys = ys
appendCat xs E = xs
appendCat (C x l r) ys = C x l (appendCat r ys)
```

### 3.5.7.2 Random-Access List

Random-access lists provide O(log n) access and update.

```haskell
-- Random-access list (binary representation)
data RAList a = RANil | RACons a (RAList (a, a))

lookupRA :: Int -> RAList a -> a
lookupRA 0 (RACons x _) = x
lookupRA i (RACons _ xs) = let (q, r) = divMod (i-1) 2 in if r == 0 then fst (lookupRA q xs) else snd (lookupRA q xs)
lookupRA _ RANil = error "out of bounds"
```

## 3.5.8 References

- [3.3 Advanced Data Structures](03-Advanced-Data-Structures.md)
- [3.4 Persistent Data Structures](04-Persistent-Data-Structures.md)
- [4.1 Sorting Algorithms](../04-Algorithms/01-Sorting-Algorithms.md)
- [2.2 Algebraic Data Types](../02-Type-System/02-Algebraic-Data-Types.md)

---

**Next:** [4.1 Sorting Algorithms](../04-Algorithms/01-Sorting-Algorithms.md)
