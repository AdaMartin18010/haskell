# Haskell实现

## 核心特性

### 惰性求值

```haskell
naturals :: [Integer]
naturals = [0..]

take 5 naturals -- [0,1,2,3,4]
```

### 类型系统

```haskell
data Tree a = Empty | Node a (Tree a) (Tree a)

class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
```

## 并发编程

### STM

```haskell
import Control.Concurrent.STM

type Account = TVar Double

transfer :: Account -> Account -> Double -> STM ()
transfer from to amount = do
  fromBalance <- readTVar from
  when (fromBalance >= amount) $ do
    writeTVar from (fromBalance - amount)
    toBalance <- readTVar to
    writeTVar to (toBalance + amount)
```

## 性能优化

### 严格求值

```haskell
{-# LANGUAGE BangPatterns #-}

factorial :: Integer -> Integer
factorial n = go n 1
  where
    go 0 !acc = acc
    go n !acc = go (n - 1) (n * acc)
```

## 测试

### QuickCheck

```haskell
import Test.QuickCheck

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs
```

## 工具

- **GHC**: 编译器
- **Cabal/Stack**: 包管理
- **HLint**: 代码检查

---

**相关链接**：

- [Rust实现](./002-Rust-Implementation.md)
- [Lean实现](./003-Lean-Implementation.md)
