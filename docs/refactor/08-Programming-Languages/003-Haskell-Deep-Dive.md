# Haskell 深度解析

## 1. 语言概述

Haskell 是一门纯函数式、强类型、惰性求值的编程语言，广泛应用于形式化建模、编译器、金融、并发等领域。

## 2. 语法基础

```haskell
-- 基本类型与函数
double :: Int -> Int
double x = x * 2

-- 模式匹配
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)

-- 列表推导
squares = [x*x | x <- [1..10]]
```

## 3. 类型系统

- 强类型、类型推断、类型类、GADT、数据类型提升
- 类型类示例：
```haskell
class Eq a where
  (==) :: a -> a -> Bool
```
- GADT示例：
```haskell
data Expr a where
  LitInt  :: Int -> Expr Int
  LitBool :: Bool -> Expr Bool
  Add     :: Expr Int -> Expr Int -> Expr Int
```

## 4. Monad与高阶抽象

- Monad定义：
```haskell
class Monad m where
  (>>=)  :: m a -> (a -> m b) -> m b
  return :: a -> m a
```
- IO Monad示例：
```haskell
main = do
  putStrLn "Hello, Haskell!"
  x <- readLn
  print (x * 2)
```
- State Monad示例：
```haskell
import Control.Monad.State
inc :: State Int Int
inc = do
  n <- get
  put (n+1)
  return n
```

## 5. 泛型与高阶类型

- 多态函数：
```haskell
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
```
- 类型提升与DataKinds：
```haskell
{-# LANGUAGE DataKinds, KindSignatures #-}
data Nat = Z | S Nat
data Vec (n :: Nat) a where
  VNil  :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a
```

## 6. 并发与并行

- 轻量线程与STM：
```haskell
import Control.Concurrent
import Control.Concurrent.STM
main = do
  tvar <- newTVarIO 0
  forkIO $ atomically $ modifyTVar' tvar (+1)
  v <- readTVarIO tvar
  print v
```

## 7. 工程实践

- 构建工具：Cabal, Stack
- 包管理：Hackage
- 测试：QuickCheck, HUnit
- 性能优化：Strictness, Profiling

## 8. Haskell与Rust/Lean对比

| 特性      | Haskell         | Rust            | Lean            |
|-----------|-----------------|-----------------|-----------------|
| 纯函数式  | ✅              | 部分支持        | ✅              |
| 类型系统  | 高阶/类型类     | trait/生命周期  | 依赖类型        |
| 并发      | STM/Async       | 线程/消息/async | 任务/并发库     |
| 工程生态  | Hackage/Stack   | Cargo/crates.io | Lake/mathlib    |

## 9. 典型应用
- 编译器、DSL、金融建模、分布式系统、形式化验证

---

**相关链接**：
- [Rust实现](../07-Implementation/002-Rust-Implementation.md)
- [Lean实现](../07-Implementation/003-Lean-Implementation.md)
- [语言比较](./002-Language-Comparison.md)
