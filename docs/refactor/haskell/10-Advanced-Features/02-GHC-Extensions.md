# Haskell GHC扩展

## 概述

GHC（Glasgow Haskell Compiler）提供了丰富的语言扩展，这些扩展大大增强了Haskell的表达能力和类型系统。本文档详细介绍最常用和最重要的GHC扩展。

## 1. 类型系统扩展

### 1.1 多参数类型类

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- 多参数类型类
class Collection c e where
    empty :: c e
    insert :: e -> c e -> c e
    member :: e -> c e -> Bool

-- 实例实现
instance Collection [] a where
    empty = []
    insert x xs = x : xs
    member x xs = x `elem` xs

instance Collection Set a where
    empty = Set.empty
    insert x s = Set.insert x s
    member x s = Set.member x s
```

### 1.2 函数依赖

```haskell
{-# LANGUAGE FunctionalDependencies #-}

-- 函数依赖：类型参数之间的依赖关系
class MultiMap k v | k -> v where
    lookup :: k -> MultiMap k v -> Maybe v
    insert :: k -> v -> MultiMap k v -> MultiMap k v

-- 实例
instance MultiMap String Int where
    lookup key map = -- 实现
    insert key value map = -- 实现
```

### 1.3 类型族

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- 类型族
type family ElementType c where
    ElementType [a] = a
    ElementType (Set a) = a
    ElementType (Map k v) = (k, v)

-- 关联类型族
class Collection c where
    type Elem c
    empty :: c
    insert :: Elem c -> c -> c

instance Collection [a] where
    type Elem [a] = a
    empty = []
    insert x xs = x : xs
```

## 2. 高级类型特性

### 2.1 GADTs（广义代数数据类型）

```haskell
{-# LANGUAGE GADTs #-}

-- 广义代数数据类型
data Expr a where
    LitInt :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add :: Expr Int -> Expr Int -> Expr Int
    If :: Expr Bool -> Expr a -> Expr a -> Expr a

-- 类型安全的求值
eval :: Expr a -> a
eval (LitInt n) = n
eval (LitBool b) = b
eval (Add e1 e2) = eval e1 + eval e2
eval (If cond e1 e2) = if eval cond then eval e1 else eval e2
```

### 2.2 存在类型

```haskell
{-# LANGUAGE ExistentialQuantification #-}

-- 存在类型
data Showable = forall a. Show a => Showable a

-- 使用存在类型
showableList :: [Showable]
showableList = [Showable 42, Showable "hello", Showable True]

showAll :: [Showable] -> [String]
showAll = map (\(Showable x) -> show x)
```

### 2.3 类型应用

```haskell
{-# LANGUAGE TypeApplications #-}

-- 类型应用
id @Int 42 :: Int
id @String "hello" :: String

-- 多态函数
const @Int @String 42 "hello" :: Int

-- 类型推断
read @Int "123" :: Int
```

## 3. 高级模式匹配

### 3.1 模式同义词

```haskell
{-# LANGUAGE PatternSynonyms #-}

-- 模式同义词
pattern Empty <- []
pattern Cons x xs <- (x:xs)
pattern Single x <- [x]

-- 双向模式同义词
pattern Nil = []
pattern (:<) x xs = x : xs

-- 使用模式同义词
isEmpty :: [a] -> Bool
isEmpty Empty = True
isEmpty _ = False

head' :: [a] -> Maybe a
head' (x :< _) = Just x
head' _ = Nothing
```

### 3.2 ViewPatterns

```haskell
{-# LANGUAGE ViewPatterns #-}

-- ViewPatterns
f :: [Int] -> String
f (length -> 0) = "empty"
f (length -> n) | n > 10 = "long"
f (take 3 -> [1,2,3]) = "starts with 1,2,3"
f _ = "other"

-- 自定义视图函数
view :: [a] -> (Int, [a])
view xs = (length xs, xs)

g :: [Int] -> String
g (view -> (len, xs)) = "length: " ++ show len
```

## 4. 高级函数特性

### 4.1 RankNTypes

```haskell
{-# LANGUAGE RankNTypes #-}

-- Rank-2类型
type Rank2 = (forall a. a -> a) -> Int

-- 高阶多态
applyToInt :: (forall a. Num a => a -> a) -> Int -> Int
applyToInt f x = f x

-- 存在类型编码
type Exists f = forall r. (forall a. f a -> r) -> r

-- 使用RankNTypes
runExists :: Exists [] -> [Int]
runExists e = e (\xs -> [length xs])
```

### 4.2 ImpredicativeTypes

```haskell
{-# LANGUAGE ImpredicativeTypes #-}

-- 非谓词类型
type Impredicative = [forall a. a -> a]

-- 函数列表
idList :: [forall a. a -> a]
idList = [id, id, id]

-- 应用非谓词类型
applyAll :: [forall a. a -> a] -> Int -> [Int]
applyAll fs x = map (\f -> f x) fs
```

## 5. 并发和并行

### 5.1 ParallelListComp

```haskell
{-# LANGUAGE ParallelListComp #-}

-- 并行列表推导
parallelList :: [(Int, String)]
parallelList = [(x, y) | x <- [1..3] | y <- ["a", "b", "c"]]

-- 多生成器并行
parallelMultiple :: [Int]
parallelMultiple = [x + y | x <- [1..3] | y <- [10, 20, 30] | z <- [100, 200, 300]]
```

### 5.2 TransformListComp

```haskell
{-# LANGUAGE TransformListComp #-}

-- 转换列表推导
transformList :: [Int]
transformList = [x | x <- [1..10], then take 5, then sort]

-- 分组和聚合
groupedList :: [(Int, [Int])]
groupedList = [the x | x <- [1,1,2,2,3], then group by x using groupWith]
```

## 6. 模板Haskell扩展

### 6.1 TemplateHaskell

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

-- 模板Haskell
generateType :: Q [Dec]
generateType = [d|
    data GeneratedType = Constructor1 | Constructor2
    deriving Show
  |]

-- 使用模板Haskell
$(generateType)
```

### 6.2 QuasiQuotes

```haskell
{-# LANGUAGE QuasiQuotes #-}

-- 自定义QuasiQuoter
import Language.Haskell.TH.Quote

-- 字符串QuasiQuoter
str :: QuasiQuoter
str = QuasiQuoter { quoteExp = \s -> [| s |] }

-- 使用QuasiQuotes
example :: String
example = [str|Hello, World!|]
```

## 7. 高级类型系统

### 7.1 TypeOperators

```haskell
{-# LANGUAGE TypeOperators #-}

-- 类型操作符
type a :+: b = Either a b
type a :*: b = (a, b)

-- 使用类型操作符
type Complex = Int :*: Int
type Result = String :+: Int
```

### 7.2 ConstraintKinds

```haskell
{-# LANGUAGE ConstraintKinds #-}

-- 约束类型
type Numeric a = (Num a, Ord a)

-- 约束族
type family ConstraintFor a :: Constraint where
    ConstraintFor Int = (Num Int, Ord Int)
    ConstraintFor String = (Show String, Eq String)

-- 使用约束
f :: ConstraintFor a => a -> a
f x = x
```

### 7.3 DataKinds

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

-- 提升数据类型
data Nat = Zero | Succ Nat

-- 类型级自然数
type family Add (n :: Nat) (m :: Nat) :: Nat where
    Add Zero m = m
    Add (Succ n) m = Succ (Add n m)

-- 向量类型
data Vec (n :: Nat) a where
    Nil :: Vec Zero a
    Cons :: a -> Vec n a -> Vec (Succ n) a
```

## 8. 高级模式匹配

### 8.1 OverloadedStrings

```haskell
{-# LANGUAGE OverloadedStrings #-}

-- 重载字符串
import Data.Text (Text)

-- 字符串字面量
textExample :: Text
textExample = "This is a Text value"

-- 字节串字面量
import Data.ByteString (ByteString)

byteStringExample :: ByteString
byteStringExample = "This is a ByteString"
```

### 8.2 OverloadedLists

```haskell
{-# LANGUAGE OverloadedLists #-}

-- 重载列表
import Data.Set (Set)

-- 集合字面量
setExample :: Set Int
setExample = [1, 2, 3, 4, 5]

-- 映射字面量
import Data.Map (Map)

mapExample :: Map String Int
mapExample = [("a", 1), ("b", 2), ("c", 3)]
```

## 9. 高级函数特性

### 9.1 RecursiveDo

```haskell
{-# LANGUAGE RecursiveDo #-}

-- 递归do表达式
import Control.Monad.Fix

recursiveExample :: IO ()
recursiveExample = mdo
    x <- getLine
    y <- if x == "quit" then return "goodbye" else getLine
    putStrLn y
    when (y /= "goodbye") recursiveExample
```

### 9.2 Arrows

```haskell
{-# LANGUAGE Arrows #-}

-- 箭头语法
import Control.Arrow

arrowExample :: Arrow a => a Int Int
arrowExample = proc x -> do
    y <- (+1) -< x
    z <- (*2) -< y
    returnA -< z
```

## 10. 实际应用示例

### 10.1 类型安全的状态机

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- 状态类型
data State = Idle | Running | Finished

-- 状态机
data StateMachine (s :: State) where
    IdleState :: StateMachine Idle
    RunningState :: Int -> StateMachine Running
    FinishedState :: String -> StateMachine Finished

-- 状态转换
start :: StateMachine Idle -> StateMachine Running
start IdleState = RunningState 0

step :: StateMachine Running -> StateMachine Running
step (RunningState n) = RunningState (n + 1)

finish :: StateMachine Running -> StateMachine Finished
finish (RunningState n) = FinishedState (show n)
```

### 10.2 类型安全的向量

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- 向量类型
data Vec (n :: Nat) a where
    VNil :: Vec Zero a
    VCons :: a -> Vec n a -> Vec (Succ n) a

-- 向量操作
vhead :: Vec (Succ n) a -> a
vhead (VCons x _) = x

vtail :: Vec (Succ n) a -> Vec n a
vtail (VCons _ xs) = xs

-- 类型安全的索引
type family Index (n :: Nat) (m :: Nat) :: Bool where
    Index Zero m = False
    Index (Succ n) Zero = True
    Index (Succ n) (Succ m) = Index n m

vindex :: (Index n m ~ True) => Vec n a -> Proxy m -> a
vindex (VCons x _) Proxy = x
vindex (VCons _ xs) (Proxy :: Proxy (Succ m)) = vindex xs (Proxy :: Proxy m)
```

## 11. 性能优化扩展

### 11.1 BangPatterns

```haskell
{-# LANGUAGE BangPatterns #-}

-- 严格模式
strictFunction :: Int -> Int
strictFunction !n = n * 2

-- 严格字段
data StrictRecord = StrictRecord !Int !String

-- 严格列表处理
strictSum :: [Int] -> Int
strictSum = go 0
  where
    go !acc [] = acc
    go !acc (x:xs) = go (acc + x) xs
```

### 11.2 UnboxedTypes

```haskell
{-# LANGUAGE UnboxedTypes #-}

-- 未装箱类型
import GHC.Prim

-- 未装箱整数
unboxedInt :: Int#
unboxedInt = 42#

-- 未装箱元组
unboxedTuple :: (# Int#, Double# #)
unboxedTuple = (# 1#, 2.0# #)
```

## 总结

GHC扩展大大增强了Haskell的表达能力，主要包括：

1. **类型系统扩展**：多参数类型类、函数依赖、类型族
2. **高级类型特性**：GADTs、存在类型、类型应用
3. **高级模式匹配**：模式同义词、ViewPatterns
4. **高级函数特性**：RankNTypes、ImpredicativeTypes
5. **并发和并行**：ParallelListComp、TransformListComp
6. **模板Haskell**：TemplateHaskell、QuasiQuotes
7. **高级类型系统**：TypeOperators、ConstraintKinds、DataKinds
8. **性能优化**：BangPatterns、UnboxedTypes

这些扩展使Haskell成为一个更加强大和灵活的编程语言。

## 相关链接

- [模板Haskell](01-Template-Haskell.md)
- [高级类型](../04-Type-System/高级类型.md)
- [性能优化](03-Performance-Optimization.md)
- [并发编程](04-Concurrent-Programming.md)

---

**最后更新**: 2024年12月  
**版本**: 1.0.0
