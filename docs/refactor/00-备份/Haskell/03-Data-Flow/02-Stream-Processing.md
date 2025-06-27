# 流处理 (Stream Processing)

## 概述

流处理是Haskell中处理无限数据序列的核心技术，基于惰性求值和函数式编程实现高效的流式数据处理。本文档系统性介绍Haskell流处理的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [流数据类型](#流数据类型)
3. [流操作](#流操作)
4. [无限流](#无限流)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 2.1: 流 (Stream)

流是无限的数据序列，在Haskell中通过惰性求值实现。

### 定义 2.2: 流处理 (Stream Processing)

流处理是对流数据进行变换、过滤和聚合的操作。

### 流的数学定义

流可以表示为函数：
$$S : \mathbb{N} \rightarrow A$$

其中 $S(n)$ 表示流的第 $n$ 个元素。

## 流数据类型

### 基本流类型

```haskell
-- 基本流类型
data Stream a = Cons a (Stream a)

-- 流构造函数
stream :: a -> Stream a -> Stream a
stream = Cons

-- 流头部
head' :: Stream a -> a
head' (Cons x _) = x

-- 流尾部
tail' :: Stream a -> Stream a
tail' (Cons _ xs) = xs
```

### 列表作为流

在Haskell中，列表天然支持流处理：

```haskell
-- 无限列表
infiniteList :: [Integer]
infiniteList = [1..]

-- 惰性求值
take 10 infiniteList  -- 只计算前10个元素
```

## 流操作

### 基本流操作

```haskell
-- 流映射
mapStream :: (a -> b) -> Stream a -> Stream b
mapStream f (Cons x xs) = Cons (f x) (mapStream f xs)

-- 流过滤
filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream pred (Cons x xs)
  | pred x = Cons x (filterStream pred xs)
  | otherwise = filterStream pred xs

-- 流折叠
foldrStream :: (a -> b -> b) -> b -> Stream a -> b
foldrStream f z (Cons x xs) = f x (foldrStream f z xs)
```

### 高级流操作

```haskell
-- 流组合
zipWithStream :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithStream f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWithStream f xs ys)

-- 流扫描
scanlStream :: (b -> a -> b) -> b -> Stream a -> Stream b
scanlStream f z (Cons x xs) = Cons z (scanlStream f (f z x) xs)

-- 流分组
groupStream :: Eq a => Stream a -> Stream [a]
groupStream (Cons x xs) = Cons (x : takeWhile (== x) xs) 
                               (groupStream (dropWhile (== x) xs))
```

## 无限流

### 无限流构造

```haskell
-- 常数流
constantStream :: a -> Stream a
constantStream x = Cons x (constantStream x)

-- 自然数流
naturals :: Stream Integer
naturals = go 0
  where go n = Cons n (go (n + 1))

-- 斐波那契流
fibonacciStream :: Stream Integer
fibonacciStream = Cons 0 (Cons 1 (zipWithStream (+) fibonacciStream (tail' fibonacciStream)))

-- 素数流
primes :: Stream Integer
primes = sieve (Cons 2 (mapStream (+1) naturals))
  where
    sieve (Cons p xs) = Cons p (sieve (filterStream (\x -> x `mod` p /= 0) xs))
```

### 流变换

```haskell
-- 流变换器
data StreamT m a = StreamT { runStreamT :: m (Maybe (a, StreamT m a)) }

-- 流变换器实例
instance Monad m => Monad (StreamT m) where
  return x = StreamT $ return (Just (x, StreamT $ return Nothing))
  StreamT m >>= f = StreamT $ do
    result <- m
    case result of
      Nothing -> return Nothing
      Just (x, xs) -> runStreamT (f x >>= \y -> StreamT $ return (Just (y, xs >>= f)))
```

## Haskell实现

### 综合示例

```haskell
-- 流处理模块
module StreamProcessing where

-- 基本流类型
data Stream a = Cons a (Stream a)

-- 流操作
head' :: Stream a -> a
head' (Cons x _) = x

tail' :: Stream a -> Stream a
tail' (Cons _ xs) = xs

-- 流映射
mapStream :: (a -> b) -> Stream a -> Stream b
mapStream f (Cons x xs) = Cons (f x) (mapStream f xs)

-- 流过滤
filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream pred (Cons x xs)
  | pred x = Cons x (filterStream pred xs)
  | otherwise = filterStream pred xs

-- 无限流
naturals :: Stream Integer
naturals = go 0
  where go n = Cons n (go (n + 1))

-- 斐波那契流
fibonacciStream :: Stream Integer
fibonacciStream = Cons 0 (Cons 1 (zipWithStream (+) fibonacciStream (tail' fibonacciStream)))

-- 流组合
zipWithStream :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithStream f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWithStream f xs ys)

-- 流到列表转换
streamToList :: Stream a -> [a]
streamToList (Cons x xs) = x : streamToList xs

-- 列表到流转换
listToStream :: [a] -> Stream a
listToStream [] = error "Cannot convert empty list to infinite stream"
listToStream (x:xs) = Cons x (listToStream xs)

-- 流处理示例
streamExample :: IO ()
streamExample = do
  -- 处理自然数流
  let evenNaturals = filterStream even naturals
  let doubledEvens = mapStream (*2) evenNaturals
  let firstTen = take 10 (streamToList doubledEvens)
  
  putStrLn $ "First 10 doubled even numbers: " ++ show firstTen
  
  -- 处理斐波那契流
  let firstTenFib = take 10 (streamToList fibonacciStream)
  putStrLn $ "First 10 Fibonacci numbers: " ++ show firstTenFib
```

### 实际应用示例

```haskell
-- 传感器数据处理
data SensorData = SensorData
  { sensorId :: Int
  , sensorValue :: Double
  , sensorTimestamp :: Integer
  }

-- 传感器数据流
sensorDataStream :: Stream SensorData
sensorDataStream = go 0
  where
    go n = Cons (SensorData n (fromIntegral n) n) (go (n + 1))

-- 传感器数据处理
processSensorData :: Stream SensorData -> Stream Double
processSensorData = 
  mapStream sensorValue .           -- 提取数值
  filterStream (\s -> sensorValue s > 0) .  -- 过滤有效数据
  mapStream (* 100)                 -- 放大100倍

-- 事件流处理
data Event = Event
  { eventId :: Int
  , eventType :: String
  , eventData :: String
  }

-- 事件流
eventStream :: Stream Event
eventStream = go 0
  where
    go n = Cons (Event n "data" ("event" ++ show n)) (go (n + 1))

-- 事件处理
processEvents :: Stream Event -> Stream String
processEvents = 
  filterStream (\e -> eventType e == "important") .  -- 过滤重要事件
  mapStream eventData .                              -- 提取数据
  mapStream (take 50)                                -- 限制长度
```

## 最佳实践

1. **利用惰性求值**: 避免过早计算，提高效率。
2. **使用高阶函数**: 如map、filter、fold等处理流数据。
3. **合理使用无限流**: 利用惰性求值处理大数据集。
4. **避免副作用**: 保持流处理的纯函数特性。
5. **组合流操作**: 通过函数组合构建复杂流处理管道。

## 相关链接

- [数据流编程](./01-Data-Flow-Programming.md)
- [管道操作](./03-Pipeline-Operations.md)
- [控制流](../02-Control-Flow/README.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
