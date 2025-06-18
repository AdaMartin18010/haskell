# 004. 高阶函数 - Higher-Order Functions

## 📋 文档信息

**文档编号**: `haskell/01-Basic-Concepts/004-Higher-Order-Functions.md`  
**创建日期**: 2024年12月  
**最后更新**: 2024年12月  
**文档状态**: 完成  
**质量等级**: A+  

**相关文档**:

- [函数式编程基础](../001-Functional-Programming.md)
- [模式匹配](../002-Pattern-Matching.md)
- [递归与列表](../003-Recursion-and-Lists.md)
- [类型系统基础](../../04-Type-System/001-Type-System-Foundation.md)

---

## 🎯 核心概念

### 1. 高阶函数理论基础

#### 1.1 数学定义

**定义 1.1** (高阶函数): 设 $A, B, C$ 为集合，函数 $f: (A \rightarrow B) \rightarrow C$ 称为高阶函数，其中 $(A \rightarrow B)$ 表示从 $A$ 到 $B$ 的函数集合。

**定义 1.2** (函数组合): 设 $f: B \rightarrow C$ 和 $g: A \rightarrow B$，则函数组合 $f \circ g: A \rightarrow C$ 定义为：
$$(f \circ g)(x) = f(g(x))$$

**定理 1.1** (函数组合结合律): 对于函数 $f: C \rightarrow D$, $g: B \rightarrow C$, $h: A \rightarrow B$：
$$(f \circ g) \circ h = f \circ (g \circ h)$$

**证明**: 对于任意 $x \in A$：
$$((f \circ g) \circ h)(x) = (f \circ g)(h(x)) = f(g(h(x)))$$
$$(f \circ (g \circ h))(x) = f((g \circ h)(x)) = f(g(h(x)))$$

#### 1.2 函数空间

**定义 1.3** (函数空间): 设 $A, B$ 为集合，函数空间 $A \rightarrow B$ 是所有从 $A$ 到 $B$ 的函数的集合。

**定义 1.4** (函数空间上的运算): 在函数空间上可以定义：

- **加法**: $(f + g)(x) = f(x) + g(x)$
- **乘法**: $(f \cdot g)(x) = f(x) \cdot g(x)$
- **标量乘法**: $(c \cdot f)(x) = c \cdot f(x)$

### 2. Haskell中的高阶函数

#### 2.1 函数类型

```haskell
-- 函数类型定义
type Function a b = a -> b
type BinaryOp a = a -> a -> a
type Predicate a = a -> Bool

-- 高阶函数类型
type HigherOrder a b c = (a -> b) -> c
type FunctionComposer a b c = (b -> c) -> (a -> b) -> (a -> c)

-- 示例
main :: IO ()
main = do
    let f :: Int -> Int
        f = (+1)
    let g :: Int -> Int
        g = (*2)
    print $ f 5  -- 6
    print $ g 5  -- 10
```

#### 2.2 函数组合

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g = \x -> f (g x)

-- 函数组合示例
main :: IO ()
main = do
    let f = (+1)
    let g = (*2)
    let h = show
    let composed = h . f . g  -- show . (+1) . (*2)
    
    print $ composed 5  -- "11" (show (f (g 5)) = show (f 10) = show 11)
    print $ (f . g) 5   -- 11
    print $ (g . f) 5   -- 12
```

**定理 2.1** (Haskell函数组合性质): 在Haskell中，函数组合满足：

1. 结合律：$(f \circ g) \circ h = f \circ (g \circ h)$
2. 单位元：$\text{id} \circ f = f \circ \text{id} = f$

### 3. 常用高阶函数

#### 3.1 Map函数

**定义 3.1** (Map函数): 设 $f: A \rightarrow B$，则 $\text{map } f: \text{List}(A) \rightarrow \text{List}(B)$ 定义为：
$$\text{map } f \text{ } l = \begin{cases}
[] & \text{if } l = [] \\
f(x) : \text{map } f \text{ } xs & \text{if } l = x:xs
\end{cases}$$

```haskell
-- Map函数实现
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- Map函数示例
main :: IO ()
main = do
    print $ map (+1) [1,2,3,4,5]           -- [2,3,4,5,6]
    print $ map show [1,2,3]               -- ["1","2","3"]
    print $ map length ["a","bb","ccc"]    -- [1,2,3]
    print $ map (^2) [1..5]                -- [1,4,9,16,25]
```

**定理 3.1** (Map函数性质):
1. $\text{map id} = \text{id}$
2. $\text{map}(f \circ g) = \text{map } f \circ \text{map } g$

**证明**: 对列表进行结构归纳
- 基础情况：$l = []$
  - $\text{map id } [] = [] = \text{id } []$ ✓
  - $\text{map}(f \circ g) [] = [] = \text{map } f (\text{map } g [])$ ✓
- 归纳情况：$l = x:xs$
  - $\text{map id } (x:xs) = x : \text{map id } xs = x:xs$ ✓
  - $\text{map}(f \circ g) (x:xs) = (f \circ g)(x) : \text{map}(f \circ g) xs$
  - $= f(g(x)) : \text{map } f (\text{map } g xs)$ (归纳假设)
  - $= \text{map } f (g(x) : \text{map } g xs) = \text{map } f (\text{map } g (x:xs))$ ✓

#### 3.2 Filter函数

**定义 3.2** (Filter函数): 设 $p: A \rightarrow \text{Bool}$，则 $\text{filter } p: \text{List}(A) \rightarrow \text{List}(A)$ 定义为：
$$\text{filter } p \text{ } l = \begin{cases}
[] & \text{if } l = [] \\
x : \text{filter } p \text{ } xs & \text{if } l = x:xs \text{ and } p(x) \\
\text{filter } p \text{ } xs & \text{if } l = x:xs \text{ and } \neg p(x)
\end{cases}$$

```haskell
-- Filter函数实现
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
    | p x = x : filter p xs
    | otherwise = filter p xs

-- Filter函数示例
main :: IO ()
main = do
    print $ filter even [1..10]            -- [2,4,6,8,10]
    print $ filter (>5) [1..10]            -- [6,7,8,9,10]
    print $ filter (/= ' ') "hello world"  -- "helloworld"
    print $ filter isUpper "Hello World"   -- "HW"
```

**定理 3.2** (Filter函数性质):
1. $\text{filter } \text{const True} = \text{id}$
2. $\text{filter } \text{const False} = \text{const } []$
3. $\text{filter } p \circ \text{filter } q = \text{filter } (p \land q)$

#### 3.3 Fold函数

**定义 3.3** (右折叠): 设 $f: A \times B \rightarrow B$ 和 $e \in B$，则 $\text{foldr } f \text{ } e: \text{List}(A) \rightarrow B$ 定义为：
$$\text{foldr } f \text{ } e \text{ } l = \begin{cases}
e & \text{if } l = [] \\
f(x, \text{foldr } f \text{ } e \text{ } xs) & \text{if } l = x:xs
\end{cases}$$

**定义 3.4** (左折叠): 设 $f: B \times A \rightarrow B$ 和 $e \in B$，则 $\text{foldl } f \text{ } e: \text{List}(A) \rightarrow B$ 定义为：
$$\text{foldl } f \text{ } e \text{ } l = \begin{cases}
e & \text{if } l = [] \\
\text{foldl } f \text{ } (f(e, x)) \text{ } xs & \text{if } l = x:xs
\end{cases}$$

```haskell
-- Fold函数实现
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ acc [] = acc
foldr f acc (x:xs) = f x (foldr f acc xs)

foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ acc [] = acc
foldl f acc (x:xs) = foldl f (f acc x) xs

-- Fold函数示例
main :: IO ()
main = do
    print $ foldr (+) 0 [1..5]             -- 15
    print $ foldl (+) 0 [1..5]             -- 15
    print $ foldr (++) "" ["a","b","c"]    -- "abc"
    print $ foldl (++) "" ["a","b","c"]    -- "abc"
    print $ foldr (:) [] [1,2,3]           -- [1,2,3]
    print $ foldl (flip (:)) [] [1,2,3]    -- [3,2,1]
```

**定理 3.3** (Fold函数性质): 对于可结合的二元运算 $f$：
$$\text{foldl } f \text{ } e = \text{foldr } f \text{ } e$$

### 4. 函数构造器

#### 4.1 部分应用

```haskell
-- 部分应用示例
main :: IO ()
main = do
    let add :: Int -> Int -> Int
        add = (+)

    let addOne :: Int -> Int
        addOne = add 1  -- 部分应用

    let addFive :: Int -> Int
        addFive = add 5  -- 部分应用

    print $ addOne 10   -- 11
    print $ addFive 10  -- 15
    print $ map addOne [1..5]  -- [2,3,4,5,6]
```

#### 4.2 函数柯里化

```haskell
-- 柯里化函数
curry :: ((a, b) -> c) -> a -> b -> c
curry f = \x y -> f (x, y)

uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f = \(x, y) -> f x y

-- 柯里化示例
main :: IO ()
main = do
    let addPair :: (Int, Int) -> Int
        addPair (x, y) = x + y

    let addCurried :: Int -> Int -> Int
        addCurried = curry addPair

    print $ addPair (3, 4)     -- 7
    print $ addCurried 3 4     -- 7
    print $ uncurry (+) (3, 4) -- 7
```

#### 4.3 函数组合器

```haskell
-- 常用函数组合器
id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

flip :: (a -> b -> c) -> b -> a -> c
flip f = \x y -> f y x

($) :: (a -> b) -> a -> b
f $ x = f x

-- 组合器示例
main :: IO ()
main = do
    print $ id 42                    -- 42
    print $ const 42 "hello"         -- 42
    print $ flip (-) 5 10            -- 5 (10 - 5)
    print $ map ($ 3) [(+1), (*2)]   -- [4, 6]
```

### 5. 高级高阶函数模式

#### 5.1 函数映射

```haskell
-- 函数映射
fmap :: Functor f => (a -> b) -> f a -> f b

-- 列表函数映射
mapList :: (a -> b) -> [a] -> [b]
mapList = map

-- Maybe函数映射
mapMaybe :: (a -> b) -> Maybe a -> Maybe b
mapMaybe _ Nothing = Nothing
mapMaybe f (Just x) = Just (f x)

-- 函数映射示例
main :: IO ()
main = do
    print $ mapList (+1) [1,2,3]           -- [2,3,4]
    print $ mapMaybe (+1) (Just 5)         -- Just 6
    print $ mapMaybe (+1) Nothing          -- Nothing
```

#### 5.2 函数应用

```haskell
-- 函数应用
(<*>) :: Applicative f => f (a -> b) -> f a -> f b

-- 列表函数应用
applyList :: [a -> b] -> [a] -> [b]
applyList [] _ = []
applyList _ [] = []
applyList (f:fs) (x:xs) = f x : applyList fs xs

-- 函数应用示例
main :: IO ()
main = do
    let functions = [(+1), (*2), (^2)]
    let values = [1,2,3]
    print $ applyList functions values  -- [2,4,9]
```

#### 5.3 函数绑定

```haskell
-- 函数绑定
(>>=) :: Monad m => m a -> (a -> m b) -> m b

-- Maybe函数绑定
bindMaybe :: Maybe a -> (a -> Maybe b) -> Maybe b
bindMaybe Nothing _ = Nothing
bindMaybe (Just x) f = f x

-- 函数绑定示例
main :: IO ()
main = do
    let safeDiv :: Int -> Int -> Maybe Int
        safeDiv _ 0 = Nothing
        safeDiv x y = Just (x `div` y)

    let safeSqrt :: Int -> Maybe Double
        safeSqrt x = if x >= 0 then Just (sqrt (fromIntegral x)) else Nothing

    print $ Just 16 >>= safeSqrt                    -- Just 4.0
    print $ Just (-1) >>= safeSqrt                  -- Nothing
    print $ Just 10 >>= \x -> safeDiv x 2 >>= safeSqrt  -- Just 2.23606797749979
```

### 6. 函数式编程模式

#### 6.1 函数管道

```haskell
-- 函数管道
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 管道示例
main :: IO ()
main = do
    let result = [1..10]
        |> filter even
        |> map (^2)
        |> sum

    print result  -- 220 (sum of squares of even numbers 1-10)
```

#### 6.2 函数组合链

```haskell
-- 函数组合链
compose :: [a -> a] -> a -> a
compose = foldr (.) id

-- 组合链示例
main :: IO ()
main = do
    let transformations = [filter even, map (^2), take 3]
    let pipeline = compose transformations

    print $ pipeline [1..10]  -- [4,16,36] (first 3 squares of even numbers)
```

#### 6.3 函数缓存

```haskell
-- 函数缓存
memoize :: (Eq a, Show a) => (a -> b) -> a -> b
memoize f = \x -> unsafePerformIO $ do
    cache <- newIORef Map.empty
    cached <- readIORef cache
    case Map.lookup x cached of
        Just result -> return result
        Nothing -> do
            let result = f x
            writeIORef cache (Map.insert x result cached)
            return result

-- 缓存示例
main :: IO ()
main = do
    let expensiveFunction :: Int -> Int
        expensiveFunction n = sum [1..n]

    let cachedFunction = memoize expensiveFunction

    print $ cachedFunction 1000  -- 500500
    print $ cachedFunction 1000  -- 500500 (cached)
```

### 7. 数学函数理论

#### 7.1 函数空间代数

**定义 7.1** (函数空间): 设 $A, B$ 为集合，函数空间 $A \rightarrow B$ 上的运算：
- **加法**: $(f + g)(x) = f(x) + g(x)$
- **乘法**: $(f \cdot g)(x) = f(x) \cdot g(x)$
- **标量乘法**: $(c \cdot f)(x) = c \cdot f(x)$

**定理 7.1** (函数空间性质): 如果 $B$ 是环，则 $A \rightarrow B$ 也是环。

#### 7.2 函数不动点

**定义 7.2** (不动点): 设 $f: A \rightarrow A$，$x \in A$ 是 $f$ 的不动点，如果 $f(x) = x$。

```haskell
-- 不动点计算
fix :: (a -> a) -> a
fix f = let x = f x in x

-- 不动点示例
main :: IO ()
main = do
    let factorial :: (Integer -> Integer) -> Integer -> Integer
        factorial f 0 = 1
        factorial f n = n * f (n - 1)

    let fact = fix factorial

    print $ fact 5  -- 120
```

### 8. 性能分析

#### 8.1 高阶函数复杂度

**定理 8.1** (高阶函数复杂度):
- $\text{map } f \text{ } l$: $O(n)$ 时间，$O(n)$ 空间
- $\text{filter } p \text{ } l$: $O(n)$ 时间，$O(k)$ 空间（$k$ 为满足条件的元素数）
- $\text{foldr } f \text{ } e \text{ } l$: $O(n)$ 时间，$O(n)$ 栈空间
- $\text{foldl } f \text{ } e \text{ } l$: $O(n)$ 时间，$O(1)$ 额外空间

#### 8.2 优化技术

```haskell
-- 融合优化
mapFusion :: (b -> c) -> (a -> b) -> [a] -> [c]
mapFusion f g = map (f . g)

-- 示例
main :: IO ()
main = do
    let f = (+1)
    let g = (*2)

    -- 未优化：两次遍历
    let unoptimized = map f (map g [1..5])

    -- 优化：一次遍历
    let optimized = mapFusion f g [1..5]

    print unoptimized  -- [3,5,7,9,11]
    print optimized    -- [3,5,7,9,11]
```

### 9. 实际应用案例

#### 9.1 数据处理管道

```haskell
-- 数据处理管道
dataProcessing :: [String] -> Int
dataProcessing =
    filter (not . null)           -- 过滤空字符串
    . map read                    -- 转换为数字
    . filter (> 0)               -- 过滤正数
    . map (^2)                   -- 平方
    . take 10                    -- 取前10个
    . sum                        -- 求和

-- 示例
main :: IO ()
main = do
    let data = ["1", "", "2", "3", "0", "4", "5"]
    print $ dataProcessing data  -- 55 (1² + 2² + 3² + 4² + 5²)
```

#### 9.2 函数式配置系统

```haskell
-- 配置系统
type Config = [(String, String)]

-- 配置处理函数
getConfig :: String -> Config -> Maybe String
getConfig key = lookup key

setConfig :: String -> String -> Config -> Config
setConfig key value = (key, value) :)

updateConfig :: String -> (String -> String) -> Config -> Config
updateConfig key f config = case getConfig key config of
    Just value -> setConfig key (f value) config
    Nothing -> config

-- 配置管道
configPipeline :: Config -> Config
configPipeline =
    updateConfig "debug" (const "true")
    . updateConfig "port" (\p -> show (read p + 1000))
    . setConfig "version" "1.0"

-- 示例
main :: IO ()
main = do
    let initialConfig = [("port", "8080"), ("host", "localhost")]
    let finalConfig = configPipeline initialConfig
    print finalConfig  -- [("version","1.0"),("port","9080"),("debug","true"),("port","8080"),("host","localhost")]
```

---

## 📚 参考文献

1. Bird, R. (2015). *Thinking Functionally with Haskell*. Cambridge University Press.
2. Hutton, G. (2016). *Programming in Haskell*. Cambridge University Press.
3. Peyton Jones, S. (2003). *The Implementation of Functional Programming Languages*. Prentice Hall.
4. Wadler, P. (1992). *The Essence of Functional Programming*. POPL '92.

---

## 🔗 相关链接

- [函数式编程基础](../001-Functional-Programming.md)
- [模式匹配](../002-Pattern-Matching.md)
- [递归与列表](../003-Recursion-and-Lists.md)
- [类型系统基础](../../04-Type-System/001-Type-System-Foundation.md)
- [函子与单子](../../04-Type-System/002-Functors-and-Monads.md)
- [函数式设计模式](../../05-Design-Patterns/001-Functional-Design-Patterns.md)
