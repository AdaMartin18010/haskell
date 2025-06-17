# Haskell 函数组合 (Function Composition)

## 概述

函数组合是函数式编程的核心概念，它体现了数学中函数复合的思想。在Haskell中，函数组合通过 `(.)` 操作符实现，这是范畴论中态射复合的直接体现。

## 数学基础

### 函数复合的数学定义

给定函数 $f: B \rightarrow C$ 和 $g: A \rightarrow B$，它们的复合函数 $f \circ g: A \rightarrow C$ 定义为：

$$(f \circ g)(x) = f(g(x))$$

### 范畴论视角

在范畴论中，函数组合满足以下公理：

1. **结合律**：$(f \circ g) \circ h = f \circ (g \circ h)$
2. **单位元**：$f \circ \text{id} = \text{id} \circ f = f$

其中 $\text{id}$ 是恒等函数。

## Haskell中的函数组合

### 基本语法

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

-- 使用示例
addOne :: Int -> Int
addOne x = x + 1

double :: Int -> Int
double x = x * 2

-- 组合函数：先加倍再加一
addOneAfterDouble :: Int -> Int
addOneAfterDouble = addOne . double

-- 等价于
addOneAfterDouble' x = addOne (double x)
```

### 数学验证

```haskell
-- 验证结合律
associativeLaw :: Int -> Int
associativeLaw = ((+1) . (*2)) . (*3)  -- 左结合
associativeLaw' = (+1) . ((*2) . (*3)) -- 右结合

-- 验证单位元
identityLaw :: Int -> Int
identityLaw = (+1) . id  -- 右单位元
identityLaw' = id . (+1) -- 左单位元
```

## 高级函数组合

### 1. 多函数组合

```haskell
-- 组合多个函数
processNumber :: Int -> String
processNumber = show . (+1) . (*2) . abs

-- 数学表示：$\text{processNumber} = \text{show} \circ (\lambda x. x+1) \circ (\lambda x. 2x) \circ \text{abs}$
```

### 2. 部分应用与组合

```haskell
-- 部分应用函数
add :: Int -> Int -> Int
add x y = x + y

-- 组合部分应用的函数
addFive :: Int -> Int
addFive = add 5

-- 组合链
process :: Int -> String
process = show . addFive . double
```

### 3. 高阶函数组合

```haskell
-- 高阶函数组合
mapAndFilter :: (a -> b) -> (b -> Bool) -> [a] -> [b]
mapAndFilter f p = filter p . map f

-- 使用示例
positiveDoubles :: [Int] -> [Int]
positiveDoubles = mapAndFilter (*2) (>0)
```

## 函数组合的类型系统

### 类型推导

函数组合的类型推导过程：

$$\frac{f: B \rightarrow C \quad g: A \rightarrow B}{f \circ g: A \rightarrow C}$$

在Haskell中：

```haskell
-- 类型推导示例
f :: String -> Int
f = length

g :: Int -> String
g = show

h :: Int -> Int
h = f . g  -- 类型错误！g的输出类型与f的输入类型不匹配

-- 正确的组合
h' :: Int -> Int
h' = g . f  -- 类型正确：Int -> String -> Int
```

### 类型安全的组合

```haskell
-- 类型安全的函数组合
safeCompose :: (b -> c) -> (a -> b) -> a -> c
safeCompose f g = f . g

-- 编译器会检查类型兼容性
```

## 实际应用

### 1. 数据处理管道

```haskell
-- 数据处理管道
dataProcessing :: [String] -> [Int]
dataProcessing = 
    filter (not . null)           -- 过滤空字符串
    . map read                    -- 转换为数字
    . filter (>0)                 -- 过滤正数
    . map (*2)                    -- 加倍
    . map show                    -- 转回字符串
    . map (++ " processed")       -- 添加标记
    . map length                  -- 计算长度

-- 数学表示：$\text{dataProcessing} = \text{length} \circ \text{mark} \circ \text{show} \circ \text{double} \circ \text{filterPositive} \circ \text{read} \circ \text{filterNonEmpty}$
```

### 2. 配置处理

```haskell
-- 配置处理管道
type Config = String

parseConfig :: Config -> Maybe Int
parseConfig = 
    Just . read                   -- 尝试解析
    . filter isDigit             -- 只保留数字
    . dropWhile (== ' ')         -- 删除前导空格

-- 使用Maybe单子的组合
parseConfigSafe :: Config -> Maybe Int
parseConfigSafe = 
    fmap read                     -- 安全地应用read
    . Just . filter isDigit      -- 过滤数字
    . dropWhile (== ' ')         -- 删除空格
```

### 3. 文本处理

```haskell
-- 文本处理管道
textProcessing :: String -> String
textProcessing = 
    map toUpper                   -- 转大写
    . filter (/= ' ')            -- 删除空格
    . reverse                     -- 反转
    . take 10                     -- 取前10个字符
    . dropWhile (== ' ')         -- 删除前导空格

-- 数学表示：$\text{textProcessing} = \text{take10} \circ \text{reverse} \circ \text{filterSpace} \circ \text{toUpper}$
```

## 函数组合的优化

### 1. 融合优化

```haskell
-- 编译器可以融合多个map操作
optimizedMap :: [Int] -> [Int]
optimizedMap = map (+1) . map (*2) . map (^2)

-- 等价于（编译器优化后）
optimizedMap' :: [Int] -> [Int]
optimizedMap' = map (\x -> (x^2 * 2) + 1)
```

### 2. 惰性求值

```haskell
-- 惰性求值允许无限列表处理
infiniteProcessing :: [Int] -> [Int]
infiniteProcessing = 
    map (*2)                      -- 无限列表
    . filter even                 -- 惰性过滤
    . take 10                     -- 只取前10个

-- 可以处理无限列表
result = infiniteProcessing [1..]  -- 不会无限循环
```

## 函数组合的范畴论基础

### 1. 函子组合

```haskell
-- 函子组合
composeFunctors :: (Functor f, Functor g) => f (g a) -> f (g b)
composeFunctors = fmap (fmap (+1))

-- 数学表示：$F \circ G$ 的函子组合
```

### 2. 单子组合

```haskell
-- 单子组合（通过单子变换器）
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Functor f, Functor g) => Functor (Compose f g) where
    fmap f (Compose x) = Compose (fmap (fmap f) x)

-- 数学表示：单子的复合结构
```

## 高级技巧

### 1. 反向组合

```haskell
-- 反向组合操作符
(>>>) :: (a -> b) -> (b -> c) -> a -> c
f >>> g = g . f

-- 使用示例
reversePipeline :: Int -> String
reversePipeline = 
    (*2) >>> (+1) >>> show >>> reverse
```

### 2. 条件组合

```haskell
-- 条件组合
conditionalCompose :: Bool -> (a -> b) -> (a -> b) -> a -> b
conditionalCompose p f g = if p then f else g

-- 使用示例
smartProcessing :: Int -> String
smartProcessing = 
    conditionalCompose (>0) 
        (show . (*2))           -- 正数加倍
        (show . abs)            -- 负数取绝对值
```

### 3. 错误处理组合

```haskell
-- 错误处理组合
safeCompose :: (a -> Maybe b) -> (b -> Maybe c) -> a -> Maybe c
safeCompose f g = f >=> g

-- 使用示例
safeProcessing :: String -> Maybe Int
safeProcessing = 
    safeCompose readMaybe        -- 安全解析
        (safeCompose Just        -- 包装为Maybe
            (\x -> if x > 0 then Just x else Nothing))  -- 验证正数
```

## 性能考虑

### 1. 组合vs嵌套

```haskell
-- 函数组合（推荐）
efficient :: [Int] -> [Int]
efficient = map (+1) . filter (>0) . map (*2)

-- 嵌套函数（不推荐）
inefficient :: [Int] -> [Int]
inefficient xs = map (+1) (filter (>0) (map (*2) xs))
```

### 2. 内存使用

```haskell
-- 流式处理（内存友好）
streamProcessing :: [Int] -> [Int]
streamProcessing = 
    map (+1) . filter (>0) . map (*2)

-- 中间结果（内存消耗大）
listProcessing :: [Int] -> [Int]
listProcessing xs = 
    let doubled = map (*2) xs
        filtered = filter (>0) doubled
    in map (+1) filtered
```

## 总结

函数组合是Haskell函数式编程的核心概念，它：

1. **体现数学基础**：直接对应数学中的函数复合
2. **提供类型安全**：编译时检查类型兼容性
3. **支持高阶抽象**：可以组合任意函数
4. **优化性能**：编译器可以进行融合优化
5. **提高可读性**：管道式的数据处理

函数组合体现了函数式编程的数学本质，将复杂的计算分解为简单的函数组合，使得代码既简洁又具有强大的表达能力。

---

**相关主题**：
- [高阶函数](03-Higher-Order-Functions.md)
- [函数式编程基础](../01-Basic-Concepts/函数式编程基础.md)
- [类型系统](../04-Type-System/类型基础.md)
- [单子理论](../04-Type-System/高级类型.md) 