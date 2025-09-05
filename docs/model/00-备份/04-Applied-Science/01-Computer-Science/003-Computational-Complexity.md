# 003-计算复杂性理论

## 1. 概述

### 1.1 定义与目标

计算复杂性理论是研究算法资源消耗的理论分支，主要关注：

- **时间复杂度**: 算法执行所需的时间
- **空间复杂度**: 算法执行所需的存储空间
- **复杂度类**: 具有相似复杂度特征的算法集合

### 1.2 形式化定义

对于算法 $A$ 和输入 $x$，我们定义：

**时间复杂度**:
$$T_A(x) = \text{算法 } A \text{ 在输入 } x \text{ 上的执行步数}$$

**空间复杂度**:
$$S_A(x) = \text{算法 } A \text{ 在输入 } x \text{ 上的最大存储使用量}$$

## 2. 渐进分析

### 2.1 大O记号

**定义**: 对于函数 $f(n)$ 和 $g(n)$，我们说 $f(n) = O(g(n))$ 当且仅当存在常数 $c > 0$ 和 $n_0$，使得对于所有 $n \geq n_0$：
$$f(n) \leq c \cdot g(n)$$

### 2.2 常见复杂度类

| 复杂度类 | 数学表示 | 描述 | 示例 |
|---------|---------|------|------|
| 常数时间 | $O(1)$ | 执行时间与输入大小无关 | 数组访问 |
| 对数时间 | $O(\log n)$ | 执行时间随输入大小对数增长 | 二分查找 |
| 线性时间 | $O(n)$ | 执行时间与输入大小成正比 | 线性搜索 |
| 线性对数时间 | $O(n \log n)$ | 执行时间介于线性和平方之间 | 归并排序 |
| 平方时间 | $O(n^2)$ | 执行时间与输入大小的平方成正比 | 冒泡排序 |
| 指数时间 | $O(2^n)$ | 执行时间随输入大小指数增长 | 穷举搜索 |

## 3. 复杂度类理论

### 3.1 P类问题

**定义**: P类包含所有可以在多项式时间内解决的问题：
$$\text{P} = \{L : \exists \text{ 算法 } A, \forall x, T_A(x) = O(|x|^k) \text{ 对于某个常数 } k\}$$

### 3.2 NP类问题

**定义**: NP类包含所有可以在多项式时间内验证解的问题：
$$\text{NP} = \{L : \exists \text{ 验证算法 } V, \forall x \in L, \exists w, V(x,w) = 1 \text{ 且 } T_V(x,w) = O(|x|^k)\}$$

### 3.3 NP完全问题

**定义**: 问题 $L$ 是NP完全的，当且仅当：

1. $L \in \text{NP}$
2. 对于所有 $L' \in \text{NP}$，$L' \leq_p L$（多项式时间归约）

## 4. Haskell实现示例

### 4.1 复杂度分析工具

```haskell
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- 复杂度分析类型类
class ComplexityAnalysis a where
    type TimeComplexity a :: *
    type SpaceComplexity a :: *
    
    -- 分析算法复杂度
    analyzeComplexity :: a -> (TimeComplexity a, SpaceComplexity a)
    
    -- 获取渐进复杂度
    getAsymptoticComplexity :: a -> String

-- 算法复杂度数据类型
data Complexity = 
    O1 | OLogN | ON | ONLogN | ON2 | ON3 | O2N | ONFactorial
    deriving (Show, Eq, Ord)

-- 复杂度比较
compareComplexity :: Complexity -> Complexity -> Ordering
compareComplexity O1 O1 = EQ
compareComplexity O1 _ = LT
compareComplexity OLogN O1 = GT
compareComplexity OLogN OLogN = EQ
compareComplexity OLogN (ON) = LT
compareComplexity OLogN _ = LT
compareComplexity ON O1 = GT
compareComplexity ON OLogN = GT
compareComplexity ON ON = EQ
compareComplexity ON ONLogN = LT
compareComplexity ON _ = LT
compareComplexity ONLogN O1 = GT
compareComplexity ONLogN OLogN = GT
compareComplexity ONLogN ON = GT
compareComplexity ONLogN ONLogN = EQ
compareComplexity ONLogN ON2 = LT
compareComplexity ONLogN _ = LT
compareComplexity ON2 O1 = GT
compareComplexity ON2 OLogN = GT
compareComplexity ON2 ON = GT
compareComplexity ON2 ONLogN = GT
compareComplexity ON2 ON2 = EQ
compareComplexity ON2 ON3 = LT
compareComplexity ON2 _ = LT
compareComplexity ON3 O1 = GT
compareComplexity ON3 OLogN = GT
compareComplexity ON3 ON = GT
compareComplexity ON3 ONLogN = GT
compareComplexity ON3 ON2 = GT
compareComplexity ON3 ON3 = EQ
compareComplexity ON3 O2N = LT
compareComplexity ON3 _ = LT
compareComplexity O2N O1 = GT
compareComplexity O2N OLogN = GT
compareComplexity O2N ON = GT
compareComplexity O2N ONLogN = GT
compareComplexity O2N ON2 = GT
compareComplexity O2N ON3 = GT
compareComplexity O2N O2N = EQ
compareComplexity O2N ONFactorial = LT
compareComplexity ONFactorial _ = GT
```

### 4.2 算法复杂度分析

```haskell
-- 算法分析实例
data Algorithm = 
    LinearSearch | BinarySearch | BubbleSort | MergeSort | QuickSort
    deriving (Show, Eq)

instance ComplexityAnalysis Algorithm where
    type TimeComplexity Algorithm = Complexity
    type SpaceComplexity Algorithm = Complexity
    
    analyzeComplexity LinearSearch = (ON, O1)
    analyzeComplexity BinarySearch = (OLogN, O1)
    analyzeComplexity BubbleSort = (ON2, O1)
    analyzeComplexity MergeSort = (ONLogN, ON)
    analyzeComplexity QuickSort = (ONLogN, OLogN)
    
    getAsymptoticComplexity alg = case alg of
        LinearSearch -> "O(n)"
        BinarySearch -> "O(log n)"
        BubbleSort -> "O(n²)"
        MergeSort -> "O(n log n)"
        QuickSort -> "O(n log n)"

-- 复杂度分析示例
complexityExamples :: IO ()
complexityExamples = do
    putStrLn "=== 算法复杂度分析 ==="
    mapM_ (\alg -> do
        let (time, space) = analyzeComplexity alg
        putStrLn $ show alg ++ ":"
        putStrLn $ "  时间复杂度: " ++ show time
        putStrLn $ "  空间复杂度: " ++ show space
        putStrLn $ "  渐进表示: " ++ getAsymptoticComplexity alg
        putStrLn ""
        ) [LinearSearch, BinarySearch, BubbleSort, MergeSort, QuickSort]
```

### 4.3 多项式时间归约

```haskell
-- 归约关系
data Reduction = 
    PolynomialReduction | LinearReduction | LogarithmicReduction
    deriving (Show, Eq)

-- 问题归约
class ProblemReduction a b where
    -- 将问题a归约到问题b
    reduce :: a -> b
    
    -- 归约的复杂度
    reductionComplexity :: Reduction

-- 3-SAT到独立集问题的归约
data ThreeSAT = ThreeSAT [Clause]
data Clause = Clause [Literal]
data Literal = Positive String | Negative String

data IndependentSet = IndependentSet Graph Int
data Graph = Graph [(Int, Int)] -- 边列表

instance ProblemReduction ThreeSAT IndependentSet where
    reduce (ThreeSAT clauses) = IndependentSet (constructGraph clauses) (length clauses)
        where
            constructGraph :: [Clause] -> Graph
            constructGraph cs = Graph $ concatMap clauseToEdges (zip [0..] cs)
            
            clauseToEdges :: (Int, Clause) -> [(Int, Int)]
            clauseToEdges (i, Clause literals) = 
                [(i, j) | j <- [0..length literals - 1], j /= i]
    
    reductionComplexity = PolynomialReduction
```

## 5. 高级复杂度理论

### 5.1 空间复杂度类

**PSPACE类**:
$$\text{PSPACE} = \{L : \exists \text{ 算法 } A, \forall x, S_A(x) = O(|x|^k) \text{ 对于某个常数 } k\}$$

**L类** (对数空间):
$$\text{L} = \{L : \exists \text{ 算法 } A, \forall x, S_A(x) = O(\log |x|)\}$$

### 5.2 随机化复杂度类

**BPP类** (有界错误概率多项式时间):
$$\text{BPP} = \{L : \exists \text{ 随机算法 } A, \forall x, \Pr[A(x) = L(x)] \geq \frac{2}{3}\}$$

**RP类** (随机多项式时间):
$$\text{RP} = \{L : \exists \text{ 随机算法 } A, \forall x \in L, \Pr[A(x) = 1] \geq \frac{1}{2}\}$$

### 5.3 量子复杂度类

**BQP类** (有界错误量子多项式时间):
$$\text{BQP} = \{L : \exists \text{ 量子算法 } A, \forall x, \Pr[A(x) = L(x)] \geq \frac{2}{3}\}$$

## 6. 实际应用

### 6.1 算法选择策略

```haskell
-- 算法选择器
data AlgorithmSelector = AlgorithmSelector {
    inputSize :: Int,
    timeConstraint :: Maybe Double,
    spaceConstraint :: Maybe Int,
    inputType :: InputType
}

data InputType = 
    Sorted | Unsorted | NearlySorted | Random | Structured
    deriving (Show, Eq)

-- 基于约束选择最优算法
selectOptimalAlgorithm :: AlgorithmSelector -> Algorithm
selectOptimalAlgorithm selector
    | inputSize selector < 50 = BubbleSort  -- 小数据集
    | inputType selector == Sorted = MergeSort  -- 已排序数据
    | inputType selector == NearlySorted = QuickSort  -- 接近排序
    | maybe True (inputSize selector <) (timeConstraint selector) = MergeSort
    | maybe True (inputSize selector <) (spaceConstraint selector) = QuickSort
    | otherwise = MergeSort

-- 算法性能预测
predictPerformance :: Algorithm -> Int -> (Double, Int)
predictPerformance alg n = case alg of
    LinearSearch -> (fromIntegral n, 1)
    BinarySearch -> (logBase 2 (fromIntegral n), 1)
    BubbleSort -> (fromIntegral (n^2), 1)
    MergeSort -> (fromIntegral n * logBase 2 (fromIntegral n), n)
    QuickSort -> (fromIntegral n * logBase 2 (fromIntegral n), logBase 2 (fromIntegral n))
```

### 6.2 复杂度优化技术

```haskell
-- 记忆化技术
class Memoizable a where
    type MemoKey a :: *
    type MemoValue a :: *
    
    memoize :: (MemoKey a -> MemoValue a) -> MemoKey a -> MemoValue a

-- 动态规划实现
data DynamicProgramming = DynamicProgramming {
    subproblems :: Map String Int,
    optimalSubstructure :: Bool
}

-- 分治策略
data DivideAndConquer = DivideAndConquer {
    divideStep :: Int -> [Int],
    conquerStep :: [Int] -> Int,
    combineStep :: [Int] -> Int
}

-- 贪心策略
data GreedyStrategy = GreedyStrategy {
    selectionFunction :: [Int] -> Int,
    feasibilityCheck :: [Int] -> Bool,
    objectiveFunction :: [Int] -> Int
}
```

## 7. 复杂度证明技术

### 7.1 下界证明

**信息论下界**:
对于比较排序算法，下界为 $\Omega(n \log n)$，因为需要 $\log_2(n!)$ 位信息来区分 $n!$ 种可能的排列。

**决策树下界**:
任何基于比较的排序算法都可以用决策树表示，树的高度就是最坏情况下的比较次数。

### 7.2 上界证明

**构造性证明**:
通过构造具体的算法来证明上界。例如，归并排序证明了 $O(n \log n)$ 的上界。

**归约证明**:
通过将问题归约到已知复杂度的算法来证明上界。

## 8. 总结

计算复杂性理论为算法设计和分析提供了理论基础：

1. **渐进分析**: 使用大O记号描述算法的增长趋势
2. **复杂度类**: 将问题按复杂度特征分类
3. **归约理论**: 建立问题间的复杂度关系
4. **实际应用**: 指导算法选择和优化策略

通过Haskell的实现，我们可以：

- 形式化地表示复杂度概念
- 自动化复杂度分析
- 实现算法选择策略
- 验证复杂度证明

---

**相关文档**:

- [001-算法基础](../01-Computer-Science/001-Algorithms.md)
- [002-数据结构](../01-Computer-Science/002-Data-Structures.md)
- [线性类型理论](../03-Theory/07-Linear-Type-Theory/001-Linear-Type-Theory-Foundation.md)
- [函数式编程基础](../haskell/01-Basic-Concepts/001-Functional-Programming-Foundation.md)
