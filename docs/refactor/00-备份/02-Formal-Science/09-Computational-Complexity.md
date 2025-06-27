# 计算复杂性理论 (Computational Complexity Theory)

## 概述

计算复杂性理论研究计算问题的难度和资源需求，包括时间复杂度、空间复杂度、以及各种复杂度类别之间的关系。它为算法设计和问题分类提供了理论基础。

## 基本概念

### 计算问题

计算问题可以形式化为函数或关系：

```haskell
-- 计算问题的形式化
class ComputationalProblem p where
  type Instance p
  type Solution p
  type Certificate p
  
  -- 问题实例
  instance :: p -> Instance p
  
  -- 解决方案
  solution :: p -> Instance p -> Solution p
  
  -- 验证证书
  verify :: p -> Instance p -> Certificate p -> Bool
```

### 复杂度度量

复杂度理论主要关注时间和空间资源：

```haskell
-- 复杂度度量
class ComplexityMeasure m where
  type Resource m
  type Bound m
  
  -- 资源使用
  resourceUsage :: m -> Algorithm -> Input -> Resource m
  
  -- 复杂度上界
  upperBound :: m -> Algorithm -> Bound m
  
  -- 复杂度下界
  lowerBound :: m -> Problem -> Bound m
```

## 复杂度类别

### 1. 基本复杂度类别

#### P类 (多项式时间)

P类包含所有可以在多项式时间内解决的问题。

```haskell
-- P类问题
class PClass p where
  type PolynomialTime p
  
  -- 多项式时间算法
  polynomialTimeAlgorithm :: p -> Instance p -> Solution p
  
  -- 时间复杂度
  timeComplexity :: p -> Instance p -> Int -> Int
  
  -- 多项式上界
  isPolynomial :: p -> (Int -> Int) -> Bool
```

**数学定义**：

问题 $L$ 属于P类当且仅当存在多项式时间算法 $A$ 和多项式 $p$，使得：
$$\forall x: A(x) \text{ 在 } O(p(|x|)) \text{ 时间内正确判定 } x \in L$$

#### NP类 (非确定性多项式时间)

NP类包含所有可以在多项式时间内验证解的问题。

```haskell
-- NP类问题
class NPClass p where
  type Certificate p
  
  -- 非确定性算法
  nondeterministicAlgorithm :: p -> Instance p -> [Solution p]
  
  -- 证书验证
  verifyCertificate :: p -> Instance p -> Certificate p -> Bool
  
  -- 多项式时间验证
  polynomialTimeVerification :: p -> Instance p -> Certificate p -> Bool
```

**数学定义**：

问题 $L$ 属于NP类当且仅当存在多项式时间验证算法 $V$ 和多项式 $p$，使得：
$$\forall x: x \in L \iff \exists c: |c| \leq p(|x|) \land V(x, c) = 1$$

#### PSPACE类 (多项式空间)

PSPACE类包含所有可以在多项式空间内解决的问题。

```haskell
-- PSPACE类问题
class PSPACEClass p where
  type PolynomialSpace p
  
  -- 多项式空间算法
  polynomialSpaceAlgorithm :: p -> Instance p -> Solution p
  
  -- 空间复杂度
  spaceComplexity :: p -> Instance p -> Int -> Int
  
  -- 空间上界
  isPolynomialSpace :: p -> (Int -> Int) -> Bool
```

### 2. 高级复杂度类别

#### EXPTIME类 (指数时间)

```haskell
-- EXPTIME类问题
class EXPTIMEClass p where
  type ExponentialTime p
  
  -- 指数时间算法
  exponentialTimeAlgorithm :: p -> Instance p -> Solution p
  
  -- 指数时间上界
  isExponentialTime :: p -> (Int -> Int) -> Bool
```

#### NEXPTIME类 (非确定性指数时间)

```haskell
-- NEXPTIME类问题
class NEXPTIMEClass p where
  type NondeterministicExponentialTime p
  
  -- 非确定性指数时间算法
  nondeterministicExponentialAlgorithm :: p -> Instance p -> [Solution p]
```

## 归约理论

### 1. 多项式时间归约

多项式时间归约是复杂度理论的核心概念。

```haskell
-- 多项式时间归约
class PolynomialTimeReduction r where
  type Reduction r
  
  -- 归约函数
  reduce :: r -> Problem -> Problem -> Instance -> Instance
  
  -- 归约的正确性
  isCorrect :: r -> Problem -> Problem -> Instance -> Bool
  
  -- 归约的时间复杂度
  reductionTime :: r -> Problem -> Problem -> Instance -> Int
```

**数学定义**：

问题 $A$ 多项式时间归约到问题 $B$（记作 $A \leq_P B$）当且仅当存在多项式时间可计算函数 $f$，使得：
$$\forall x: x \in A \iff f(x) \in B$$

### 2. 图灵归约

图灵归约允许使用目标问题作为子程序。

```haskell
-- 图灵归约
class TuringReduction t where
  type Oracle t
  
  -- 图灵归约
  turingReduce :: t -> Problem -> Problem -> Instance -> Instance
  
  -- 预言机调用
  oracleCall :: t -> Oracle t -> Instance -> Bool
  
  -- 归约的正确性
  isTuringCorrect :: t -> Problem -> Problem -> Instance -> Bool
```

## 完全性问题

### 1. NP完全性

NP完全问题是NP类中最难的问题。

```haskell
-- NP完全问题
class NPComplete p where
  -- NP完全性条件
  isInNP :: p -> Bool
  isNPHard :: p -> Bool
  
  -- NP完全性证明
  proveNPComplete :: p -> Proof
  
  -- 标准NP完全问题
  standardNPComplete :: [Problem]
```

**数学定义**：

问题 $L$ 是NP完全的当且仅当：

1. $L \in \text{NP}$
2. $\forall A \in \text{NP}: A \leq_P L$

### 2. PSPACE完全性

```haskell
-- PSPACE完全问题
class PSPACEComplete p where
  -- PSPACE完全性条件
  isInPSPACE :: p -> Bool
  isPSPACEHard :: p -> Bool
  
  -- PSPACE完全性证明
  provePSPACEComplete :: p -> Proof
```

## 经典NP完全问题

### 1. 布尔可满足性问题 (SAT)

```haskell
-- 布尔可满足性问题
data SAT = SAT {
  variables :: [Variable],
  clauses :: [Clause]
}

-- 变量
data Variable = Variable {
  name :: String,
  value :: Maybe Bool
}

-- 子句
data Clause = Clause {
  literals :: [Literal]
}

-- 文字
data Literal = 
  Positive Variable
  | Negative Variable

-- SAT求解器
class SATSolver s where
  solve :: s -> SAT -> Maybe Assignment
  
  -- 赋值
  type Assignment s
  
  -- 验证赋值
  verifyAssignment :: s -> SAT -> Assignment s -> Bool
```

### 2. 3-SAT问题

```haskell
-- 3-SAT问题
data ThreeSAT = ThreeSAT {
  variables :: [Variable],
  clauses :: [ThreeClause]  -- 每个子句恰好3个文字
}

-- 3-子句
data ThreeClause = ThreeClause {
  literal1 :: Literal,
  literal2 :: Literal,
  literal3 :: Literal
}

-- 3-SAT求解器
class ThreeSATSolver s where
  solve :: s -> ThreeSAT -> Maybe Assignment
  reduceFromSAT :: s -> SAT -> ThreeSAT
```

### 3. 顶点覆盖问题

```haskell
-- 顶点覆盖问题
data VertexCover = VertexCover {
  graph :: Graph,
  k :: Int
}

-- 图
data Graph = Graph {
  vertices :: [Vertex],
  edges :: [Edge]
}

-- 顶点
data Vertex = Vertex {
  id :: Int,
  label :: String
}

-- 边
data Edge = Edge {
  from :: Vertex,
  to :: Vertex
}

-- 顶点覆盖求解器
class VertexCoverSolver s where
  solve :: s -> VertexCover -> Maybe [Vertex]
  reduceFromThreeSAT :: s -> ThreeSAT -> VertexCover
```

## 近似算法

### 1. 近似算法框架

```haskell
-- 近似算法
class ApproximationAlgorithm a where
  type ApproximationRatio a
  
  -- 近似解
  approximate :: a -> Problem -> Instance -> Solution
  
  -- 近似比
  approximationRatio :: a -> Problem -> Instance -> Double
  
  -- 最优解
  optimalSolution :: a -> Problem -> Instance -> Solution
```

### 2. 多项式时间近似方案 (PTAS)

```haskell
-- PTAS
class PTAS p where
  -- 近似方案
  approximationScheme :: p -> Problem -> Epsilon -> Algorithm
  
  -- 精度参数
  type Epsilon p
  
  -- 时间复杂度
  timeComplexity :: p -> Epsilon -> (Int -> Int)
```

## 随机化算法

### 1. 随机化复杂度类别

#### BPP类 (有界错误概率多项式时间)

```haskell
-- BPP类
class BPPClass p where
  type BoundedError p
  
  -- 随机化算法
  randomizedAlgorithm :: p -> Instance p -> Random -> Solution p
  
  -- 错误概率
  errorProbability :: p -> Instance p -> Double
  
  -- 有界错误
  isBoundedError :: p -> Instance p -> Bool
```

#### RP类 (随机多项式时间)

```haskell
-- RP类
class RPClass p where
  -- 单侧错误
  oneSidedError :: p -> Instance p -> Bool
  
  -- 随机化算法
  rpAlgorithm :: p -> Instance p -> Random -> Bool
```

### 2. 去随机化

```haskell
-- 去随机化
class Derandomization d where
  -- 去随机化算法
  derandomize :: d -> RandomizedAlgorithm -> DeterministicAlgorithm
  
  -- 伪随机数生成器
  pseudorandomGenerator :: d -> Seed -> [Random]
  
  -- 种子长度
  seedLength :: d -> Int
```

## 电路复杂性

### 1. 电路模型

```haskell
-- 布尔电路
data BooleanCircuit = BooleanCircuit {
  inputs :: [Input],
  gates :: [Gate],
  outputs :: [Output]
}

-- 输入
data Input = Input {
  index :: Int,
  name :: String
}

-- 门
data Gate = 
  AND [Wire]
  | OR [Wire]
  | NOT Wire
  | XOR [Wire]

-- 输出
data Output = Output {
  gate :: Gate,
  name :: String
}

-- 线
data Wire = Wire {
  from :: Either Input Gate,
  to :: Gate
}
```

### 2. 电路复杂度类别

#### AC类 (交替电路)

```haskell
-- AC类
class ACClass c where
  type AlternatingCircuit c
  
  -- 交替深度
  alternatingDepth :: c -> Int
  
  -- 多项式大小
  polynomialSize :: c -> Bool
```

#### NC类 (Nick类)

```haskell
-- NC类
class NCClass c where
  type NickCircuit c
  
  -- 对数深度
  logarithmicDepth :: c -> Bool
  
  -- 多项式大小
  polynomialSize :: c -> Bool
```

## Haskell实现示例

### 复杂度分析器

```haskell
-- 复杂度分析器
data ComplexityAnalyzer = ComplexityAnalyzer

-- 算法复杂度
data AlgorithmComplexity = 
  Constant
  | Logarithmic
  | Linear
  | Linearithmic
  | Quadratic
  | Cubic
  | Exponential
  | Factorial

-- 复杂度分析
analyzeComplexity :: ComplexityAnalyzer -> Algorithm -> Input -> AlgorithmComplexity
analyzeComplexity analyzer algorithm input = 
  let steps = countSteps algorithm input
      size = inputSize input
  in classifyComplexity steps size

-- 输入大小
inputSize :: Input -> Int
inputSize input = case input of
  ListInput xs -> length xs
  StringInput s -> length s
  GraphInput g -> vertexCount g
  MatrixInput m -> rows m * cols m

-- 复杂度分类
classifyComplexity :: Int -> Int -> AlgorithmComplexity
classifyComplexity steps size
  | steps <= 1 = Constant
  | steps <= logBase 2 (fromIntegral size) = Logarithmic
  | steps <= size = Linear
  | steps <= size * logBase 2 (fromIntegral size) = Linearithmic
  | steps <= size^2 = Quadratic
  | steps <= size^3 = Cubic
  | steps <= 2^size = Exponential
  | otherwise = Factorial
```

### SAT求解器

```haskell
-- 简单的SAT求解器
data SimpleSATSolver = SimpleSATSolver

-- 求解SAT
solveSAT :: SimpleSATSolver -> SAT -> Maybe Assignment
solveSAT solver sat = 
  let allAssignments = generateAllAssignments (variables sat)
  in find (\assignment -> verifyAssignment solver sat assignment) allAssignments

-- 生成所有赋值
generateAllAssignments :: [Variable] -> [Assignment]
generateAllAssignments vars = 
  let bools = replicateM (length vars) [True, False]
  in map (zip vars) bools

-- 验证赋值
verifyAssignment :: SimpleSATSolver -> SAT -> Assignment -> Bool
verifyAssignment solver sat assignment = 
  all (\clause -> evaluateClause clause assignment) (clauses sat)

-- 评估子句
evaluateClause :: Clause -> Assignment -> Bool
evaluateClause clause assignment = 
  any (\literal -> evaluateLiteral literal assignment) (literals clause)

-- 评估文字
evaluateLiteral :: Literal -> Assignment -> Bool
evaluateLiteral literal assignment = 
  case literal of
    Positive var -> lookup var assignment == Just True
    Negative var -> lookup var assignment == Just False
```

### 归约实现

```haskell
-- 3-SAT到顶点覆盖的归约
reduceThreeSATToVertexCover :: ThreeSAT -> VertexCover
reduceThreeSATToVertexCover threeSAT = 
  let vertices = createVertices threeSAT
      edges = createEdges threeSAT
      k = calculateK threeSAT
  in VertexCover (Graph vertices edges) k

-- 创建顶点
createVertices :: ThreeSAT -> [Vertex]
createVertices threeSAT = 
  let varVertices = concatMap createVariableVertices (variables threeSAT)
      clauseVertices = concatMap createClauseVertices (clauses threeSAT)
  in varVertices ++ clauseVertices

-- 创建边
createEdges :: ThreeSAT -> [Edge]
createEdges threeSAT = 
  let varEdges = createVariableEdges (variables threeSAT)
      clauseEdges = createClauseEdges (clauses threeSAT)
      connectionEdges = createConnectionEdges threeSAT
  in varEdges ++ clauseEdges ++ connectionEdges
```

## 总结

计算复杂性理论为算法设计和问题分类提供了理论基础。通过研究不同复杂度类别之间的关系，我们可以理解计算问题的内在难度，并为算法设计提供指导。

复杂度理论的研究不仅推动了计算机科学的发展，也为其他学科提供了重要的工具和方法。P vs NP问题作为计算机科学的核心问题之一，仍然是一个开放的研究领域。
