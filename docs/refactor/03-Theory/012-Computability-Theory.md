# 012. 可计算性理论 (Computability Theory)

## 1. 概述

可计算性理论是研究计算本质和计算能力界限的数学理论。它探讨哪些问题可以通过算法解决，哪些问题在原则上无法解决。可计算性理论为计算机科学提供了理论基础，是理解计算复杂性和算法设计的核心。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[011-Turing-Machines]] - 图灵机理论
- [[005-Denotational-Semantics]] - 指称语义

## 2. 数学基础

### 2.1 可计算函数定义

**定义 2.1.1** (部分函数)
部分函数 $f: \mathbb{N}^k \to \mathbb{N}$ 是从 $\mathbb{N}^k$ 到 $\mathbb{N}$ 的关系，其中每个输入最多对应一个输出。

**定义 2.1.2** (可计算函数)
部分函数 $f: \mathbb{N}^k \to \mathbb{N}$ 是可计算的，如果存在图灵机 $M$ 使得：

对于任意 $(n_1, \ldots, n_k) \in \mathbb{N}^k$：
- 如果 $f(n_1, \ldots, n_k)$ 有定义，则 $M$ 在输入 $\langle n_1, \ldots, n_k \rangle$ 上停机并输出 $f(n_1, \ldots, n_k)$
- 如果 $f(n_1, \ldots, n_k)$ 无定义，则 $M$ 在输入 $\langle n_1, \ldots, n_k \rangle$ 上不停机

**定义 2.1.3** (递归函数)
递归函数是可计算的全函数，即定义域为 $\mathbb{N}^k$ 的可计算函数。

**定义 2.1.4** (递归可枚举集)
集合 $A \subseteq \mathbb{N}$ 是递归可枚举的，如果存在可计算函数 $f$ 使得 $A = \text{range}(f)$。

### 2.2 递归函数理论

**定义 2.2.1** (基本递归函数)
基本递归函数包括：

1. **零函数**: $Z(n) = 0$
2. **后继函数**: $S(n) = n + 1$
3. **投影函数**: $P_i^k(n_1, \ldots, n_k) = n_i$

**定义 2.2.2** (递归函数构造)
递归函数通过以下运算从基本函数构造：

1. **复合**: 如果 $f$ 和 $g_1, \ldots, g_k$ 是递归函数，则 $h(\vec{n}) = f(g_1(\vec{n}), \ldots, g_k(\vec{n}))$ 是递归函数

2. **原始递归**: 如果 $f$ 和 $g$ 是递归函数，则函数 $h$ 定义为：
   $$h(0, \vec{n}) = f(\vec{n})$$
   $$h(m+1, \vec{n}) = g(h(m, \vec{n}), m, \vec{n})$$
   是递归函数

3. **μ-递归**: 如果 $f$ 是递归函数，则函数 $h$ 定义为：
   $$h(\vec{n}) = \mu m[f(m, \vec{n}) = 0]$$
   是递归函数，其中 $\mu m$ 表示最小的 $m$ 使得 $f(m, \vec{n}) = 0$

**定理 2.2.1** (递归函数与图灵机等价)
函数 $f$ 是递归函数当且仅当存在图灵机 $M$ 计算 $f$。

**证明**:
- **必要性**: 通过递归函数的构造规则构造图灵机
- **充分性**: 通过图灵机的编码和模拟构造递归函数

### 2.3 不可判定性问题

**定义 2.3.1** (判定问题)
判定问题是形如"给定输入 $x$，判断 $x$ 是否满足性质 $P$"的问题。

**定义 2.3.2** (可判定性)
判定问题是可判定的，如果存在算法（图灵机）能够对所有输入给出正确的是/否答案。

**定理 2.3.1** (停机问题不可判定)
停机问题 $H = \{\langle M, w \rangle \mid M \text{ 是图灵机且 } M \text{ 在输入 } w \text{ 上停机}\}$ 是不可判定的。

**证明** (对角线法):
假设存在图灵机 $H$ 判定停机问题。构造图灵机 $D$：

$$D(\langle M \rangle) = \begin{cases}
\text{停机} & \text{if } H(\langle M, \langle M \rangle \rangle) = \text{否} \\
\text{不停机} & \text{if } H(\langle M, \langle M \rangle \rangle) = \text{是}
\end{cases}$$

考虑 $D(\langle D \rangle)$：
- 如果 $D(\langle D \rangle)$ 停机，则 $H(\langle D, \langle D \rangle \rangle) = \text{否}$，矛盾
- 如果 $D(\langle D \rangle)$ 不停机，则 $H(\langle D, \langle D \rangle \rangle) = \text{是}$，矛盾

## 3. Haskell 实现

### 3.1 递归函数实现

```haskell
-- | 自然数类型
type Nat = Integer

-- | 部分函数类型
type PartialFunction = Nat -> Maybe Nat

-- | 基本递归函数
class RecursiveFunction f where
  -- | 零函数
  zero :: Nat -> Nat
  zero _ = 0
  
  -- | 后继函数
  successor :: Nat -> Nat
  successor n = n + 1
  
  -- | 投影函数
  projection :: Int -> [Nat] -> Nat
  projection i xs = xs !! (i - 1)

-- | 递归函数实例
instance RecursiveFunction Nat where
  zero = zero
  successor = successor
  projection = projection

-- | 复合函数
compose :: (Nat -> Maybe Nat) -> [Nat -> Maybe Nat] -> [Nat] -> Maybe Nat
compose f gs xs = do
  results <- sequence [g xs | g <- gs]
  f (sum results)

-- | 原始递归
primitiveRecursion :: (Nat -> Maybe Nat) -> (Nat -> Nat -> Nat -> Maybe Nat) -> Nat -> Nat -> Maybe Nat
primitiveRecursion f g 0 n = f n
primitiveRecursion f g m n = do
  prev <- primitiveRecursion f g (m - 1) n
  g prev (m - 1) n

-- | μ-递归 (最小化)
muRecursion :: (Nat -> Nat -> Maybe Nat) -> Nat -> Maybe Nat
muRecursion f n = findMin (\m -> f m n == Just 0)
  where
    findMin p = go 0
      where
        go m = if p m then Just m else go (m + 1)

-- | 加法函数 (通过原始递归)
add :: Nat -> Nat -> Nat
add m n = fromMaybe 0 (primitiveRecursion 
  (\n -> Just n)  -- f(n) = n
  (\prev m n -> Just (successor prev))  -- g(prev, m, n) = prev + 1
  m n)

-- | 乘法函数 (通过原始递归)
multiply :: Nat -> Nat -> Nat
multiply m n = fromMaybe 0 (primitiveRecursion
  (\n -> Just 0)  -- f(n) = 0
  (\prev m n -> Just (add prev n))  -- g(prev, m, n) = prev + n
  m n)

-- | 阶乘函数 (通过原始递归)
factorial :: Nat -> Maybe Nat
factorial n = primitiveRecursion
  (\n -> Just 1)  -- f(n) = 1
  (\prev m n -> Just (multiply prev (m + 1)))  -- g(prev, m, n) = prev * (m + 1)
  n 0

-- | 指数函数 (通过原始递归)
power :: Nat -> Nat -> Maybe Nat
power m n = primitiveRecursion
  (\n -> Just 1)  -- f(n) = 1
  (\prev m n -> Just (multiply prev m))  -- g(prev, m, n) = prev * m
  n m
```

### 3.2 图灵机编码

```haskell
-- | 图灵机编码
type TMEncoding = Nat

-- | 编码图灵机
encodeTM :: TuringMachine String String -> TMEncoding
encodeTM tm = 
  encodeList [encodeStates, encodeAlphabet, encodeTransitions, 
              encodeStartState, encodeAcceptStates]
  where
    encodeStates = encodeSet (states tm)
    encodeAlphabet = encodeSet (inputAlphabet tm)
    encodeTransitions = encodeTransitionFunction (transition tm)
    encodeStartState = encodeString (startState tm)
    encodeAcceptStates = encodeSet (acceptStates tm)

-- | 编码集合
encodeSet :: Set String -> Nat
encodeSet s = encodeList (map encodeString (toList s))

-- | 编码字符串
encodeString :: String -> Nat
encodeString s = foldl (\acc c -> acc * 256 + fromEnum c) 0 s

-- | 编码列表
encodeList :: [Nat] -> Nat
encodeList xs = foldl (\acc x -> acc * 2 + x) 0 (map encodeNat xs)

-- | 编码自然数
encodeNat :: Nat -> Nat
encodeNat n = if n == 0 then 0 else 2 * encodeNat (n `div` 2) + 1

-- | 解码图灵机
decodeTM :: TMEncoding -> Maybe (TuringMachine String String)
decodeTM encoding = do
  (states, rest1) <- decodeSet encoding
  (alphabet, rest2) <- decodeSet rest1
  (transitions, rest3) <- decodeTransitionFunction rest2
  (startState, rest4) <- decodeString rest3
  (acceptStates, _) <- decodeSet rest4
  return TuringMachine
    { states = states
    , inputAlphabet = alphabet
    , tapeAlphabet = alphabet
    , transition = transitions
    , startState = startState
    , blankSymbol = "B"
    , acceptStates = acceptStates
    }

-- | 解码集合
decodeSet :: Nat -> Maybe (Set String, Nat)
decodeSet n = do
  (list, rest) <- decodeList n
  return (fromList list, rest)

-- | 解码字符串
decodeString :: Nat -> Maybe (String, Nat)
decodeString n = 
  let chars = reverse (unfoldr (\x -> if x == 0 then Nothing else Just (chr (fromIntegral (x `mod` 256)), x `div` 256)) n)
  in Just (chars, 0)

-- | 解码列表
decodeList :: Nat -> Maybe ([Nat], Nat)
decodeList n = 
  let (list, rest) = unfoldr (\x -> if x == 0 then Nothing else Just (x `mod` 2, x `div` 2)) n
  in Just (reverse list, rest)
```

### 3.3 通用图灵机

```haskell
-- | 通用图灵机
universalTuringMachine :: TuringMachine String String
universalTuringMachine = TuringMachine
  { states = fromList ["q0", "q1", "q2", "q3", "q4", "q_accept", "q_reject"]
  , inputAlphabet = fromList ["0", "1", "#", "|"]
  , tapeAlphabet = fromList ["0", "1", "#", "|", "B"]
  , transition = \q a -> case (q, a) of
      ("q0", "#") -> Transition "q1" "#" R  -- 开始模拟
      ("q1", "|") -> Transition "q2" "|" R  -- 读取图灵机编码
      ("q2", "0") -> Transition "q2" "0" R  -- 继续读取编码
      ("q2", "1") -> Transition "q2" "1" R
      ("q2", "#") -> Transition "q3" "#" L  -- 开始模拟执行
      ("q3", "0") -> Transition "q3" "0" L  -- 回退到开始位置
      ("q3", "1") -> Transition "q3" "1" L
      ("q3", "|") -> Transition "q4" "|" R  -- 开始执行模拟
      ("q4", "0") -> Transition "q4" "0" R  -- 模拟图灵机执行
      ("q4", "1") -> Transition "q4" "1" R
      ("q4", "B") -> Transition "q_accept" "B" R  -- 接受
      _ -> Transition "q_reject" a R  -- 拒绝
  , startState = "q0"
  , blankSymbol = "B"
  , acceptStates = fromList ["q_accept"]
  }

-- | 模拟图灵机
simulateTM :: TMEncoding -> [String] -> ExecutionResult String String
simulateTM code input = 
  case decodeTM code of
    Just tm -> executeTM tm input
    Nothing -> Reject "decode_error" [] 0

-- | 通用函数计算
universalFunction :: TMEncoding -> Nat -> Maybe Nat
universalFunction code input = 
  case simulateTM code (encodeNat input) of
    Accept _ result _ -> decodeNat result
    _ -> Nothing
  where
    encodeNat n = show n
    decodeNat s = readMaybe s
```

### 3.4 不可判定性问题

```haskell
-- | 停机问题判定器 (假设存在)
haltingDecider :: TMEncoding -> Nat -> Bool
haltingDecider code input = 
  case simulateTM code (show input) of
    Accept _ _ _ -> True
    Reject _ _ _ -> True
    Loop -> False

-- | 对角线图灵机
diagonalTM :: TMEncoding -> Nat -> ExecutionResult String String
diagonalTM code input = 
  if haltingDecider code input
  then Loop  -- 如果停机，则进入无限循环
  else Accept "q_accept" [] 0  -- 如果不停机，则停机

-- | 对角线图灵机的编码
diagonalTMCode :: TMEncoding
diagonalTMCode = encodeTM (TuringMachine
  { states = fromList ["q0", "q1", "q_accept", "q_reject"]
  , inputAlphabet = fromList ["0", "1"]
  , tapeAlphabet = fromList ["0", "1", "B"]
  , transition = \q a -> case (q, a) of
      ("q0", "0") -> Transition "q1" "0" R
      ("q0", "1") -> Transition "q1" "1" R
      ("q1", "0") -> Transition "q1" "0" R
      ("q1", "1") -> Transition "q1" "1" R
      ("q1", "B") -> Transition "q_accept" "B" R
      _ -> Transition "q_reject" a R
  , startState = "q0"
  , blankSymbol = "B"
  , acceptStates = fromList ["q_accept"]
  })

-- | 停机问题的矛盾
haltingContradiction :: Bool
haltingContradiction = 
  let result = haltingDecider diagonalTMCode diagonalTMCode
  in result == not result  -- 这会导致矛盾
```

## 4. 应用实例

### 4.1 递归函数计算器

```haskell
-- | 递归函数计算器
data RecursiveCalculator = RecursiveCalculator
  { basicFunctions :: Map String (Nat -> Maybe Nat)
  , compositeFunctions :: Map String ([Nat] -> Maybe Nat)
  }

-- | 创建计算器
createCalculator :: RecursiveCalculator
createCalculator = RecursiveCalculator
  { basicFunctions = fromList
      [ ("zero", \_ -> Just 0)
      , ("successor", \n -> Just (n + 1))
      , ("identity", \n -> Just n)
      ]
  , compositeFunctions = fromList
      [ ("add", \[m, n] -> Just (m + n))
      , ("multiply", \[m, n] -> Just (m * n))
      , ("factorial", \[n] -> factorial n)
      , ("power", \[m, n] -> power m n)
      ]
  }

-- | 计算递归函数
calculate :: RecursiveCalculator -> String -> [Nat] -> Maybe Nat
calculate calc name args = 
  case Map.lookup name (basicFunctions calc) of
    Just f -> if length args == 1 then f (head args) else Nothing
    Nothing -> 
      case Map.lookup name (compositeFunctions calc) of
        Just f -> f args
        Nothing -> Nothing

-- | 计算示例
calculationExamples :: [(String, [Nat], Maybe Nat)]
calculationExamples = 
  [ ("add", [3, 4], Just 7)
  , ("multiply", [5, 6], Just 30)
  , ("factorial", [5], Just 120)
  , ("power", [2, 8], Just 256)
  ]
```

### 4.2 可判定性检查器

```haskell
-- | 可判定性问题
data DecidabilityProblem = DecidabilityProblem
  { problemName :: String
  , problemDescription :: String
  , isDecidable :: Bool
  , proof :: String
  }

-- | 可判定性问题集合
decidabilityProblems :: [DecidabilityProblem]
decidabilityProblems = 
  [ DecidabilityProblem
      { problemName = "停机问题"
      , problemDescription = "给定图灵机M和输入w，判断M在w上是否停机"
      , isDecidable = False
      , proof = "通过对角线法证明不可判定"
      }
  , DecidabilityProblem
      { problemName = "空语言问题"
      , problemDescription = "给定图灵机M，判断L(M)是否为空"
      , isDecidable = False
      , proof = "通过Rice定理证明不可判定"
      }
  , DecidabilityProblem
      { problemName = "等价性问题"
      , problemDescription = "给定两个图灵机M1和M2，判断L(M1) = L(M2)"
      , isDecidable = False
      , proof = "通过Rice定理证明不可判定"
      }
  , DecidabilityProblem
      { problemName = "成员问题"
      , problemDescription = "给定图灵机M和字符串w，判断w是否属于L(M)"
      , isDecidable = False
      , proof = "通过停机问题归约证明不可判定"
      }
  ]

-- | 检查问题可判定性
checkDecidability :: String -> Maybe Bool
checkDecidability problemName = 
  case find (\p -> problemName == problemName p) decidabilityProblems of
    Just problem -> Just (isDecidable problem)
    Nothing -> Nothing
```

## 5. 理论性质

### 5.1 Rice定理

**定理 5.1.1** (Rice定理)
任何非平凡的语言性质都是不可判定的。

**定义**: 语言性质 $P$ 是非平凡的，如果存在图灵机 $M_1$ 使得 $L(M_1) \in P$，且存在图灵机 $M_2$ 使得 $L(M_2) \notin P$。

**证明**: 通过归约到停机问题。假设存在图灵机 $A$ 判定性质 $P$，构造图灵机 $B$ 判定停机问题：

```haskell
-- | Rice定理的应用
riceTheorem :: String -> Bool -> Bool
riceTheorem propertyName isTrivial = 
  if isTrivial
  then True  -- 平凡性质可能是可判定的
  else False -- 非平凡性质不可判定

-- | 应用Rice定理
applyRiceTheorem :: [DecidabilityProblem]
applyRiceTheorem = 
  [ DecidabilityProblem
      { problemName = "有限性问题"
      , problemDescription = "判断语言是否为有限集"
      , isDecidable = False
      , proof = "Rice定理：非平凡性质"
      }
  , DecidabilityProblem
      { problemName = "正则性问题"
      , problemDescription = "判断语言是否为正则语言"
      , isDecidable = False
      , proof = "Rice定理：非平凡性质"
      }
  , DecidabilityProblem
      { problemName = "上下文无关性问题"
      , problemDescription = "判断语言是否为上下文无关语言"
      , isDecidable = False
      , proof = "Rice定理：非平凡性质"
      }
  ]
```

### 5.2 归约理论

**定义 5.2.1** (图灵归约)
问题 $A$ 图灵归约到问题 $B$，记作 $A \leq_T B$，如果存在图灵机 $M$ 使得：

对于任意输入 $x$，$M$ 可以通过调用 $B$ 的判定器来计算 $A$ 的答案。

**定义 5.2.2** (多一归约)
问题 $A$ 多一归约到问题 $B$，记作 $A \leq_m B$，如果存在可计算函数 $f$ 使得：

对于任意输入 $x$，$x \in A \iff f(x) \in B$。

**定理 5.2.1** (归约的传递性)
如果 $A \leq_T B$ 且 $B \leq_T C$，则 $A \leq_T C$。

```haskell
-- | 归约类型
data ReductionType = TuringReduction | ManyOneReduction

-- | 归约关系
data Reduction a b = Reduction
  { reductionType :: ReductionType
  , reductionFunction :: a -> b
  , reductionProof :: String
  }

-- | 归约示例
reductionExamples :: [Reduction String String]
reductionExamples = 
  [ Reduction
      { reductionType = ManyOneReduction
      , reductionFunction = \x -> "halt_" ++ x
      , reductionProof = "停机问题归约到空语言问题"
      }
  , Reduction
      { reductionType = ManyOneReduction
      , reductionFunction = \x -> "equiv_" ++ x
      , reductionProof = "空语言问题归约到等价性问题"
      }
  ]
```

### 5.3 递归可枚举性

**定义 5.3.1** (递归可枚举集)
集合 $A \subseteq \mathbb{N}$ 是递归可枚举的，如果存在可计算函数 $f$ 使得 $A = \text{range}(f)$。

**定理 5.3.1** (递归可枚举集的性质)
集合 $A$ 是递归可枚举的当且仅当存在图灵机 $M$ 使得 $A = L(M)$。

**定理 5.3.2** (递归可枚举集的补集)
如果 $A$ 和 $\overline{A}$ 都是递归可枚举的，则 $A$ 是递归的。

```haskell
-- | 递归可枚举集
data RecursivelyEnumerableSet = RecursivelyEnumerableSet
  { setName :: String
  , enumerator :: Nat -> Maybe Nat
  , isRecursive :: Bool
  }

-- | 递归可枚举集示例
reSetExamples :: [RecursivelyEnumerableSet]
reSetExamples = 
  [ RecursivelyEnumerableSet
      { setName = "可停机图灵机编码"
      , enumerator = \n -> Just n  -- 简化版本
      , isRecursive = False
      }
  , RecursivelyEnumerableSet
      { setName = "非空语言图灵机编码"
      , enumerator = \n -> Just n  -- 简化版本
      , isRecursive = False
      }
  ]
```

## 6. 复杂度分析

### 6.1 计算复杂度

- **递归函数**: 无固定复杂度，取决于具体函数
- **图灵机模拟**: $O(n^2)$ 空间，无固定时间
- **通用图灵机**: $O(n^3)$ 时间，$O(n^2)$ 空间

### 6.2 不可判定性

- **停机问题**: 不可判定
- **空语言问题**: 不可判定
- **等价性问题**: 不可判定
- **成员问题**: 不可判定

## 7. 扩展与变体

### 7.1 相对可计算性

```haskell
-- | 相对可计算性
data RelativeComputability = RelativeComputability
  { oracle :: String -> Bool
  , computableFunction :: String -> Maybe String
  }

-- | 相对图灵机
relativeTM :: (String -> Bool) -> TuringMachine String String
relativeTM oracle = TuringMachine
  { states = fromList ["q0", "q1", "q2", "q_accept", "q_reject"]
  , inputAlphabet = fromList ["0", "1", "?"]
  , tapeAlphabet = fromList ["0", "1", "?", "B"]
  , transition = \q a -> case (q, a) of
      ("q0", "?") -> 
        if oracle "query"
        then Transition "q1" "1" R
        else Transition "q2" "0" R
      ("q1", "0") -> Transition "q1" "0" R
      ("q1", "1") -> Transition "q1" "1" R
      ("q1", "B") -> Transition "q_accept" "B" R
      ("q2", "0") -> Transition "q2" "0" R
      ("q2", "1") -> Transition "q2" "1" R
      ("q2", "B") -> Transition "q_reject" "B" R
      _ -> Transition "q_reject" a R
  , startState = "q0"
  , blankSymbol = "B"
  , acceptStates = fromList ["q_accept"]
  }
```

### 7.2 计算理论应用

```haskell
-- | 计算理论应用
data ComputabilityApplication = ComputabilityApplication
  { applicationName :: String
  , description :: String
  , computabilityResult :: String
  }

-- | 应用示例
computabilityApplications :: [ComputabilityApplication]
computabilityApplications = 
  [ ComputabilityApplication
      { applicationName = "编译器优化"
      , description = "判断程序优化是否保持语义等价"
      , computabilityResult = "不可判定"
      }
  , ComputabilityApplication
      { applicationName = "程序验证"
      , description = "自动验证程序是否满足规约"
      , computabilityResult = "部分可判定"
      }
  , ComputabilityApplication
      { applicationName = "类型推断"
      , description = "推断程序表达式的类型"
      , computabilityResult = "可判定但复杂"
      }
  ]
```

## 8. 总结

可计算性理论为计算机科学提供了重要的理论基础，具有以下特点：

1. **理论基础**: 为计算提供形式化定义
2. **界限分析**: 识别可计算与不可计算的问题
3. **归约技术**: 建立问题间的复杂关系
4. **不可判定性**: 揭示计算的固有局限性
5. **实际应用**: 指导算法设计和程序分析

可计算性理论在编译器设计、程序验证、算法分析等领域有重要应用，是理解计算本质的核心理论。

**相关文档**:
- [[009-Regular-Languages]] - 正则语言理论
- [[010-Context-Free-Grammars]] - 上下文无关文法
- [[011-Turing-Machines]] - 图灵机理论 