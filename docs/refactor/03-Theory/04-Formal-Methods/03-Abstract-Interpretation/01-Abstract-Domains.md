# 抽象域

## 📋 概述

抽象域是抽象解释理论的核心概念，用于表示程序状态集合的抽象。它提供了一种在保持程序语义的同时，简化复杂状态空间的方法。本文档介绍抽象域的基本概念、常见抽象域和Haskell实现。

## 🎯 核心概念

### 抽象域基础

#### 格理论

```haskell
-- 格
class (Eq a) => Lattice a where
    bottom :: a                    -- 最小元素
    top :: a                       -- 最大元素
    meet :: a -> a -> a           -- 下确界
    join :: a -> a -> a           -- 上确界
    leq :: a -> a -> Bool         -- 偏序关系

-- 格的性质
latticeProperties :: Lattice a => a -> a -> a -> Bool
latticeProperties x y z = 
    -- 交换律
    meet x y == meet y x &&
    join x y == join y x &&
    -- 结合律
    meet (meet x y) z == meet x (meet y z) &&
    join (join x y) z == join x (join y z) &&
    -- 吸收律
    meet x (join x y) == x &&
    join x (meet x y) == x &&
    -- 单位元
    meet x top == x &&
    join x bottom == x

-- 完全格
class (Lattice a) => CompleteLattice a where
    meetAll :: [a] -> a           -- 任意集合的下确界
    joinAll :: [a] -> a           -- 任意集合的上确界

-- 单调函数
type MonotoneFunction a = a -> a

-- 单调性检查
isMonotone :: (Lattice a) => MonotoneFunction a -> a -> a -> Bool
isMonotone f x y = 
    if leq x y 
    then leq (f x) (f y)
    else True
```

#### 抽象域定义

```haskell
-- 抽象域
class (CompleteLattice a) => AbstractDomain a where
    -- 抽象函数：从具体状态到抽象状态
    alpha :: ConcreteState -> a
    -- 具体化函数：从抽象状态到具体状态集合
    gamma :: a -> [ConcreteState]
    -- 抽象域操作
    abstractJoin :: a -> a -> a
    abstractMeet :: a -> a -> a
    abstractWidening :: a -> a -> a
    abstractNarrowing :: a -> a -> a

-- 具体状态
data ConcreteState = ConcreteState
    { variables :: Map String Int
    , heap :: Map Int Int
    , stack :: [Int]
    }
    deriving (Show, Eq)

-- 抽象状态
data AbstractState = AbstractState
    { intervals :: Map String Interval
    , signs :: Map String Sign
    , parity :: Map String Parity
    }
    deriving (Show, Eq)
```

### 常见抽象域

#### 区间域

```haskell
-- 区间
data Interval = 
    Interval Int Int              -- 闭区间 [a, b]
  | Top                           -- 全区间 [-∞, +∞]
  | Bottom                        -- 空区间
  deriving (Show, Eq)

-- 区间格实例
instance Lattice Interval where
    bottom = Bottom
    top = Top
    
    meet (Interval a1 b1) (Interval a2 b2) = 
        let a = max a1 a2
            b = min b1 b2
        in if a <= b then Interval a b else Bottom
    meet Top interval = interval
    meet interval Top = interval
    meet Bottom _ = Bottom
    meet _ Bottom = Bottom
    
    join (Interval a1 b1) (Interval a2 b2) = 
        let a = min a1 a2
            b = max b1 b2
        in Interval a b
    join Top _ = Top
    join _ Top = Top
    join Bottom interval = interval
    join interval Bottom = interval
    
    leq (Interval a1 b1) (Interval a2 b2) = 
        a2 <= a1 && b1 <= b2
    leq Bottom _ = True
    leq _ Top = True
    leq _ _ = False

-- 区间运算
intervalAdd :: Interval -> Interval -> Interval
intervalAdd (Interval a1 b1) (Interval a2 b2) = 
    Interval (a1 + a2) (b1 + b2)
intervalAdd Top _ = Top
intervalAdd _ Top = Top
intervalAdd Bottom _ = Bottom
intervalAdd _ Bottom = Bottom

intervalSub :: Interval -> Interval -> Interval
intervalSub (Interval a1 b1) (Interval a2 b2) = 
    Interval (a1 - b2) (b1 - a2)
intervalSub Top _ = Top
intervalSub _ Top = Top
intervalSub Bottom _ = Bottom
intervalSub _ Bottom = Bottom

intervalMul :: Interval -> Interval -> Interval
intervalMul (Interval a1 b1) (Interval a2 b2) = 
    let candidates = [a1 * a2, a1 * b2, b1 * a2, b1 * b2]
    in Interval (minimum candidates) (maximum candidates)
intervalMul Top _ = Top
intervalMul _ Top = Top
intervalMul Bottom _ = Bottom
intervalMul _ Bottom = Bottom
```

#### 符号域

```haskell
-- 符号
data Sign = 
    Negative                      -- 负数
  | Zero                          -- 零
  | Positive                      -- 正数
  | TopSign                       -- 任意符号
  | BottomSign                    -- 无符号
  deriving (Show, Eq)

-- 符号格实例
instance Lattice Sign where
    bottom = BottomSign
    top = TopSign
    
    meet Negative Negative = Negative
    meet Positive Positive = Positive
    meet Zero Zero = Zero
    meet TopSign s = s
    meet s TopSign = s
    meet BottomSign _ = BottomSign
    meet _ BottomSign = BottomSign
    meet _ _ = BottomSign
    
    join Negative Negative = Negative
    join Positive Positive = Positive
    join Zero Zero = Zero
    join TopSign _ = TopSign
    join _ TopSign = TopSign
    join BottomSign s = s
    join s BottomSign = s
    join _ _ = TopSign
    
    leq s TopSign = True
    leq BottomSign _ = True
    leq s1 s2 = s1 == s2

-- 符号运算
signAdd :: Sign -> Sign -> Sign
signAdd Negative Negative = Negative
signAdd Positive Positive = Positive
signAdd Zero s = s
signAdd s Zero = s
signAdd Negative Positive = TopSign
signAdd Positive Negative = TopSign
signAdd TopSign _ = TopSign
signAdd _ TopSign = TopSign
signAdd BottomSign _ = BottomSign
signAdd _ BottomSign = BottomSign

signMul :: Sign -> Sign -> Sign
signMul Negative Negative = Positive
signMul Positive Positive = Positive
signMul Negative Positive = Negative
signMul Positive Negative = Negative
signMul Zero _ = Zero
signMul _ Zero = Zero
signMul TopSign _ = TopSign
signMul _ TopSign = TopSign
signMul BottomSign _ = BottomSign
signMul _ BottomSign = BottomSign
```

#### 奇偶域

```haskell
-- 奇偶性
data Parity = 
    Even                          -- 偶数
  | Odd                           -- 奇数
  | TopParity                     -- 任意奇偶性
  | BottomParity                  -- 无奇偶性
  deriving (Show, Eq)

-- 奇偶格实例
instance Lattice Parity where
    bottom = BottomParity
    top = TopParity
    
    meet Even Even = Even
    meet Odd Odd = Odd
    meet TopParity p = p
    meet p TopParity = p
    meet BottomParity _ = BottomParity
    meet _ BottomParity = BottomParity
    meet _ _ = BottomParity
    
    join Even Even = Even
    join Odd Odd = Odd
    join TopParity _ = TopParity
    join _ TopParity = TopParity
    join BottomParity p = p
    join p BottomParity = p
    join _ _ = TopParity
    
    leq p TopParity = True
    leq BottomParity _ = True
    leq p1 p2 = p1 == p2

-- 奇偶运算
parityAdd :: Parity -> Parity -> Parity
parityAdd Even Even = Even
parityAdd Odd Odd = Even
parityAdd Even Odd = Odd
parityAdd Odd Even = Odd
parityAdd TopParity _ = TopParity
parityAdd _ TopParity = TopParity
parityAdd BottomParity _ = BottomParity
parityAdd _ BottomParity = BottomParity

parityMul :: Parity -> Parity -> Parity
parityMul Even _ = Even
parityMul _ Even = Even
parityMul Odd Odd = Odd
parityMul TopParity _ = TopParity
parityMul _ TopParity = TopParity
parityMul BottomParity _ = BottomParity
parityMul _ BottomParity = BottomParity
```

## 🔧 Haskell实现

### 抽象解释器

```haskell
-- 抽象解释器
module AbstractInterpreter where

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

-- 抽象解释状态
data AbstractInterpreterState = AbstractInterpreterState
    { abstractState :: AbstractState
    , programPoint :: String
    , callStack :: [String]
    }

-- 抽象解释器单子
type AbstractInterpreter = State AbstractInterpreterState

-- 抽象解释主函数
abstractInterpret :: Program -> AbstractState -> AbstractState
abstractInterpret program initialState = 
    let initialState' = AbstractInterpreterState initialState "start" []
        finalState = execState (interpretProgram program) initialState'
    in abstractState finalState

-- 解释程序
interpretProgram :: Program -> AbstractInterpreter ()
interpretProgram program = 
    case program of
        Skip -> return ()
        Assign var expr -> interpretAssign var expr
        Seq p1 p2 -> do
            interpretProgram p1
            interpretProgram p2
        If cond p1 p2 -> interpretIf cond p1 p2
        While cond body -> interpretWhile cond body

-- 解释赋值
interpretAssign :: String -> Expression -> AbstractInterpreter ()
interpretAssign var expr = do
    state <- get
    let newValue = abstractEval expr (abstractState state)
    put $ state { 
        abstractState = updateVariable (abstractState state) var newValue
    }

-- 解释条件语句
interpretIf :: Expression -> Program -> Program -> AbstractInterpreter ()
interpretIf cond p1 p2 = do
    state <- get
    let condValue = abstractEval cond (abstractState state)
    case condValue of
        Sign Positive -> interpretProgram p1
        Sign Negative -> interpretProgram p2
        Sign Zero -> interpretProgram p2
        _ -> do
            -- 分支合并
            let state1 = execState (interpretProgram p1) state
            let state2 = execState (interpretProgram p2) state
            put $ state { 
                abstractState = abstractJoin (abstractState state1) (abstractState state2)
            }

-- 解释循环
interpretWhile :: Expression -> Program -> AbstractInterpreter ()
interpretWhile cond body = do
    state <- get
    let condValue = abstractEval cond (abstractState state)
    case condValue of
        Sign Positive -> do
            interpretProgram body
            interpretWhile cond body
        Sign Negative -> return ()
        Sign Zero -> return ()
        _ -> do
            -- 使用扩宽操作
            let state' = execState (interpretProgram body) state
            let widened = abstractWidening (abstractState state) (abstractState state')
            put $ state { abstractState = widened }
            interpretWhile cond body

-- 抽象求值
abstractEval :: Expression -> AbstractState -> AbstractValue
abstractEval expr state = 
    case expr of
        Const n -> abstractConst n
        Var var -> lookupVariable state var
        Add e1 e2 -> 
            let v1 = abstractEval e1 state
                v2 = abstractEval e2 state
            in abstractAdd v1 v2
        Sub e1 e2 -> 
            let v1 = abstractEval e1 state
                v2 = abstractEval e2 state
            in abstractSub v1 v2
        Mul e1 e2 -> 
            let v1 = abstractEval e1 state
                v2 = abstractEval e2 state
            in abstractMul v1 v2

-- 抽象值
data AbstractValue = 
    IntervalValue Interval
  | SignValue Sign
  | ParityValue Parity
  deriving (Show, Eq)

-- 抽象常量
abstractConst :: Int -> AbstractValue
abstractConst n = 
    let interval = Interval n n
        sign = if n < 0 then Negative else if n == 0 then Zero else Positive
        parity = if even n then Even else Odd
    in IntervalValue interval  -- 简化，只返回区间值

-- 抽象运算
abstractAdd :: AbstractValue -> AbstractValue -> AbstractValue
abstractAdd (IntervalValue i1) (IntervalValue i2) = 
    IntervalValue (intervalAdd i1 i2)
abstractAdd (SignValue s1) (SignValue s2) = 
    SignValue (signAdd s1 s2)
abstractAdd (ParityValue p1) (ParityValue p2) = 
    ParityValue (parityAdd p1 p2)
abstractAdd _ _ = error "Type mismatch in abstract addition"

abstractSub :: AbstractValue -> AbstractValue -> AbstractValue
abstractSub (IntervalValue i1) (IntervalValue i2) = 
    IntervalValue (intervalSub i1 i2)
abstractSub (SignValue s1) (SignValue s2) = 
    SignValue (signAdd s1 (signNeg s2))
abstractSub (ParityValue p1) (ParityValue p2) = 
    ParityValue (parityAdd p1 p2)  -- 减法等价于加法
abstractSub _ _ = error "Type mismatch in abstract subtraction"

abstractMul :: AbstractValue -> AbstractValue -> AbstractValue
abstractMul (IntervalValue i1) (IntervalValue i2) = 
    IntervalValue (intervalMul i1 i2)
abstractMul (SignValue s1) (SignValue s2) = 
    SignValue (signMul s1 s2)
abstractMul (ParityValue p1) (ParityValue p2) = 
    ParityValue (parityMul p1 p2)
abstractMul _ _ = error "Type mismatch in abstract multiplication"
```

### 扩宽和缩窄

```haskell
-- 扩宽操作
abstractWidening :: AbstractState -> AbstractState -> AbstractState
abstractWidening state1 state2 = 
    AbstractState
        { intervals = Map.intersectionWith intervalWidening 
                       (intervals state1) (intervals state2)
        , signs = Map.intersectionWith signWidening 
                    (signs state1) (signs state2)
        , parity = Map.intersectionWith parityWidening 
                     (parity state1) (parity state2)
        }

-- 区间扩宽
intervalWidening :: Interval -> Interval -> Interval
intervalWidening (Interval a1 b1) (Interval a2 b2) = 
    let a = if a2 < a1 then minBound else a1
        b = if b2 > b1 then maxBound else b1
    in Interval a b
intervalWidening Top _ = Top
intervalWidening _ Top = Top
intervalWidening Bottom interval = interval
intervalWidening interval Bottom = interval

-- 符号扩宽
signWidening :: Sign -> Sign -> Sign
signWidening s1 s2 = 
    if s1 == s2 then s1 else TopSign

-- 奇偶扩宽
parityWidening :: Parity -> Parity -> Parity
parityWidening p1 p2 = 
    if p1 == p2 then p1 else TopParity

-- 缩窄操作
abstractNarrowing :: AbstractState -> AbstractState -> AbstractState
abstractNarrowing state1 state2 = 
    AbstractState
        { intervals = Map.intersectionWith intervalNarrowing 
                       (intervals state1) (intervals state2)
        , signs = Map.intersectionWith signNarrowing 
                    (signs state1) (signs state2)
        , parity = Map.intersectionWith parityNarrowing 
                     (parity state1) (parity state2)
        }

-- 区间缩窄
intervalNarrowing :: Interval -> Interval -> Interval
intervalNarrowing (Interval a1 b1) (Interval a2 b2) = 
    let a = max a1 a2
        b = min b1 b2
    in if a <= b then Interval a b else Bottom
intervalNarrowing Top interval = interval
intervalNarrowing interval Top = interval
intervalNarrowing Bottom _ = Bottom
intervalNarrowing _ Bottom = Bottom
```

## 📊 应用示例

### 简单程序分析

```haskell
-- 示例程序：x = 1; while x < 10 do x = x + 1
exampleProgram :: Program
exampleProgram = 
    Seq (Assign "x" (Const 1))
        (While (Less (Var "x") (Const 10))
               (Assign "x" (Add (Var "x") (Const 1))))

-- 初始抽象状态
initialAbstractState :: AbstractState
initialAbstractState = AbstractState
    { intervals = Map.empty
    , signs = Map.empty
    , parity = Map.empty
    }

-- 分析程序
analyzeProgram :: IO ()
analyzeProgram = do
    let finalState = abstractInterpret exampleProgram initialAbstractState
    putStrLn $ "Final abstract state: " ++ show finalState
    putStrLn $ "x interval: " ++ show (Map.lookup "x" (intervals finalState))
    putStrLn $ "x sign: " ++ show (Map.lookup "x" (signs finalState))
    putStrLn $ "x parity: " ++ show (Map.lookup "x" (parity finalState))
```

### 抽象域组合

```haskell
-- 组合抽象域
data CombinedDomain = CombinedDomain
    { intervalDomain :: Map String Interval
    , signDomain :: Map String Sign
    , parityDomain :: Map String Parity
    }
    deriving (Show, Eq)

-- 组合域格实例
instance Lattice CombinedDomain where
    bottom = CombinedDomain Map.empty Map.empty Map.empty
    top = CombinedDomain 
            (Map.fromList [("x", Top)]) 
            (Map.fromList [("x", TopSign)]) 
            (Map.fromList [("x", TopParity)])
    
    meet (CombinedDomain i1 s1 p1) (CombinedDomain i2 s2 p2) = 
        CombinedDomain 
            (Map.intersectionWith meet i1 i2)
            (Map.intersectionWith meet s1 s2)
            (Map.intersectionWith meet p1 p2)
    
    join (CombinedDomain i1 s1 p1) (CombinedDomain i2 s2 p2) = 
        CombinedDomain 
            (Map.unionWith join i1 i2)
            (Map.unionWith join s1 s2)
            (Map.unionWith join p1 p2)
    
    leq (CombinedDomain i1 s1 p1) (CombinedDomain i2 s2 p2) = 
        all (\(k, v) -> Map.lookup k i2 == Just v && leq v (Map.findWithDefault top k i2)) (Map.toList i1) &&
        all (\(k, v) -> Map.lookup k s2 == Just v && leq v (Map.findWithDefault top k s2)) (Map.toList s1) &&
        all (\(k, v) -> Map.lookup k p2 == Just v && leq v (Map.findWithDefault top k p2)) (Map.toList p1)
```

## 📚 理论基础

### 数学基础

抽象域基于以下数学基础：

1. **格论**：完全格、单调函数、不动点理论
2. **序理论**：偏序关系、上确界、下确界
3. **域理论**：连续函数、不动点定理

### 算法基础

抽象解释的核心算法包括：

1. **不动点计算**：使用扩宽和缩窄操作
2. **抽象求值**：在抽象域上计算表达式
3. **状态转换**：抽象状态的转换规则

### 应用领域

抽象域的应用领域：

1. **静态分析**：程序性质分析
2. **编译器优化**：代码优化和转换
3. **程序验证**：程序正确性验证

## 🔗 相关链接

- [扩宽-缩窄](02-Widening-Narrowing.md)
- [不动点计算](03-Fixpoint-Computation.md)
- [静态分析](04-Static-Analysis.md)
- [形式化方法](../README.md)

---

*本文档提供了抽象域的完整介绍，包括形式化定义、Haskell实现和应用示例。* 