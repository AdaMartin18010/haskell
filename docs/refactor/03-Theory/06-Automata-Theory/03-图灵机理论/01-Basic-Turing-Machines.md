# 基本图灵机理论

## 📋 概述

图灵机是计算理论的基础模型，由Alan Turing在1936年提出。它定义了什么是可计算的，为现代计算机科学奠定了理论基础。

## 🏗️ 形式化定义

### 基本图灵机

一个图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, q_{accept}, q_{reject})$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $q_{accept} \in Q$ 是接受状态
- $q_{reject} \in Q$ 是拒绝状态

### 数学表示

```haskell
-- 图灵机的基本定义
data TuringMachine = TuringMachine
  { states :: Set State
  , inputAlphabet :: Set Symbol
  , tapeAlphabet :: Set Symbol
  , transition :: Map (State, Symbol) (State, Symbol, Direction)
  , initialState :: State
  , acceptState :: State
  , rejectState :: State
  }

-- 移动方向
data Direction = Left | Right
  deriving (Eq, Show)

-- 状态和符号的标识符
newtype State = State { unState :: String }
  deriving (Eq, Ord, Show)

newtype Symbol = Symbol { unSymbol :: Char }
  deriving (Eq, Ord, Show)
```

## 🔧 Haskell实现

### 基本数据结构

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Automata.TuringMachine where

import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- 基本类型定义
data State = State { stateId :: Text }
  deriving (Eq, Ord, Show, Generic)

data Symbol = Symbol { symbolChar :: Char }
  deriving (Eq, Ord, Show, Generic)

data Direction = Left | Right
  deriving (Eq, Show, Generic)

-- 转移函数
type TransitionFunction = Map (State, Symbol) (State, Symbol, Direction)

-- 图灵机
data TuringMachine = TuringMachine
  { states :: Set State
  , inputAlphabet :: Set Symbol
  , tapeAlphabet :: Set Symbol
  , transition :: TransitionFunction
  , initialState :: State
  , acceptState :: State
  , rejectState :: State
  }
  deriving (Eq, Show, Generic)

-- 磁带表示
data Tape = Tape
  { leftTape :: [Symbol]    -- 头部左侧的符号
  , currentSymbol :: Symbol -- 当前符号
  , rightTape :: [Symbol]   -- 头部右侧的符号
  }
  deriving (Eq, Show, Generic)

-- 图灵机配置
data Configuration = Configuration
  { currentState :: State
  , tape :: Tape
  }
  deriving (Eq, Show, Generic)
```

### 磁带操作

```haskell
-- 创建初始磁带
initialTape :: [Symbol] -> Tape
initialTape input = Tape
  { leftTape = []
  , currentSymbol = head input
  , rightTape = tail input
  }

-- 移动磁带头部
moveTape :: Direction -> Tape -> Tape
moveTape Left tape = Tape
  { leftTape = init (leftTape tape)
  , currentSymbol = last (leftTape tape)
  , rightTape = currentSymbol tape : rightTape tape
  }
moveTape Right tape = Tape
  { leftTape = currentSymbol tape : leftTape tape
  , currentSymbol = head (rightTape tape)
  , rightTape = tail (rightTape tape)
  }

-- 写入符号
writeSymbol :: Symbol -> Tape -> Tape
writeSymbol symbol tape = tape { currentSymbol = symbol }

-- 获取磁带内容
getTapeContent :: Tape -> [Symbol]
getTapeContent tape = reverse (leftTape tape) ++ [currentSymbol tape] ++ rightTape tape
```

### 图灵机执行

```haskell
-- 执行一步
step :: TuringMachine -> Configuration -> Maybe Configuration
step tm config = 
  case Map.lookup (currentState config, currentSymbol (tape config)) (transition tm) of
    Just (newState, newSymbol, direction) -> 
      let newTape = moveTape direction (writeSymbol newSymbol (tape config))
      in Just $ Configuration newState newTape
    Nothing -> Nothing

-- 执行多步
run :: TuringMachine -> Configuration -> [Configuration]
run tm config = 
  case step tm config of
    Just nextConfig -> config : run tm nextConfig
    Nothing -> [config]

-- 检查是否接受
isAccepted :: TuringMachine -> Configuration -> Bool
isAccepted tm config = currentState config == acceptState tm

-- 检查是否拒绝
isRejected :: TuringMachine -> Configuration -> Bool
isRejected tm config = currentState config == rejectState tm

-- 检查是否停机
isHalted :: TuringMachine -> Configuration -> Bool
isHalted tm config = isAccepted tm config || isRejected tm config

-- 运行图灵机
runTuringMachine :: TuringMachine -> [Symbol] -> Maybe Bool
runTuringMachine tm input = 
  let initialConfig = Configuration (initialState tm) (initialTape input)
      configurations = run tm initialConfig
      finalConfig = last configurations
  in if isAccepted tm finalConfig
     then Just True
     else if isRejected tm finalConfig
          then Just False
          else Nothing  -- 不停止
```

## 🎯 应用示例

### 识别回文

```haskell
-- 识别回文的图灵机
palindromeTM :: TuringMachine
palindromeTM = TuringMachine
  { states = Set.fromList [q0, q1, q2, q3, q4, qaccept, qreject]
  , inputAlphabet = Set.fromList [a, b]
  , tapeAlphabet = Set.fromList [a, b, blank, x]
  , transition = Map.fromList
      [ -- 初始状态：移动到最右端
        ((q0, a), (q0, a, Right))
      , ((q0, b), (q0, b, Right))
      , ((q0, blank), (q1, blank, Left))
      , -- 状态q1：比较两端
      , ((q1, a), (q2, x, Left))
      , ((q1, b), (q3, x, Left))
      , ((q1, x), (qaccept, x, Left))
      , -- 状态q2：寻找左端的a
      , ((q2, a), (q4, x, Right))
      , ((q2, b), (qreject, b, Left))
      , ((q2, x), (q2, x, Left))
      , -- 状态q3：寻找左端的b
      , ((q3, a), (qreject, a, Left))
      , ((q3, b), (q4, x, Right))
      , ((q3, x), (q3, x, Left))
      , -- 状态q4：移动到右端
      , ((q4, a), (q4, a, Right))
      , ((q4, b), (q4, b, Right))
      , ((q4, x), (q4, x, Right))
      , ((q4, blank), (q1, blank, Left))
      ]
  , initialState = q0
  , acceptState = qaccept
  , rejectState = qreject
  }
  where
    q0 = State "q0"
    q1 = State "q1"
    q2 = State "q2"
    q3 = State "q3"
    q4 = State "q4"
    qaccept = State "q_accept"
    qreject = State "q_reject"
    a = Symbol 'a'
    b = Symbol 'b'
    blank = Symbol ' '
    x = Symbol 'x'

-- 测试回文识别
testPalindrome :: IO ()
testPalindrome = do
  putStrLn "Testing palindrome Turing machine:"
  putStrLn $ "abba: " ++ show (runTuringMachine palindromeTM [Symbol 'a', Symbol 'b', Symbol 'b', Symbol 'a'])
  putStrLn $ "aba: " ++ show (runTuringMachine palindromeTM [Symbol 'a', Symbol 'b', Symbol 'a'])
  putStrLn $ "ab: " ++ show (runTuringMachine palindromeTM [Symbol 'a', Symbol 'b'])
```

### 加法计算

```haskell
-- 计算a+b的图灵机
additionTM :: TuringMachine
additionTM = TuringMachine
  { states = Set.fromList [q0, q1, q2, q3, qaccept]
  , inputAlphabet = Set.fromList [one, plus]
  , tapeAlphabet = Set.fromList [one, plus, blank]
  , transition = Map.fromList
      [ -- 初始状态：移动到第一个加数末尾
        ((q0, one), (q0, one, Right))
      , ((q0, plus), (q1, plus, Right))
      , -- 状态q1：移动到第二个加数末尾
      , ((q1, one), (q1, one, Right))
      , ((q1, blank), (q2, one, Left))
      , -- 状态q2：删除加号
      , ((q2, one), (q2, one, Left))
      , ((q2, plus), (q3, blank, Left))
      , -- 状态q3：移动到开始
      , ((q3, one), (q3, one, Left))
      , ((q3, blank), (qaccept, blank, Right))
      ]
  , initialState = q0
  , acceptState = qaccept
  , rejectState = q0  -- 不使用拒绝状态
  }
  where
    q0 = State "q0"
    q1 = State "q1"
    q2 = State "q2"
    q3 = State "q3"
    qaccept = State "q_accept"
    one = Symbol '1'
    plus = Symbol '+'
    blank = Symbol ' '

-- 测试加法
testAddition :: IO ()
testAddition = do
  putStrLn "Testing addition Turing machine:"
  putStrLn $ "1+1: " ++ show (runTuringMachine additionTM [Symbol '1', Symbol '+', Symbol '1'])
  putStrLn $ "11+1: " ++ show (runTuringMachine additionTM [Symbol '1', Symbol '1', Symbol '+', Symbol '1'])
```

## 🔍 形式化验证

### 图灵机性质

```haskell
-- 检查图灵机是否确定性
isDeterministic :: TuringMachine -> Bool
isDeterministic tm = 
  let transitions = Map.toList (transition tm)
      keys = map fst transitions
      uniqueKeys = Set.fromList keys
  in length keys == Set.size uniqueKeys

-- 检查图灵机是否完整
isComplete :: TuringMachine -> Bool
isComplete tm = 
  let allPairs = [(s, sym) | s <- Set.toList (states tm), 
                           sym <- Set.toList (tapeAlphabet tm)]
      definedPairs = Map.keysSet (transition tm)
      allPairsSet = Set.fromList allPairs
  in allPairsSet `Set.isSubsetOf` definedPairs

-- 检查图灵机是否有效
isValid :: TuringMachine -> Bool
isValid tm = 
  let stateValid = initialState tm `Set.member` states tm &&
                   acceptState tm `Set.member` states tm &&
                   rejectState tm `Set.member` states tm
      alphabetValid = inputAlphabet tm `Set.isSubsetOf` tapeAlphabet tm
      transitionValid = all (\((s, sym), (s', sym', _)) -> 
                               s `Set.member` states tm &&
                               s' `Set.member` states tm &&
                               sym `Set.member` tapeAlphabet tm &&
                               sym' `Set.member` tapeAlphabet tm)
                           (Map.toList (transition tm))
  in stateValid && alphabetValid && transitionValid
```

### 停机问题

```haskell
-- 停机问题：检查图灵机在给定输入上是否停机
haltsOnInput :: TuringMachine -> [Symbol] -> Bool
haltsOnInput tm input = 
  case runTuringMachine tm input of
    Just _ -> True
    Nothing -> False

-- 通用停机检测器（理论上不可实现）
universalHaltingDetector :: TuringMachine -> [Symbol] -> Bool
universalHaltingDetector tm input = 
  -- 这是一个理论上的函数，实际上不可计算
  -- 停机问题证明了不存在这样的算法
  undefined

-- 有界停机检测器（实际可实现）
boundedHaltingDetector :: TuringMachine -> [Symbol] -> Int -> Bool
boundedHaltingDetector tm input maxSteps = 
  let initialConfig = Configuration (initialState tm) (initialTape input)
      configurations = take maxSteps (run tm initialConfig)
      finalConfig = last configurations
  in isHalted tm finalConfig
```

## 📈 性能分析

### 复杂度分析

```haskell
-- 计算步数
stepCount :: TuringMachine -> [Symbol] -> Maybe Int
stepCount tm input = 
  let initialConfig = Configuration (initialState tm) (initialTape input)
      configurations = run tm initialConfig
  in if any (isHalted tm) configurations
     then Just (length configurations - 1)
     else Nothing

-- 空间复杂度
spaceComplexity :: TuringMachine -> [Symbol] -> Maybe Int
spaceComplexity tm input = 
  let initialConfig = Configuration (initialState tm) (initialTape input)
      configurations = run tm initialConfig
      tapeLengths = [length (getTapeContent (tape config)) | config <- configurations]
  in if any (isHalted tm) configurations
     then Just (maximum tapeLengths)
     else Nothing

-- 时间-空间权衡
timeSpaceTradeoff :: TuringMachine -> [Symbol] -> Maybe (Int, Int)
timeSpaceTradeoff tm input = 
  case (stepCount tm input, spaceComplexity tm input) of
    (Just steps, Just space) -> Just (steps, space)
    _ -> Nothing
```

## 🎯 总结

基本图灵机理论为计算理论提供了坚实的基础：

1. **形式化定义**：严格的数学定义确保概念的精确性
2. **Haskell实现**：函数式编程提供了清晰的实现
3. **应用示例**：通过具体示例验证理论的实用性
4. **形式化验证**：支持图灵机性质的验证
5. **复杂度分析**：提供计算复杂度的量化分析

这些基本概念为可计算性理论和复杂性理论奠定了坚实的基础。

---

*本文档提供了基本图灵机理论的完整形式化定义和Haskell实现。*
