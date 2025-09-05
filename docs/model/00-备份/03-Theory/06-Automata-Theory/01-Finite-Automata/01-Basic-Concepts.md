# 有限自动机基本概念

## 📋 概述

有限自动机(Finite Automaton)是最基本的自动机模型，用于识别正则语言。它由有限个状态组成，根据输入符号在状态间转移。

## 🏗️ 形式化定义

### 有限自动机

一个有限自动机是一个五元组 $A = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

### 数学表示

```haskell
-- 有限自动机的基本定义
data FiniteAutomaton = FiniteAutomaton
  { states :: Set State
  , alphabet :: Set Symbol
  , transition :: Map (State, Symbol) State
  , initialState :: State
  , acceptingStates :: Set State
  }

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

module Automata.Finite where

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

-- 转移函数
type TransitionFunction = Map (State, Symbol) State

-- 有限自动机
data FiniteAutomaton = FiniteAutomaton
  { states :: Set State
  , alphabet :: Set Symbol
  , transition :: TransitionFunction
  , initialState :: State
  , acceptingStates :: Set State
  }
  deriving (Eq, Show, Generic)

-- 计算转移
computeTransition :: FiniteAutomaton -> State -> Symbol -> Maybe State
computeTransition fa state symbol = Map.lookup (state, symbol) (transition fa)

-- 扩展转移函数（处理字符串）
extendedTransition :: FiniteAutomaton -> State -> [Symbol] -> State
extendedTransition fa q [] = q
extendedTransition fa q (s:ss) = 
  case computeTransition fa q s of
    Just q' -> extendedTransition fa q' ss
    Nothing -> q  -- 未定义转移时保持当前状态

-- 语言接受
accepts :: FiniteAutomaton -> [Symbol] -> Bool
accepts fa input = 
  let finalState = extendedTransition fa (initialState fa) input
  in finalState `Set.member` acceptingStates fa
```

### 确定性有限自动机(DFA)

```haskell
-- DFA是转移函数完全定义的有限自动机
isDFA :: FiniteAutomaton -> Bool
isDFA fa = all (\q -> all (\s -> Map.member (q, s) (transition fa)) (alphabet fa)) (states fa)

-- 构造DFA
makeDFA :: Set State -> Set Symbol -> TransitionFunction -> State -> Set State -> FiniteAutomaton
makeDFA states alphabet transition initial accepting = FiniteAutomaton
  { states = states
  , alphabet = alphabet
  , transition = transition
  , initialState = initial
  , acceptingStates = accepting
  }

-- DFA最小化
minimizeDFA :: FiniteAutomaton -> FiniteAutomaton
minimizeDFA fa = 
  let equivalentStates = findEquivalentStates fa
      minimizedStates = Set.fromList [representative s equivalentStates | s <- Set.toList (states fa)]
      minimizedTransition = minimizeTransition fa equivalentStates
      minimizedAccepting = Set.fromList [representative s equivalentStates | s <- Set.toList (acceptingStates fa)]
  in FiniteAutomaton
      { states = minimizedStates
      , alphabet = alphabet fa
      , transition = minimizedTransition
      , initialState = representative (initialState fa) equivalentStates
      , acceptingStates = minimizedAccepting
      }

-- 寻找等价状态
findEquivalentStates :: FiniteAutomaton -> Map State State
findEquivalentStates fa = 
  let initialPartition = partitionByAcceptance fa
      refinedPartition = refinePartition fa initialPartition
  in buildEquivalenceMap refinedPartition

-- 按接受性分区
partitionByAcceptance :: FiniteAutomaton -> [[State]]
partitionByAcceptance fa = 
  [Set.toList (acceptingStates fa), 
   Set.toList (states fa `Set.difference` acceptingStates fa)]

-- 精化分区
refinePartition :: FiniteAutomaton -> [[State]] -> [[State]]
refinePartition fa partition = 
  let newPartition = concatMap (splitByTransitions fa partition) partition
  in if newPartition == partition 
     then partition 
     else refinePartition fa newPartition

-- 按转移行为分割状态
splitByTransitions :: FiniteAutomaton -> [[State]] -> [State] -> [[State]]
splitByTransitions fa partition states = 
  let groups = groupBy (\s1 s2 -> sameTransitions fa partition s1 s2) states
  in groups

-- 检查两个状态是否有相同的转移行为
sameTransitions :: FiniteAutomaton -> [[State]] -> State -> State -> Bool
sameTransitions fa partition s1 s2 = 
  all (\symbol -> 
    let next1 = computeTransition fa s1 symbol
        next2 = computeTransition fa s2 symbol
    in case (next1, next2) of
         (Just n1, Just n2) -> samePartition partition n1 n2
         (Nothing, Nothing) -> True
         _ -> False
  ) (alphabet fa)

-- 检查两个状态是否在同一分区
samePartition :: [[State]] -> State -> State -> Bool
samePartition partition s1 s2 = 
  any (\group -> s1 `elem` group && s2 `elem` group) partition

-- 构建等价映射
buildEquivalenceMap :: [[State]] -> Map State State
buildEquivalenceMap partition = 
  Map.fromList [(s, head group) | group <- partition, s <- group]

-- 找到状态的代表
representative :: State -> Map State State -> State
representative state equivMap = Map.findWithDefault state state equivMap

-- 最小化转移函数
minimizeTransition :: FiniteAutomaton -> Map State State -> TransitionFunction
minimizeTransition fa equivMap = 
  Map.fromList [((representative s1 equivMap, symbol), representative s2 equivMap)
               | ((s1, symbol), s2) <- Map.toList (transition fa)]
```

### 非确定性有限自动机(NFA)

```haskell
-- NFA的转移函数返回状态集合
type NFATransitionFunction = Map (State, Symbol) (Set State)

-- NFA定义
data NondeterministicFiniteAutomaton = NFA
  { nfaStates :: Set State
  , nfaAlphabet :: Set Symbol
  , nfaTransition :: NFATransitionFunction
  , nfaInitialState :: State
  , nfaAcceptingStates :: Set State
  }
  deriving (Eq, Show, Generic)

-- NFA转移计算
nfaComputeTransition :: NondeterministicFiniteAutomaton -> State -> Symbol -> Set State
nfaComputeTransition nfa state symbol = 
  Map.findWithDefault Set.empty (state, symbol) (nfaTransition nfa)

-- NFA扩展转移
nfaExtendedTransition :: NondeterministicFiniteAutomaton -> Set State -> [Symbol] -> Set State
nfaExtendedTransition nfa currentStates [] = currentStates
nfaExtendedTransition nfa currentStates (s:ss) = 
  let nextStates = Set.unions [nfaComputeTransition nfa q s | q <- Set.toList currentStates]
  in nfaExtendedTransition nfa nextStates ss

-- NFA语言接受
nfaAccepts :: NondeterministicFiniteAutomaton -> [Symbol] -> Bool
nfaAccepts nfa input = 
  let finalStates = nfaExtendedTransition nfa (Set.singleton (nfaInitialState nfa)) input
  in not (Set.null (finalStates `Set.intersection` nfaAcceptingStates nfa))

-- NFA到DFA的转换（子集构造法）
nfaToDFA :: NondeterministicFiniteAutomaton -> FiniteAutomaton
nfaToDFA nfa = 
  let dfaStates = generateDFAStates nfa
      dfaTransition = generateDFATransition nfa dfaStates
      dfaInitialState = Set.singleton (nfaInitialState nfa)
      dfaAcceptingStates = Set.fromList [s | s <- Set.toList dfaStates, 
                                            not (Set.null (s `Set.intersection` nfaAcceptingStates nfa))]
  in FiniteAutomaton
      { states = dfaStates
      , alphabet = nfaAlphabet nfa
      , transition = dfaTransition
      , initialState = dfaInitialState
      , acceptingStates = dfaAcceptingStates
      }

-- 生成DFA状态（NFA状态的幂集）
generateDFAStates :: NondeterministicFiniteAutomaton -> Set (Set State)
generateDFAStates nfa = 
  let allStates = Set.toList (nfaStates nfa)
      powerSet = generatePowerSet allStates
  in Set.fromList [Set.fromList subset | subset <- powerSet]

-- 生成幂集
generatePowerSet :: [a] -> [[a]]
generatePowerSet [] = [[]]
generatePowerSet (x:xs) = 
  let rest = generatePowerSet xs
  in rest ++ map (x:) rest

-- 生成DFA转移函数
generateDFATransition :: NondeterministicFiniteAutomaton -> Set (Set State) -> TransitionFunction
generateDFATransition nfa dfaStates = 
  Map.fromList [((stateSet, symbol), nextStateSet)
               | stateSet <- Set.toList dfaStates
               , symbol <- Set.toList (nfaAlphabet nfa)
               , let nextStateSet = Set.unions [nfaComputeTransition nfa q symbol | q <- Set.toList stateSet]
               , not (Set.null nextStateSet)]
```

## 🎯 应用示例

### 简单模式识别

```haskell
-- 识别包含"ab"的字符串的DFA
abPatternDFA :: FiniteAutomaton
abPatternDFA = FiniteAutomaton
  { states = Set.fromList [q0, q1, q2]
  , alphabet = Set.fromList [a, b]
  , transition = Map.fromList
      [ ((q0, a), q1)
      , ((q0, b), q0)
      , ((q1, a), q1)
      , ((q1, b), q2)
      , ((q2, a), q2)
      , ((q2, b), q2)
      ]
  , initialState = q0
  , acceptingStates = Set.singleton q2
  }
  where
    q0 = State "q0"
    q1 = State "q1"
    q2 = State "q2"
    a = Symbol 'a'
    b = Symbol 'b'

-- 测试
testABPattern :: IO ()
testABPattern = do
  putStrLn "Testing ab pattern DFA:"
  putStrLn $ "ab: " ++ show (accepts abPatternDFA [Symbol 'a', Symbol 'b'])
  putStrLn $ "ba: " ++ show (accepts abPatternDFA [Symbol 'b', Symbol 'a'])
  putStrLn $ "aab: " ++ show (accepts abPatternDFA [Symbol 'a', Symbol 'a', Symbol 'b'])
  putStrLn $ "abb: " ++ show (accepts abPatternDFA [Symbol 'a', Symbol 'b', Symbol 'b'])
```

### 数字识别

```haskell
-- 识别偶数的DFA
evenNumberDFA :: FiniteAutomaton
evenNumberDFA = FiniteAutomaton
  { states = Set.fromList [even, odd]
  , alphabet = Set.fromList [zero, one]
  , transition = Map.fromList
      [ ((even, zero), even)
      , ((even, one), odd)
      , ((odd, zero), even)
      , ((odd, one), odd)
      ]
  , initialState = even
  , acceptingStates = Set.singleton even
  }
  where
    even = State "even"
    odd = State "odd"
    zero = Symbol '0'
    one = Symbol '1'

-- 测试偶数识别
testEvenNumber :: IO ()
testEvenNumber = do
  putStrLn "Testing even number DFA:"
  putStrLn $ "0: " ++ show (accepts evenNumberDFA [Symbol '0'])
  putStrLn $ "1: " ++ show (accepts evenNumberDFA [Symbol '1'])
  putStrLn $ "10: " ++ show (accepts evenNumberDFA [Symbol '1', Symbol '0'])
  putStrLn $ "11: " ++ show (accepts evenNumberDFA [Symbol '1', Symbol '1'])
```

## 🔍 形式化验证

### 自动机性质检查

```haskell
-- 检查自动机是否接受空语言
acceptsEmptyLanguage :: FiniteAutomaton -> Bool
acceptsEmptyLanguage fa = Set.null (acceptingStates fa)

-- 检查自动机是否接受所有字符串
acceptsAllStrings :: FiniteAutomaton -> Bool
acceptsAllStrings fa = acceptingStates fa == states fa

-- 检查自动机是否接受有限语言
acceptsFiniteLanguage :: FiniteAutomaton -> Bool
acceptsFiniteLanguage fa = 
  let reachableStates = findReachableStates fa
      hasCycle = hasCycleInAutomaton fa reachableStates
  in not hasCycle

-- 寻找可达状态
findReachableStates :: FiniteAutomaton -> Set State
findReachableStates fa = findReachableStates' fa (Set.singleton (initialState fa)) Set.empty

findReachableStates' :: FiniteAutomaton -> Set State -> Set State -> Set State
findReachableStates' fa frontier visited
  | Set.null frontier = visited
  | otherwise = findReachableStates' fa newFrontier (Set.union visited frontier)
  where
    newFrontier = Set.unions [nextStates fa s | s <- Set.toList frontier, s `Set.notMember` visited]

nextStates :: FiniteAutomaton -> State -> Set State
nextStates fa state = Set.fromList [next | symbol <- Set.toList (alphabet fa), 
                                          Just next <- [computeTransition fa state symbol]]

-- 检查是否有环
hasCycleInAutomaton :: FiniteAutomaton -> Set State -> Bool
hasCycleInAutomaton fa reachableStates = 
  any (\state -> hasCycleFromState fa state Set.empty) (Set.toList reachableStates)

hasCycleFromState :: FiniteAutomaton -> State -> Set State -> Bool
hasCycleFromState fa state visited
  | state `Set.member` visited = True
  | otherwise = any (\next -> hasCycleFromState fa next (Set.insert state visited)) 
                   (nextStates fa state)
```

## 📈 性能分析

### 复杂度分析

```haskell
-- 转移计算复杂度
transitionComplexity :: FiniteAutomaton -> Int
transitionComplexity fa = Map.size (transition fa)

-- 状态空间复杂度
stateSpaceComplexity :: FiniteAutomaton -> Int
stateSpaceComplexity fa = Set.size (states fa)

-- 最小化复杂度
minimizationComplexity :: FiniteAutomaton -> Int
minimizationComplexity fa = 
  let n = Set.size (states fa)
      m = Set.size (alphabet fa)
  in O(n^2 * m)  -- 简化表示

-- 语言接受复杂度
acceptanceComplexity :: FiniteAutomaton -> [Symbol] -> Int
acceptanceComplexity fa input = length input  -- 线性时间
```

## 🎯 总结

有限自动机基本概念为形式语言理论提供了坚实的基础：

1. **形式化定义**：严格的数学定义确保概念的精确性
2. **Haskell实现**：函数式编程提供了清晰的实现
3. **确定性vs非确定性**：两种模型各有优势和应用场景
4. **最小化算法**：优化自动机结构的重要技术
5. **应用验证**：通过具体示例验证理论的实用性

这些基本概念为后续的上下文无关语言和图灵机理论奠定了坚实的基础。

---

*本文档提供了有限自动机基本概念的完整形式化定义和Haskell实现。*
