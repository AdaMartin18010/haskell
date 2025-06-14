# Petri网基础概念与定义

## 📋 概述

Petri网是一种用于建模和分析并发系统的形式化工具，由Carl Adam Petri在1962年提出。它通过有向二分图来描述系统的状态和状态转换。

## 🏗️ 形式化定义

### 基本Petri网

一个Petri网是一个四元组 $PN = (P, T, F, M_0)$，其中：

- $P$ 是库所(places)的有限集合
- $T$ 是变迁(transitions)的有限集合
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系(flow relation)
- $M_0: P \rightarrow \mathbb{N}$ 是初始标记(initial marking)

### 数学表示

```haskell
-- Petri网的基本定义
data PetriNet = PetriNet
  { places :: Set Place
  , transitions :: Set Transition
  , flowRelation :: Set (Either (Place, Transition) (Transition, Place))
  , initialMarking :: Map Place Natural
  }

-- 库所和变迁的标识符
newtype Place = Place { unPlace :: String }
  deriving (Eq, Ord, Show)

newtype Transition = Transition { unTransition :: String }
  deriving (Eq, Ord, Show)

-- 标记函数
type Marking = Map Place Natural
```

## 🔧 Haskell实现

### 基本数据结构

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module PetriNet.Basic where

import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- 基本类型定义
data Place = Place { placeId :: Text }
  deriving (Eq, Ord, Show, Generic)

data Transition = Transition { transitionId :: Text }
  deriving (Eq, Ord, Show, Generic)

-- 流关系
data FlowRelation
  = PlaceToTransition Place Transition
  | TransitionToPlace Transition Place
  deriving (Eq, Ord, Show, Generic)

-- 标记
type Marking = Map Place Natural

-- Petri网
data PetriNet = PetriNet
  { places :: Set Place
  , transitions :: Set Transition
  , flowRelation :: Set FlowRelation
  , initialMarking :: Marking
  }
  deriving (Eq, Show, Generic)

-- 前置和后置集合
preSet :: PetriNet -> Transition -> Set Place
preSet pn t = Set.fromList [p | PlaceToTransition p t' <- Set.toList (flowRelation pn), t' == t]

postSet :: PetriNet -> Transition -> Set Place
postSet pn t = Set.fromList [p | TransitionToPlace t' p <- Set.toList (flowRelation pn), t' == t]

-- 检查变迁是否可激发
isEnabled :: PetriNet -> Transition -> Marking -> Bool
isEnabled pn t marking = all (\p -> Map.findWithDefault 0 p marking > 0) (preSet pn t)

-- 激发变迁
fireTransition :: PetriNet -> Transition -> Marking -> Maybe Marking
fireTransition pn t marking
  | not (isEnabled pn t marking) = Nothing
  | otherwise = Just $ newMarking
  where
    newMarking = Map.unionWith (+) 
      (Map.difference marking (Map.fromSet (const 1) (preSet pn t)))
      (Map.fromSet (const 1) (postSet pn t))
```

### 可达性分析

```haskell
-- 可达性分析
reachableMarkings :: PetriNet -> Set Marking
reachableMarkings pn = reachableMarkings' pn (Set.singleton (initialMarking pn)) Set.empty

reachableMarkings' :: PetriNet -> Set Marking -> Set Marking -> Set Marking
reachableMarkings' pn frontier visited
  | Set.null frontier = visited
  | otherwise = reachableMarkings' pn newFrontier (Set.union visited frontier)
  where
    newFrontier = Set.unions [nextMarkings pn m | m <- Set.toList frontier, m `Set.notMember` visited]

nextMarkings :: PetriNet -> Marking -> Set Marking
nextMarkings pn marking = Set.fromList 
  [m | t <- Set.toList (transitions pn), 
       Just m <- [fireTransition pn t marking]]

-- 可达性检查
isReachable :: PetriNet -> Marking -> Bool
isReachable pn target = target `Set.member` reachableMarkings pn
```

## 📊 基本性质

### 活性(Liveness)

```haskell
-- 活性定义
isLive :: PetriNet -> Bool
isLive pn = all (\t -> isTransitionLive pn t) (transitions pn)

isTransitionLive :: PetriNet -> Transition -> Bool
isTransitionLive pn t = all (\m -> canFireEventually pn t m) (reachableMarkings pn)

canFireEventually :: PetriNet -> Transition -> Marking -> Bool
canFireEventually pn t marking = 
  any (\m -> isEnabled pn t m) (reachableFromMarking pn marking)

reachableFromMarking :: PetriNet -> Marking -> Set Marking
reachableFromMarking pn start = reachableFromMarking' pn (Set.singleton start) Set.empty

reachableFromMarking' :: PetriNet -> Set Marking -> Set Marking -> Set Marking
reachableFromMarking' pn frontier visited
  | Set.null frontier = visited
  | otherwise = reachableFromMarking' pn newFrontier (Set.union visited frontier)
  where
    newFrontier = Set.unions [nextMarkings pn m | m <- Set.toList frontier, m `Set.notMember` visited]
```

### 有界性(Boundedness)

```haskell
-- 有界性检查
isBounded :: PetriNet -> Bool
isBounded pn = all (\p -> isPlaceBounded pn p) (places pn)

isPlaceBounded :: PetriNet -> Place -> Bool
isPlaceBounded pn p = 
  let maxTokens = maximum [Map.findWithDefault 0 p m | m <- Set.toList (reachableMarkings pn)]
  in maxTokens < maxBound

-- k-有界性
isKBounded :: PetriNet -> Natural -> Bool
isKBounded pn k = all (\p -> isPlaceKBounded pn p k) (places pn)

isPlaceKBounded :: PetriNet -> Place -> Natural -> Bool
isPlaceKBounded pn p k = all (\m -> Map.findWithDefault 0 p m <= k) (reachableMarkings pn)
```

## 🎯 应用示例

### 生产者-消费者系统

```haskell
-- 生产者-消费者Petri网
producerConsumerNet :: PetriNet
producerConsumerNet = PetriNet
  { places = Set.fromList [p1, p2, p3, p4]
  , transitions = Set.fromList [t1, t2, t3, t4]
  , flowRelation = Set.fromList
      [ PlaceToTransition p1 t1
      , TransitionToPlace t1 p2
      , PlaceToTransition p2 t2
      , TransitionToPlace t2 p3
      , PlaceToTransition p3 t3
      , TransitionToPlace t3 p4
      , PlaceToTransition p4 t4
      , TransitionToPlace t4 p1
      ]
  , initialMarking = Map.fromList [(p1, 1), (p2, 0), (p3, 1), (p4, 0)]
  }
  where
    p1 = Place "producer_ready"
    p2 = Place "buffer"
    p3 = Place "consumer_ready"
    p4 = Place "consumed"
    t1 = Transition "produce"
    t2 = Transition "consume"
    t3 = Transition "consume_ready"
    t4 = Transition "producer_ready"
```

### 互斥系统

```haskell
-- 互斥Petri网
mutualExclusionNet :: PetriNet
mutualExclusionNet = PetriNet
  { places = Set.fromList [p1, p2, p3, p4, p5]
  , transitions = Set.fromList [t1, t2, t3, t4]
  , flowRelation = Set.fromList
      [ PlaceToTransition p1 t1
      , TransitionToPlace t1 p2
      , PlaceToTransition p2 t2
      , TransitionToPlace t2 p3
      , PlaceToTransition p3 t3
      , TransitionToPlace t3 p4
      , PlaceToTransition p4 t4
      , TransitionToPlace t4 p1
      , PlaceToTransition p5 t1
      , PlaceToTransition p5 t3
      ]
  , initialMarking = Map.fromList [(p1, 1), (p2, 0), (p3, 1), (p4, 0), (p5, 1)]
  }
  where
    p1 = Place "process1_idle"
    p2 = Place "process1_critical"
    p3 = Place "process2_idle"
    p4 = Place "process2_critical"
    p5 = Place "mutex"
    t1 = Transition "enter1"
    t2 = Transition "exit1"
    t3 = Transition "enter2"
    t4 = Transition "exit2"
```

## 🔍 形式化验证

### 不变式验证

```haskell
-- 不变式检查
checkInvariant :: PetriNet -> (Marking -> Bool) -> Bool
checkInvariant pn invariant = all invariant (reachableMarkings pn)

-- 互斥不变式
mutualExclusionInvariant :: Marking -> Bool
mutualExclusionInvariant marking = 
  Map.findWithDefault 0 (Place "process1_critical") marking + 
  Map.findWithDefault 0 (Place "process2_critical") marking <= 1

-- 安全性检查
safetyCheck :: PetriNet -> (Marking -> Bool) -> Bool
safetyCheck pn safety = checkInvariant pn safety

-- 活性检查
livenessCheck :: PetriNet -> Bool
livenessCheck pn = isLive pn
```

## 📈 性能分析

### 状态空间分析

```haskell
-- 状态空间统计
stateSpaceStats :: PetriNet -> (Int, Int, Int)
stateSpaceStats pn = (totalStates, enabledTransitions, deadStates)
  where
    reachable = reachableMarkings pn
    totalStates = Set.size reachable
    enabledTransitions = sum [countEnabled pn m | m <- Set.toList reachable]
    deadStates = length [m | m <- Set.toList reachable, countEnabled pn m == 0]

countEnabled :: PetriNet -> Marking -> Int
countEnabled pn marking = length [t | t <- Set.toList (transitions pn), isEnabled pn t marking]

-- 覆盖树生成
coverabilityTree :: PetriNet -> Tree Marking
coverabilityTree pn = buildCoverabilityTree pn (initialMarking pn) Set.empty

data Tree a = Node a [Tree a]
  deriving (Show)

buildCoverabilityTree :: PetriNet -> Marking -> Set Marking -> Tree Marking
buildCoverabilityTree pn marking visited
  | marking `Set.member` visited = Node marking []
  | otherwise = Node marking children
  where
    children = [buildCoverabilityTree pn m (Set.insert marking visited) 
               | m <- nextMarkings pn marking]
```

## 🎯 总结

Petri网基础概念为并发系统建模提供了强大的形式化工具：

1. **形式化定义**：严格的数学定义确保概念的精确性
2. **Haskell实现**：函数式编程提供了清晰的实现
3. **性质分析**：活性、有界性等关键性质的形式化检查
4. **应用验证**：通过具体示例验证理论的实用性

这些基础概念为后续的高级Petri网理论和应用奠定了坚实的基础。

---

*本文档提供了Petri网基础概念的完整形式化定义和Haskell实现。*
