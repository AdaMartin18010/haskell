# Petri网标记与变迁规则

## 📋 概述

标记(Marking)和变迁规则(Transition Rules)是Petri网的核心概念。标记表示系统的当前状态，变迁规则定义了系统如何从一个状态转移到另一个状态。

## 🏗️ 形式化定义

### 标记(Marking)

标记是库所到自然数的映射：$M: P \rightarrow \mathbb{N}$

- $M(p)$ 表示库所 $p$ 中的托肯(token)数量
- 初始标记 $M_0$ 是系统的起始状态
- 可达标记是从初始标记通过变迁序列可达的所有标记

### 变迁规则

对于变迁 $t \in T$，其前置集合和后置集合定义为：

- **前置集合**：$^\bullet t = \{p \in P | (p,t) \in F\}$
- **后置集合**：$t^\bullet = \{p \in P | (t,p) \in F\}$

### 激发条件

变迁 $t$ 在标记 $M$ 下可激发的条件是：
$$\forall p \in ^\bullet t: M(p) \geq 1$$

### 激发结果

当变迁 $t$ 激发时，产生新标记 $M'$：
$$M'(p) = M(p) - |\{t\} \cap ^\bullet p| + |\{t\} \cap p^\bullet|$$

## 🔧 Haskell实现

### 标记操作

```haskell
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module PetriNet.Markings where

import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- 标记类型
type Marking = Map Place Natural

-- 标记操作
emptyMarking :: Marking
emptyMarking = Map.empty

-- 添加托肯
addTokens :: Place -> Natural -> Marking -> Marking
addTokens place count marking = Map.insertWith (+) place count marking

-- 移除托肯
removeTokens :: Place -> Natural -> Marking -> Marking
removeTokens place count marking = 
  case Map.lookup place marking of
    Just current -> 
      if current >= count 
      then Map.insert place (current - count) marking
      else marking  -- 托肯不足，不执行操作
    Nothing -> marking

-- 检查托肯数量
tokenCount :: Place -> Marking -> Natural
tokenCount place marking = Map.findWithDefault 0 place marking

-- 标记比较
markingLessThanOrEqual :: Marking -> Marking -> Bool
markingLessThanOrEqual m1 m2 = 
  all (\place -> tokenCount place m1 <= tokenCount place m2) 
      (Map.keysSet m1 `Set.union` Map.keysSet m2)

-- 标记相等
markingEqual :: Marking -> Marking -> Bool
markingEqual m1 m2 = m1 == m2

-- 标记加法
markingAdd :: Marking -> Marking -> Marking
markingAdd m1 m2 = Map.unionWith (+) m1 m2

-- 标记减法（安全）
markingSubtract :: Marking -> Marking -> Maybe Marking
markingSubtract m1 m2 = 
  if markingLessThanOrEqual m2 m1
  then Just $ Map.unionWith (\a b -> if a >= b then a - b else 0) m1 m2
  else Nothing
```

### 变迁规则实现

```haskell
-- 前置和后置集合
preSet :: PetriNet -> Transition -> Set Place
preSet pn t = Set.fromList [p | PlaceToTransition p t' <- Set.toList (flowRelation pn), t' == t]

postSet :: PetriNet -> Transition -> Set Place
postSet pn t = Set.fromList [p | TransitionToPlace t' p <- Set.toList (flowRelation pn), t' == t]

-- 检查变迁是否可激发
isEnabled :: PetriNet -> Transition -> Marking -> Bool
isEnabled pn t marking = 
  let prePlaces = preSet pn t
  in all (\p -> tokenCount p marking > 0) prePlaces

-- 计算激发所需的托肯
requiredTokens :: PetriNet -> Transition -> Marking
requiredTokens pn t = 
  let prePlaces = preSet pn t
  in Map.fromSet (const 1) prePlaces

-- 计算激发产生的托肯
producedTokens :: PetriNet -> Transition -> Marking
producedTokens pn t = 
  let postPlaces = postSet pn t
  in Map.fromSet (const 1) postPlaces

-- 激发变迁
fireTransition :: PetriNet -> Transition -> Marking -> Maybe Marking
fireTransition pn t marking
  | not (isEnabled pn t marking) = Nothing
  | otherwise = Just $ newMarking
  where
    required = requiredTokens pn t
    produced = producedTokens pn t
    afterRemoval = markingSubtract marking required
    newMarking = case afterRemoval of
      Just m -> markingAdd m produced
      Nothing -> marking  -- 不应该发生，因为已经检查了可激发性
```

### 高级标记操作

```haskell
-- 标记覆盖
markingCovers :: Marking -> Marking -> Bool
markingCovers m1 m2 = markingLessThanOrEqual m2 m1

-- 标记并集
markingUnion :: Marking -> Marking -> Marking
markingUnion m1 m2 = Map.unionWith max m1 m2

-- 标记交集
markingIntersection :: Marking -> Marking -> Marking
markingIntersection m1 m2 = Map.intersectionWith min m1 m2

-- 标记差集
markingDifference :: Marking -> Marking -> Marking
markingDifference m1 m2 = 
  Map.differenceWith (\a b -> if a > b then Just (a - b) else Nothing) m1 m2

-- 标记权重
markingWeight :: Marking -> Natural
markingWeight marking = sum (Map.elems marking)

-- 非零库所
nonZeroPlaces :: Marking -> Set Place
nonZeroPlaces marking = Map.keysSet (Map.filter (> 0) marking)

-- 零库所
zeroPlaces :: Marking -> Set Place
zeroPlaces marking = Map.keysSet (Map.filter (== 0) marking)
```

## 📊 变迁分析

### 变迁性质

```haskell
-- 变迁类型
data TransitionType
  = SourceTransition    -- 源变迁：只有输出
  | SinkTransition      -- 汇变迁：只有输入
  | InternalTransition  -- 内部变迁：既有输入又有输出
  deriving (Eq, Show)

-- 确定变迁类型
transitionType :: PetriNet -> Transition -> TransitionType
transitionType pn t
  | Set.null pre && not (Set.null post) = SourceTransition
  | not (Set.null pre) && Set.null post = SinkTransition
  | otherwise = InternalTransition
  where
    pre = preSet pn t
    post = postSet pn t

-- 变迁冲突
conflictingTransitions :: PetriNet -> Marking -> Set Transition
conflictingTransitions pn marking = 
  let enabled = Set.fromList [t | t <- Set.toList (transitions pn), isEnabled pn t marking]
      conflicts = Set.fromList [t1 | t1 <- Set.toList enabled, 
                                   t2 <- Set.toList enabled,
                                   t1 /= t2,
                                   not (Set.disjoint (preSet pn t1) (preSet pn t2))]
  in conflicts

-- 并发变迁
concurrentTransitions :: PetriNet -> Marking -> Set Transition
concurrentTransitions pn marking = 
  let enabled = Set.fromList [t | t <- Set.toList (transitions pn), isEnabled pn t marking]
      conflicts = conflictingTransitions pn marking
  in enabled `Set.difference` conflicts
```

### 变迁序列

```haskell
-- 变迁序列
type TransitionSequence = [Transition]

-- 执行变迁序列
executeSequence :: PetriNet -> TransitionSequence -> Marking -> Maybe Marking
executeSequence pn [] marking = Just marking
executeSequence pn (t:ts) marking = 
  case fireTransition pn t marking of
    Just newMarking -> executeSequence pn ts newMarking
    Nothing -> Nothing

-- 可达的变迁序列
reachableSequences :: PetriNet -> Int -> [[Transition]]
reachableSequences pn maxLength = 
  reachableSequences' pn maxLength (initialMarking pn) [[]]

reachableSequences' :: PetriNet -> Int -> Marking -> [[Transition]] -> [[Transition]]
reachableSequences' pn maxLength currentMarking sequences
  | maxLength <= 0 = sequences
  | otherwise = 
      let enabled = [t | t <- Set.toList (transitions pn), isEnabled pn t currentMarking]
          newSequences = [seq ++ [t] | seq <- sequences, t <- enabled]
          nextMarkings = [m | t <- enabled, Just m <- [fireTransition pn t currentMarking]]
          allSequences = sequences ++ newSequences
      in concat [reachableSequences' pn (maxLength - 1) m allSequences | m <- nextMarkings]
```

## 🎯 应用示例

### 生产者-消费者系统

```haskell
-- 生产者-消费者系统的标记变化
producerConsumerMarkings :: [Marking]
producerConsumerMarkings = 
  let p1 = Place "producer_ready"
      p2 = Place "buffer"
      p3 = Place "consumer_ready"
      p4 = Place "consumed"
      t1 = Transition "produce"
      t2 = Transition "consume"
      t3 = Transition "consume_ready"
      t4 = Transition "producer_ready"
      
      initial = Map.fromList [(p1, 1), (p2, 0), (p3, 1), (p4, 0)]
      
      -- 执行序列：produce -> consume -> consume_ready -> producer_ready
      m1 = fireTransition producerConsumerNet t1 initial
      m2 = case m1 of Just m -> fireTransition producerConsumerNet t2 m; Nothing -> Nothing
      m3 = case m2 of Just m -> fireTransition producerConsumerNet t3 m; Nothing -> Nothing
      m4 = case m3 of Just m -> fireTransition producerConsumerNet t4 m; Nothing -> Nothing
      
  in [initial] ++ catMaybes [m1, m2, m3, m4]

-- 验证标记序列
verifyMarkingSequence :: [Marking] -> Bool
verifyMarkingSequence [] = True
verifyMarkingSequence [_] = True
verifyMarkingSequence (m1:m2:ms) = 
  let reachable = reachableMarkings producerConsumerNet
  in m2 `Set.member` reachable && verifyMarkingSequence (m2:ms)
```

### 互斥系统

```haskell
-- 互斥系统的标记分析
mutualExclusionAnalysis :: PetriNet -> Marking -> Bool
mutualExclusionAnalysis pn marking = 
  let p1 = Place "process1_critical"
      p2 = Place "process2_critical"
      critical1 = tokenCount p1 marking
      critical2 = tokenCount p2 marking
  in critical1 + critical2 <= 1  -- 互斥条件

-- 验证所有可达标记都满足互斥条件
verifyMutualExclusion :: PetriNet -> Bool
verifyMutualExclusion pn = 
  all (mutualExclusionAnalysis pn) (reachableMarkings pn)
```

## 🔍 形式化验证

### 标记不变式

```haskell
-- 不变式检查
checkInvariant :: PetriNet -> (Marking -> Bool) -> Bool
checkInvariant pn invariant = all invariant (reachableMarkings pn)

-- 托肯守恒不变式
tokenConservationInvariant :: PetriNet -> Marking -> Bool
tokenConservationInvariant pn marking = 
  let totalTokens = markingWeight marking
      initialTokens = markingWeight (initialMarking pn)
  in totalTokens == initialTokens

-- 库所有界性检查
placeBoundedness :: PetriNet -> Place -> Natural -> Bool
placeBoundedness pn place bound = 
  all (\marking -> tokenCount place marking <= bound) (reachableMarkings pn)

-- 检查所有库所都有界
allPlacesBounded :: PetriNet -> Bool
allPlacesBounded pn = 
  all (\place -> placeBoundedness pn place maxBound) (places pn)
```

### 变迁活性

```haskell
-- 变迁活性检查
transitionLiveness :: PetriNet -> Transition -> Bool
transitionLiveness pn t = 
  all (\marking -> canFireEventually pn t marking) (reachableMarkings pn)

-- 检查变迁最终可激发
canFireEventually :: PetriNet -> Transition -> Marking -> Bool
canFireEventually pn t marking = 
  let reachableFromMarking = reachableFromMarking pn marking
  in any (\m -> isEnabled pn t m) reachableFromMarking

-- 所有变迁都活性
allTransitionsLive :: PetriNet -> Bool
allTransitionsLive pn = all (\t -> transitionLiveness pn t) (transitions pn)
```

## 📈 性能分析

### 标记空间分析

```haskell
-- 标记空间统计
markingSpaceStats :: PetriNet -> (Int, Int, Int)
markingSpaceStats pn = (totalMarkings, maxTokens, avgTokens)
  where
    reachable = reachableMarkings pn
    totalMarkings = Set.size reachable
    maxTokens = maximum [markingWeight m | m <- Set.toList reachable]
    avgTokens = sum [markingWeight m | m <- Set.toList reachable] `div` totalMarkings

-- 标记分布分析
markingDistribution :: PetriNet -> Map Natural Int
markingDistribution pn = 
  let reachable = reachableMarkings pn
      weights = [markingWeight m | m <- Set.toList reachable]
  in Map.fromListWith (+) [(w, 1) | w <- weights]

-- 库所使用频率
placeUsageFrequency :: PetriNet -> Map Place Int
placeUsageFrequency pn = 
  let reachable = reachableMarkings pn
      usage = [place | m <- Set.toList reachable, 
                     place <- Map.keys (Map.filter (> 0) m)]
  in Map.fromListWith (+) [(p, 1) | p <- usage]
```

## 🎯 总结

Petri网的标记与变迁规则为并发系统建模提供了强大的形式化工具：

1. **标记表示**：精确表示系统状态
2. **变迁规则**：严格定义状态转换
3. **激发条件**：确保系统行为的一致性
4. **形式化验证**：支持系统性质的验证
5. **性能分析**：提供系统行为的量化分析

这些概念为Petri网的分析和应用奠定了坚实的基础。

---

*本文档提供了Petri网标记与变迁规则的完整形式化定义和Haskell实现。*
