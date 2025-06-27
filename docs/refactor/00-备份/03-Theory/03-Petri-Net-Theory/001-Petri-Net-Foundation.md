# Petri网理论基础

## 📋 概述

Petri网是一种用于建模和分析并发系统的形式化工具。本文档介绍Petri网的基础理论，包括网结构、变迁规则、可达性分析、并发性分析和结构性质。

## 🎯 Petri网基础

### 定义 1.1 (Petri网)

Petri网是一个四元组 $N = (P, T, F, M_0)$，其中：

- $P$ 是有限的位置集合（places）
- $T$ 是有限的变迁集合（transitions）
- $F \subseteq (P \times T) \cup (T \times P)$ 是流关系（flow relation）
- $M_0 : P \rightarrow \mathbb{N}$ 是初始标识（initial marking）

```haskell
-- Petri网定义
data PetriNet = PetriNet
    { places :: Set Place
    , transitions :: Set Transition
    , flowRelation :: Set Flow
    , initialMarking :: Marking
    }

-- 位置和变迁
type Place = String
type Transition = String

-- 流关系
data Flow = 
    PlaceToTransition Place Transition
    | TransitionToPlace Transition Place
    deriving (Show, Eq, Ord)

-- 标识
type Marking = Map Place Int

-- 示例：简单Petri网
simplePetriNet :: PetriNet
simplePetriNet = PetriNet
    { places = Set.fromList ["p1", "p2", "p3"]
    , transitions = Set.fromList ["t1", "t2"]
    , flowRelation = Set.fromList 
        [ PlaceToTransition "p1" "t1"
        , TransitionToPlace "t1" "p2"
        , PlaceToTransition "p2" "t2"
        , TransitionToPlace "t2" "p3"
        ]
    , initialMarking = Map.fromList [("p1", 1), ("p2", 0), ("p3", 0)]
    }
```

### 定义 1.2 (标识)

标识 $M : P \rightarrow \mathbb{N}$ 表示每个位置中的托肯（token）数量。

### 定义 1.3 (前集和后集)

对于 $x \in P \cup T$：

- $^\bullet x = \{y \mid (y, x) \in F\}$ 是 $x$ 的前集
- $x^\bullet = \{y \mid (x, y) \in F\}$ 是 $x$ 的后集

```haskell
-- 前集和后集
preSet :: PetriNet -> Either Place Transition -> Set (Either Place Transition)
preSet net x = 
    let flows = flowRelation net
    in Set.fromList [case flow of
                       PlaceToTransition p t -> if Right t == x then Left p else error "No match"
                       TransitionToPlace t p -> if Left p == x then Right t else error "No match"
                    | flow <- Set.toList flows]

postSet :: PetriNet -> Either Place Transition -> Set (Either Place Transition)
postSet net x = 
    let flows = flowRelation net
    in Set.fromList [case flow of
                       PlaceToTransition p t -> if Left p == x then Right t else error "No match"
                       TransitionToPlace t p -> if Right t == x then Left p else error "No match"
                    | flow <- Set.toList flows]

-- 获取变迁的前集和后集
transitionPreSet :: PetriNet -> Transition -> Set Place
transitionPreSet net t = 
    let pre = preSet net (Right t)
    in Set.fromList [p | Left p <- Set.toList pre]

transitionPostSet :: PetriNet -> Transition -> Set Place
transitionPostSet net t = 
    let post = postSet net (Right t)
    in Set.fromList [p | Left p <- Set.toList post]
```

## 🔧 变迁规则

### 定义 1.4 (变迁使能)

变迁 $t \in T$ 在标识 $M$ 下使能，记作 $M[t\rangle$，当且仅当：
$$\forall p \in ^\bullet t : M(p) \geq F(p, t)$$

### 定义 1.5 (变迁发生)

如果 $M[t\rangle$，则变迁 $t$ 可以发生，产生新标识 $M'$，记作 $M[t\rangle M'$，其中：
$$M'(p) = M(p) - F(p, t) + F(t, p)$$

### 定理 1.1 (变迁发生保持托肯守恒)

对于任何变迁 $t$ 和标识 $M$，如果 $M[t\rangle M'$，则：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} M(p)$$

**证明：** 通过流关系的定义：
$$\sum_{p \in P} M'(p) = \sum_{p \in P} (M(p) - F(p, t) + F(t, p)) = \sum_{p \in P} M(p)$$

```haskell
-- 变迁使能检查
isEnabled :: PetriNet -> Marking -> Transition -> Bool
isEnabled net marking t = 
    let prePlaces = transitionPreSet net t
        requiredTokens = Map.fromList [(p, 1) | p <- Set.toList prePlaces]  -- 简化：每个输入位置需要1个托肯
    in all (\p -> Map.findWithDefault 0 p marking >= Map.findWithDefault 0 p requiredTokens) 
           (Set.toList prePlaces)

-- 变迁发生
fireTransition :: PetriNet -> Marking -> Transition -> Maybe Marking
fireTransition net marking t = 
    if isEnabled net marking t
    then Just $ updateMarking net marking t
    else Nothing

-- 更新标识
updateMarking :: PetriNet -> Marking -> Transition -> Marking
updateMarking net marking t = 
    let prePlaces = transitionPreSet net t
        postPlaces = transitionPostSet net t
        
        -- 移除输入托肯
        marking1 = foldl (\m p -> Map.insert p (Map.findWithDefault 0 p m - 1) m) marking prePlaces
        
        -- 添加输出托肯
        marking2 = foldl (\m p -> Map.insert p (Map.findWithDefault 0 p m + 1) m) marking1 postPlaces
    in marking2

-- 托肯守恒检查
tokenConservation :: PetriNet -> Marking -> Transition -> Bool
tokenConservation net marking t = 
    case fireTransition net marking t of
        Just newMarking -> 
            let totalBefore = sum (Map.elems marking)
                totalAfter = sum (Map.elems newMarking)
            in totalBefore == totalAfter
        Nothing -> True  -- 如果变迁不能发生，则守恒性不适用
```

## 📊 可达性分析

### 定义 2.1 (可达性)

标识 $M'$ 从标识 $M$ 可达，记作 $M \rightarrow^* M'$，如果存在变迁序列 $\sigma = t_1 t_2 \cdots t_n$ 使得：
$$M[t_1\rangle M_1[t_2\rangle M_2 \cdots [t_n\rangle M'$$

### 定义 2.2 (可达集)

从标识 $M$ 可达的所有标识集合：
$$R(M) = \{M' \mid M \rightarrow^* M'\}$$

### 定理 2.1 (可达性保持)

如果 $M \rightarrow^* M'$ 且 $M'[t\rangle M''$，则 $M \rightarrow^* M''$。

**证明：** 通过可达性的传递性：

1. $M \rightarrow^* M'$ 存在变迁序列 $\sigma$
2. $M'[t\rangle M''$ 表示 $t$ 在 $M'$ 下使能
3. 因此 $M \rightarrow^* M''$ 通过序列 $\sigma t$

```haskell
-- 可达性分析
reachabilityAnalysis :: PetriNet -> [Marking]
reachabilityAnalysis net = 
    let initial = initialMarking net
        reachable = bfs initial [initial]
    in reachable
  where
    bfs :: Marking -> [Marking] -> [Marking]
    bfs current visited = 
        let enabled = enabledTransitions net current
            newMarkings = [m | t <- enabled, Just m <- [fireTransition net current t]]
            unvisited = filter (`notElem` visited) newMarkings
        in if null unvisited 
           then visited
           else bfs (head unvisited) (visited ++ unvisited)

-- 获取使能的变迁
enabledTransitions :: PetriNet -> Marking -> [Transition]
enabledTransitions net marking = 
    [t | t <- Set.toList (transitions net), isEnabled net marking t]

-- 可达性检查
isReachable :: PetriNet -> Marking -> Marking -> Bool
isReachable net from to = 
    let reachable = reachabilityAnalysis net
    in to `elem` reachable

-- 变迁序列
type TransitionSequence = [Transition]

-- 执行变迁序列
executeSequence :: PetriNet -> Marking -> TransitionSequence -> Maybe Marking
executeSequence net marking [] = Just marking
executeSequence net marking (t:ts) = do
    newMarking <- fireTransition net marking t
    executeSequence net newMarking ts
```

## 🔍 并发性分析

### 定义 3.1 (并发变迁)

两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下并发，记作 $M[t_1, t_2\rangle$，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 = \emptyset$（无共享输入位置）

### 定理 3.1 (并发交换性)

如果 $M[t_1, t_2\rangle$，则 $M[t_1\rangle M_1[t_2\rangle M'$ 且 $M[t_2\rangle M_2[t_1\rangle M'$，其中 $M_1 \neq M_2$ 但 $M'$ 相同。

**证明：** 通过并发变迁的定义：

1. 无共享输入位置确保独立性
2. 变迁发生顺序不影响最终结果
3. 中间标识可能不同但最终标识相同

```haskell
-- 并发变迁检查
areConcurrent :: PetriNet -> Marking -> Transition -> Transition -> Bool
areConcurrent net marking t1 t2 = 
    let enabled1 = isEnabled net marking t1
        enabled2 = isEnabled net marking t2
        pre1 = transitionPreSet net t1
        pre2 = transitionPreSet net t2
        noSharedInputs = Set.null (Set.intersection pre1 pre2)
    in enabled1 && enabled2 && noSharedInputs

-- 并发变迁发生
fireConcurrent :: PetriNet -> Marking -> Transition -> Transition -> Maybe Marking
fireConcurrent net marking t1 t2 = 
    if areConcurrent net marking t1 t2
    then do
        m1 <- fireTransition net marking t1
        fireTransition net m1 t2
    else Nothing

-- 并发交换性验证
concurrencyCommutativity :: PetriNet -> Marking -> Transition -> Transition -> Bool
concurrencyCommutativity net marking t1 t2 = 
    if areConcurrent net marking t1 t2
    then 
        let result1 = fireConcurrent net marking t1 t2
            result2 = fireConcurrent net marking t2 t1
        in result1 == result2
    else True  -- 如果不并发，则交换性不适用
```

### 定义 3.2 (冲突)

两个变迁 $t_1, t_2 \in T$ 在标识 $M$ 下冲突，当且仅当：

1. $M[t_1\rangle$ 且 $M[t_2\rangle$
2. $^\bullet t_1 \cap ^\bullet t_2 \neq \emptyset$（有共享输入位置）

### 定理 3.2 (冲突解决)

如果 $t_1, t_2$ 在 $M$ 下冲突，则最多只能发生其中一个变迁。

**证明：** 通过冲突定义：

1. 共享输入位置限制托肯数量
2. 一个变迁的发生会消耗共享托肯
3. 另一个变迁将不再使能

```haskell
-- 冲突检查
areConflicting :: PetriNet -> Marking -> Transition -> Transition -> Bool
areConflicting net marking t1 t2 = 
    let enabled1 = isEnabled net marking t1
        enabled2 = isEnabled net marking t2
        pre1 = transitionPreSet net t1
        pre2 = transitionPreSet net t2
        sharedInputs = Set.intersection pre1 pre2
    in enabled1 && enabled2 && not (Set.null sharedInputs)

-- 冲突解决
resolveConflict :: PetriNet -> Marking -> Transition -> Transition -> Maybe Transition
resolveConflict net marking t1 t2 = 
    if areConflicting net marking t1 t2
    then Just t1  -- 选择第一个变迁（实际应用中可能有更复杂的策略）
    else Nothing
```

## 📈 结构性质

### 定义 4.1 (有界性)

位置 $p \in P$ 是 $k$-有界的，如果对于所有可达标识 $M \in R(M_0)$，都有 $M(p) \leq k$。

### 定义 4.2 (安全Petri网)

Petri网是安全的，如果所有位置都是1-有界的。

### 定理 4.1 (有界性判定)

位置 $p$ 是 $k$-有界的当且仅当在状态空间中 $M(p) \leq k$ 对所有可达标识 $M$ 成立。

```haskell
-- 有界性检查
isBounded :: PetriNet -> Place -> Int -> Bool
isBounded net p k = 
    let reachable = reachabilityAnalysis net
        maxTokens = maximum [Map.findWithDefault 0 p marking | marking <- reachable]
    in maxTokens <= k

-- 安全Petri网检查
isSafe :: PetriNet -> Bool
isSafe net = 
    let allPlaces = Set.toList (places net)
    in all (\p -> isBounded net p 1) allPlaces

-- 获取位置的有界性
getBoundedness :: PetriNet -> Place -> Int
getBoundedness net p = 
    let reachable = reachabilityAnalysis net
        maxTokens = maximum [Map.findWithDefault 0 p marking | marking <- reachable]
    in maxTokens
```

### 定义 4.3 (活性)

变迁 $t \in T$ 是活的，如果对于每个可达标识 $M \in R(M_0)$，都存在标识 $M' \in R(M)$ 使得 $M'[t\rangle$。

### 定义 4.4 (死锁)

标识 $M$ 是死锁，如果没有变迁在 $M$ 下使能。

### 定理 4.2 (活性保持)

如果所有变迁都是活的，则Petri网不会出现死锁。

**证明：** 通过活性定义：

1. 每个变迁在任何可达标识后都能再次使能
2. 不存在所有变迁都无法使能的标识
3. 因此不会出现死锁

```haskell
-- 活性检查
isLive :: PetriNet -> Transition -> Bool
isLive net t = 
    let reachable = reachabilityAnalysis net
        canFireFrom marking = any (\m -> isEnabled net m t) (reachableFrom net marking)
    in all canFireFrom reachable

-- 从给定标识可达的所有标识
reachableFrom :: PetriNet -> Marking -> [Marking]
reachableFrom net marking = 
    let allReachable = reachabilityAnalysis net
        startIndex = case elemIndex marking allReachable of
            Just i -> i
            Nothing -> 0
    in drop startIndex allReachable

-- 死锁检查
isDeadlock :: PetriNet -> Marking -> Bool
isDeadlock net marking = 
    let enabled = enabledTransitions net marking
    in null enabled

-- 死锁检测
hasDeadlock :: PetriNet -> Bool
hasDeadlock net = 
    let reachable = reachabilityAnalysis net
    in any (isDeadlock net) reachable
```

### 定义 4.5 (可逆性)

Petri网是可逆的，如果对于每个可达标识 $M \in R(M_0)$，都有 $M \rightarrow^* M_0$。

### 定理 4.3 (可逆性判定)

Petri网是可逆的当且仅当初始标识 $M_0$ 在状态空间中是强连通的。

```haskell
-- 可逆性检查
isReversible :: PetriNet -> Bool
isReversible net = 
    let reachable = reachabilityAnalysis net
        initial = initialMarking net
    in all (\marking -> isReachable net marking initial) reachable

-- 强连通性检查
isStronglyConnected :: PetriNet -> Bool
isStronglyConnected net = 
    let reachable = reachabilityAnalysis net
        allPairs = [(m1, m2) | m1 <- reachable, m2 <- reachable]
    in all (\(m1, m2) -> isReachable net m1 m2) allPairs
```

## 🔧 高级Petri网

### 定义 5.1 (时间Petri网)

时间Petri网是六元组 $N = (P, T, F, M_0, I, D)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $I : T \rightarrow \mathbb{R}^+ \times \mathbb{R}^+$ 是时间间隔函数
- $D : T \rightarrow \mathbb{R}^+$ 是持续时间函数

```haskell
-- 时间Petri网
data TimedPetriNet = TimedPetriNet
    { baseNet :: PetriNet
    , timeIntervals :: Map Transition (Double, Double)
    , durations :: Map Transition Double
    }

-- 时间变迁发生
fireTimedTransition :: TimedPetriNet -> Marking -> Transition -> Double -> Maybe Marking
fireTimedTransition timedNet marking t time = 
    let net = baseNet timedNet
        interval = Map.findWithDefault (0, infinity) t (timeIntervals timedNet)
        (minTime, maxTime) = interval
    in if time >= minTime && time <= maxTime
       then fireTransition net marking t
       else Nothing
  where
    infinity = 1e10
```

### 定义 5.2 (着色Petri网)

着色Petri网是五元组 $N = (P, T, F, M_0, C)$，其中：

- $(P, T, F, M_0)$ 是基础Petri网
- $C : P \cup T \rightarrow \text{Type}$ 是颜色函数

```haskell
-- 着色Petri网
data ColoredPetriNet a = ColoredPetriNet
    { baseNet :: PetriNet
    , colorFunction :: Map (Either Place Transition) a
    }

-- 着色标识
type ColoredMarking a = Map Place [a]

-- 着色变迁发生
fireColoredTransition :: (Eq a) => ColoredPetriNet a -> ColoredMarking a -> Transition -> Maybe (ColoredMarking a)
fireColoredTransition coloredNet marking t = 
    let net = baseNet coloredNet
        prePlaces = transitionPreSet net t
        postPlaces = transitionPostSet net t
        
        -- 检查输入托肯
        canFire = all (\p -> not (null (Map.findWithDefault [] p marking))) prePlaces
        
        -- 执行变迁
        if canFire
        then Just $ updateColoredMarking coloredNet marking t
        else Nothing
  where
    updateColoredMarking coloredNet marking t = 
        let net = baseNet coloredNet
            prePlaces = transitionPreSet net t
            postPlaces = transitionPostSet net t
            
            -- 移除输入托肯
            marking1 = foldl (\m p -> Map.insert p (tail (Map.findWithDefault [] p m)) m) marking prePlaces
            
            -- 添加输出托肯
            tokenColor = head (Map.findWithDefault [] (head (Set.toList prePlaces)) marking)
            marking2 = foldl (\m p -> Map.insert p (tokenColor : Map.findWithDefault [] p m) m) marking1 postPlaces
        in marking2
```

## 🚀 实际应用

### 生产者-消费者模型

```haskell
-- 生产者-消费者Petri网
producerConsumerNet :: PetriNet
producerConsumerNet = PetriNet
    { places = Set.fromList ["producer", "buffer", "consumer", "empty", "full"]
    , transitions = Set.fromList ["produce", "consume"]
    , flowRelation = Set.fromList 
        [ PlaceToTransition "producer" "produce"
        , TransitionToPlace "produce" "buffer"
        , PlaceToTransition "buffer" "consume"
        , TransitionToPlace "consume" "consumer"
        , PlaceToTransition "empty" "produce"
        , TransitionToPlace "produce" "full"
        , PlaceToTransition "full" "consume"
        , TransitionToPlace "consume" "empty"
        ]
    , initialMarking = Map.fromList 
        [ ("producer", 1)
        , ("buffer", 0)
        , ("consumer", 0)
        , ("empty", 3)  -- 缓冲区容量
        , ("full", 0)
        ]
    }

-- 分析生产者-消费者系统
analyzeProducerConsumer :: IO ()
analyzeProducerConsumer = do
    let net = producerConsumerNet
        reachable = reachabilityAnalysis net
    
    putStrLn "生产者-消费者系统分析："
    putStrLn $ "可达状态数: " ++ show (length reachable)
    putStrLn $ "系统是否安全: " ++ show (isSafe net)
    putStrLn $ "系统是否有死锁: " ++ show (hasDeadlock net)
    putStrLn $ "系统是否可逆: " ++ show (isReversible net)
```

## 🔗 相关链接

### 理论基础

- [并发理论](../01-Concurrency-Theory/001-Concurrent-Systems.md)
- [图论](../02-Formal-Science/01-Mathematics/003-Graph-Theory.md)
- [形式语言理论](../02-Formal-Science/07-Formal-Language-Theory/001-Formal-Language-Foundation.md)

### 高级Petri网

- [时间Petri网](./002-Timed-Petri-Nets.md)
- [着色Petri网](./003-Colored-Petri-Nets.md)
- [层次Petri网](./004-Hierarchical-Petri-Nets.md)

### 实际应用

- [工作流建模](../haskell/14-Real-World-Applications/001-Workflow-Modeling.md)
- [并发系统验证](../haskell/13-Formal-Verification/002-Model-Checking.md)
- [分布式系统分析](../haskell/15-Advanced-Architecture/002-Distributed-Systems.md)

---

**最后更新**: 2024年12月
**版本**: 1.0
**状态**: ✅ 完成
**维护者**: 形式化知识体系团队
