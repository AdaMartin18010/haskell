# 模型检查

## 概述

模型检查是一种自动化的形式化验证技术，用于验证有限状态系统是否满足给定的时序逻辑规范。它通过系统地探索系统的所有可能状态来检查规范的正确性。

## 理论基础

### 状态转换系统

```haskell
-- 状态转换系统
data TransitionSystem state action = TransitionSystem
  { states :: Set state
  , initialStates :: Set state
  , actions :: Set action
  , transitions :: Map state [(action, state)]
  , atomicPropositions :: Map state (Set String)
  }

-- 状态转换关系
type Transition state action = (state, action, state)

-- 路径
type Path state action = [Transition state action]

-- 可达性关系
reachable :: (Eq state, Ord state) => TransitionSystem state action -> state -> state -> Bool
reachable ts start end = end `Set.member` reachableStates ts start

-- 计算可达状态
reachableStates :: (Eq state, Ord state) => TransitionSystem state action -> state -> Set state
reachableStates ts start = 
  let initial = Set.singleton start
      step current = Set.unions [Set.fromList (map (\(_, _, s) -> s) (transitions ts s)) 
                                | s <- Set.toList current]
  in fixpoint step initial

-- 不动点计算
fixpoint :: (Eq a, Ord a) => (Set a -> Set a) -> Set a -> Set a
fixpoint f initial = 
  let next = f initial
  in if next == initial 
     then initial 
     else fixpoint f next
```

### 时序逻辑

#### 计算树逻辑 (CTL)

```haskell
-- 计算树逻辑
data CTL state
  = AP String                    -- 原子命题
  | Not (CTL state)             -- 否定
  | And (CTL state) (CTL state) -- 合取
  | Or (CTL state) (CTL state)  -- 析取
  | EX (CTL state)              -- 存在下一个
  | AX (CTL state)              -- 所有下一个
  | EF (CTL state)              -- 存在未来
  | AF (CTL state)              -- 所有未来
  | EG (CTL state)              -- 存在全局
  | AG (CTL state)              -- 所有全局
  | EU (CTL state) (CTL state)  -- 存在直到
  | AU (CTL state) (CTL state)  -- 所有直到

-- CTL语义
class CTLSemantics state action where
  -- 状态满足公式
  satisfies :: TransitionSystem state action -> state -> CTL state -> Bool
  satisfies ts s formula = case formula of
    AP prop -> prop `Set.member` (atomicPropositions ts Map.! s)
    Not phi -> not (satisfies ts s phi)
    And phi psi -> satisfies ts s phi && satisfies ts s psi
    Or phi psi -> satisfies ts s phi || satisfies ts s psi
    EX phi -> any (\s' -> satisfies ts s' phi) (nextStates ts s)
    AX phi -> all (\s' -> satisfies ts s' phi) (nextStates ts s)
    EF phi -> s `Set.member` (leastFixpoint ts phi preExists)
    AF phi -> s `Set.member` (leastFixpoint ts phi preForall)
    EG phi -> s `Set.member` (greatestFixpoint ts phi preExists)
    AG phi -> s `Set.member` (greatestFixpoint ts phi preForall)
    EU phi psi -> s `Set.member` (leastFixpoint ts psi 
      (\s -> satisfies ts s psi || (satisfies ts s phi && any (\s' -> s' `Set.member` s) (nextStates ts s))))
    AU phi psi -> s `Set.member` (leastFixpoint ts psi
      (\s -> satisfies ts s psi || (satisfies ts s phi && all (\s' -> s' `Set.member` s) (nextStates ts s))))

-- 后继状态
nextStates :: TransitionSystem state action -> state -> [state]
nextStates ts s = [s' | (_, _, s') <- transitions ts Map.! s]

-- 前驱状态
preStates :: TransitionSystem state action -> state -> [state]
preStates ts s = [s' | (s', _, s'') <- concatMap (transitions ts Map.!) (states ts), s'' == s]

-- 存在前驱
preExists :: TransitionSystem state action -> Set state -> Set state
preExists ts states = Set.fromList [s | s <- states ts, 
  any (\s' -> s' `Set.member` states) (nextStates ts s)]

-- 所有前驱
preForall :: TransitionSystem state action -> Set state -> Set state
preForall ts states = Set.fromList [s | s <- states ts, 
  all (\s' -> s' `Set.member` states) (nextStates ts s)]
```

#### 线性时序逻辑 (LTL)

```haskell
-- 线性时序逻辑
data LTL
  = AP String           -- 原子命题
  | Not LTL            -- 否定
  | And LTL LTL        -- 合取
  | Or LTL LTL         -- 析取
  | Next LTL           -- 下一个
  | Until LTL LTL      -- 直到
  | Release LTL LTL    -- 释放
  | Finally LTL        -- 最终
  | Globally LTL       -- 全局

-- LTL到Büchi自动机的转换
class LTLToBuchi where
  -- 将LTL公式转换为Büchi自动机
  ltlToBuchi :: LTL -> BuchiAutomaton
  ltlToBuchi formula = constructBuchi (normalizeLTL formula)
  
  -- LTL范式化
  normalizeLTL :: LTL -> LTL
  normalizeLTL = pushNegations . expandTemporalOperators
  
  -- 构建Büchi自动机
  constructBuchi :: LTL -> BuchiAutomaton
  constructBuchi formula = BuchiAutomaton
    { states = generateStates formula
    , initialStates = initialStates formula
    , alphabet = generateAlphabet formula
    , transitions = generateTransitions formula
    , acceptingStates = generateAcceptingStates formula
    }

-- Büchi自动机
data BuchiAutomaton = BuchiAutomaton
  { states :: Set String
  , initialStates :: Set String
  , alphabet :: Set String
  , transitions :: Map String [(String, String)] -- (state, symbol, next_state)
  , acceptingStates :: Set String
  }

-- Büchi自动机接受性
accepts :: BuchiAutomaton -> [String] -> Bool
accepts ba word = 
  let runs = allRuns ba word
      acceptingRuns = filter (isAccepting ba) runs
  in not (null acceptingRuns)

-- 所有运行
allRuns :: BuchiAutomaton -> [String] -> [[String]]
allRuns ba word = 
  let initial = Set.toList (initialStates ba)
  in concatMap (\s -> runsFrom ba s word) initial

-- 从状态开始的运行
runsFrom :: BuchiAutomaton -> String -> [String] -> [[String]]
runsFrom ba state [] = [[state]]
runsFrom ba state (symbol:symbols) = 
  let nextStates = [s' | (s, sym, s') <- transitions ba Map.! state, sym == symbol]
  in concatMap (\s' -> map (state:) (runsFrom ba s' symbols)) nextStates

-- 检查运行是否接受
isAccepting :: BuchiAutomaton -> [String] -> Bool
isAccepting ba run = 
  let infiniteSuffix = drop (length run `div` 2) run
      visitedStates = Set.fromList infiniteSuffix
  in not (Set.null (Set.intersection visitedStates (acceptingStates ba)))
```

## 模型检查算法

### 显式状态模型检查

```haskell
-- 显式状态模型检查器
class ExplicitModelChecker state action where
  -- CTL模型检查
  checkCTL :: TransitionSystem state action -> CTL state -> Set state
  checkCTL ts formula = case formula of
    AP prop -> statesWithProp ts prop
    Not phi -> states ts `Set.difference` checkCTL ts phi
    And phi psi -> checkCTL ts phi `Set.intersection` checkCTL ts psi
    Or phi psi -> checkCTL ts phi `Set.union` checkCTL ts psi
    EX phi -> preExists ts (checkCTL ts phi)
    AX phi -> preForall ts (checkCTL ts phi)
    EF phi -> leastFixpoint ts (checkCTL ts phi) (preExists ts)
    AF phi -> leastFixpoint ts (checkCTL ts phi) (preForall ts)
    EG phi -> greatestFixpoint ts (checkCTL ts phi) (preExists ts)
    AG phi -> greatestFixpoint ts (checkCTL ts phi) (preForall ts)
    EU phi psi -> leastFixpoint ts (checkCTL ts psi) 
      (\s -> checkCTL ts psi `Set.union` (checkCTL ts phi `Set.intersection` preExists ts s))
    AU phi psi -> leastFixpoint ts (checkCTL ts psi)
      (\s -> checkCTL ts psi `Set.union` (checkCTL ts phi `Set.intersection` preForall ts s))

-- 最小不动点
leastFixpoint :: (Eq state, Ord state) => 
  TransitionSystem state action -> Set state -> (Set state -> Set state) -> Set state
leastFixpoint ts initial f = 
  let step current = f current
  in fixpoint step initial

-- 最大不动点
greatestFixpoint :: (Eq state, Ord state) => 
  TransitionSystem state action -> Set state -> (Set state -> Set state) -> Set state
greatestFixpoint ts initial f = 
  let step current = f current
  in fixpoint step (states ts)

-- 具有特定命题的状态
statesWithProp :: TransitionSystem state action -> String -> Set state
statesWithProp ts prop = Set.fromList [s | s <- states ts, 
  prop `Set.member` (atomicPropositions ts Map.! s)]
```

### 符号模型检查

```haskell
-- 符号模型检查器
class SymbolicModelChecker where
  -- 使用BDD进行符号模型检查
  symbolicCheckCTL :: BDD -> CTL BDD -> BDD
  symbolicCheckCTL ts formula = case formula of
    AP prop -> bddVariable prop
    Not phi -> bddNot (symbolicCheckCTL ts phi)
    And phi psi -> bddAnd (symbolicCheckCTL ts phi) (symbolicCheckCTL ts psi)
    Or phi psi -> bddOr (symbolicCheckCTL ts phi) (symbolicCheckCTL ts psi)
    EX phi -> symbolicPreExists ts (symbolicCheckCTL ts phi)
    AX phi -> symbolicPreForall ts (symbolicCheckCTL ts phi)
    EF phi -> symbolicLeastFixpoint ts (symbolicCheckCTL ts phi) symbolicPreExists
    AF phi -> symbolicLeastFixpoint ts (symbolicCheckCTL ts phi) symbolicPreForall
    EG phi -> symbolicGreatestFixpoint ts (symbolicCheckCTL ts phi) symbolicPreExists
    AG phi -> symbolicGreatestFixpoint ts (symbolicCheckCTL ts phi) symbolicPreForall

-- 二元决策图 (BDD)
data BDD
  = BDDTrue
  | BDDFalse
  | BDDNode String BDD BDD -- variable, then-branch, else-branch

-- BDD操作
bddAnd :: BDD -> BDD -> BDD
bddAnd BDDTrue b = b
bddAnd BDDFalse _ = BDDFalse
bddAnd (BDDNode v t e) b = BDDNode v (bddAnd t b) (bddAnd e b)

bddOr :: BDD -> BDD -> BDD
bddOr BDDTrue _ = BDDTrue
bddOr BDDFalse b = b
bddOr (BDDNode v t e) b = BDDNode v (bddOr t b) (bddOr e b)

bddNot :: BDD -> BDD
bddNot BDDTrue = BDDFalse
bddNot BDDFalse = BDDTrue
bddNot (BDDNode v t e) = BDDNode v (bddNot t) (bddNot e)

-- 符号前驱计算
symbolicPreExists :: BDD -> BDD -> BDD
symbolicPreExists ts states = 
  let vars = bddVariables ts
      nextVars = map (\v -> v ++ "'") vars
  in bddExists nextVars (bddAnd ts (bddSubstitute states vars nextVars))

symbolicPreForall :: BDD -> BDD -> BDD
symbolicPreForall ts states = 
  let vars = bddVariables ts
      nextVars = map (\v -> v ++ "'") vars
  in bddForall nextVars (bddImplies ts (bddSubstitute states vars nextVars))
```

### 有界模型检查

```haskell
-- 有界模型检查器
class BoundedModelChecker where
  -- k步有界模型检查
  boundedModelCheck :: Int -> TransitionSystem state action -> LTL -> Bool
  boundedModelCheck k ts formula = 
    let buchi = ltlToBuchi formula
        product = synchronousProduct ts buchi
        boundedPaths = generateBoundedPaths product k
    in any (\path -> isAcceptingPath buchi path) boundedPaths

-- 同步积
synchronousProduct :: TransitionSystem state action -> BuchiAutomaton -> TransitionSystem (state, String) action
synchronousProduct ts ba = TransitionSystem
  { states = Set.fromList [(s, q) | s <- states ts, q <- states ba]
  , initialStates = Set.fromList [(s, q) | s <- initialStates ts, q <- initialStates ba]
  , actions = actions ts
  , transitions = Map.fromList [((s, q), [(a, (s', q')) | (a, s') <- transitions ts Map.! s,
                                                          (q, _, q') <- transitions ba Map.! q])
                               | (s, q) <- Set.toList (states ts `Set.cartesian` states ba)]
  , atomicPropositions = Map.fromList [((s, q), atomicPropositions ts Map.! s)
                                      | (s, q) <- Set.toList (states ts `Set.cartesian` states ba)]
  }

-- 生成有界路径
generateBoundedPaths :: TransitionSystem state action -> Int -> [[state]]
generateBoundedPaths ts k = 
  let initial = Set.toList (initialStates ts)
  in concatMap (\s -> boundedPathsFrom ts s k) initial

-- 从状态开始的有界路径
boundedPathsFrom :: TransitionSystem state action -> state -> Int -> [[state]]
boundedPathsFrom ts state 0 = [[state]]
boundedPathsFrom ts state k = 
  let nextStates = [s' | (_, _, s') <- transitions ts Map.! state]
  in concatMap (\s' -> map (state:) (boundedPathsFrom ts s' (k-1))) nextStates
```

## 实际应用

### 协议验证

```haskell
-- 互斥协议模型
data MutexState = MutexState
  { process1 :: ProcessState
  , process2 :: ProcessState
  , mutex :: MutexState
  }

data ProcessState = Idle | Requesting | Critical
data MutexState = Free | Locked

-- 互斥协议转换系统
mutexTransitionSystem :: TransitionSystem MutexState String
mutexTransitionSystem = TransitionSystem
  { states = Set.fromList [MutexState p1 p2 m | p1 <- [Idle, Requesting, Critical],
                                                p2 <- [Idle, Requesting, Critical],
                                                m <- [Free, Locked]]
  , initialStates = Set.singleton (MutexState Idle Idle Free)
  , actions = Set.fromList ["request1", "request2", "enter1", "enter2", "exit1", "exit2"]
  , transitions = mutexTransitions
  , atomicPropositions = mutexAtomicProps
  }

-- 互斥协议转换规则
mutexTransitions :: Map MutexState [(String, MutexState)]
mutexTransitions = Map.fromList
  [ (MutexState Idle p2 Free, [("request1", MutexState Requesting p2 Free)])
  , (MutexState p1 Idle Free, [("request2", MutexState p1 Requesting Free)])
  , (MutexState Requesting p2 Free, [("enter1", MutexState Critical p2 Locked)])
  , (MutexState p1 Requesting Free, [("enter2", MutexState p1 Critical Locked)])
  , (MutexState Critical p2 Locked, [("exit1", MutexState Idle p2 Free)])
  , (MutexState p1 Critical Locked, [("exit2", MutexState p1 Idle Free)])
  ]

-- 互斥协议原子命题
mutexAtomicProps :: Map MutexState (Set String)
mutexAtomicProps = Map.fromList
  [ (MutexState p1 p2 m, Set.fromList (processProps p1 ++ processProps p2 ++ mutexProps m))
  | p1 <- [Idle, Requesting, Critical],
    p2 <- [Idle, Requesting, Critical],
    m <- [Free, Locked]
  ]
  where
    processProps Idle = ["idle1"]
    processProps Requesting = ["requesting1"]
    processProps Critical = ["critical1"]
    mutexProps Free = ["free"]
    mutexProps Locked = ["locked"]

-- 互斥性质验证
verifyMutexProperties :: Bool
verifyMutexProperties = 
  let ts = mutexTransitionSystem
      -- 互斥性质：不能同时有两个进程在临界区
      mutualExclusion = AG (Not (And (AP "critical1") (AP "critical2")))
      -- 无死锁性质：总是存在一个进程可以进入临界区
      noDeadlock = AG (EF (Or (AP "critical1") (AP "critical2")))
      -- 无饥饿性质：请求进入临界区的进程最终会进入
      noStarvation = AG (AP "requesting1" `implies` AF (AP "critical1"))
      
      meResult = checkCTL ts mutualExclusion
      ndResult = checkCTL ts noDeadlock
      nsResult = checkCTL ts noStarvation
  in all (\s -> s `Set.member` meResult) (initialStates ts) &&
     all (\s -> s `Set.member` ndResult) (initialStates ts) &&
     all (\s -> s `Set.member` nsResult) (initialStates ts)
```

### 缓存一致性协议

```haskell
-- 缓存一致性状态
data CacheState = CacheState
  { cache1 :: CacheLine
  , cache2 :: CacheLine
  , memory :: MemoryLine
  }

data CacheLine = Invalid | Shared | Modified
data MemoryLine = MemoryLine { value :: Int, valid :: Bool }

-- 缓存一致性协议转换系统
cacheCoherenceSystem :: TransitionSystem CacheState String
cacheCoherenceSystem = TransitionSystem
  { states = Set.fromList [CacheState c1 c2 m | c1 <- [Invalid, Shared, Modified],
                                                c2 <- [Invalid, Shared, Modified],
                                                m <- [MemoryLine 0 True, MemoryLine 1 True]]
  , initialStates = Set.singleton (CacheState Invalid Invalid (MemoryLine 0 True))
  , actions = Set.fromList ["read1", "read2", "write1", "write2", "invalidate1", "invalidate2"]
  , transitions = cacheTransitions
  , atomicPropositions = cacheAtomicProps
  }

-- 缓存一致性性质验证
verifyCacheCoherence :: Bool
verifyCacheCoherence = 
  let ts = cacheCoherenceSystem
      -- 一致性性质：如果两个缓存都是Modified，则它们必须包含相同的值
      coherence = AG (And (AP "modified1") (AP "modified2") `implies` (AP "same_value"))
      -- 有效性性质：读取操作总是返回最近写入的值
      validity = AG (AP "read1" `implies` AF (AP "correct_value"))
      
      coResult = checkCTL ts coherence
      vaResult = checkCTL ts validity
  in all (\s -> s `Set.member` coResult) (initialStates ts) &&
     all (\s -> s `Set.member` vaResult) (initialStates ts)
```

### 实时系统验证

```haskell
-- 实时任务状态
data RealTimeTask = RealTimeTask
  { taskId :: Int
  , deadline :: Time
  , executionTime :: Time
  , priority :: Priority
  , state :: TaskState
  }

data TaskState = Ready | Running | Blocked | Completed
type Time = Int
type Priority = Int

-- 实时调度器状态
data SchedulerState = SchedulerState
  { tasks :: [RealTimeTask]
  , currentTime :: Time
  , runningTask :: Maybe Int
  }

-- 实时系统转换系统
realTimeSystem :: TransitionSystem SchedulerState String
realTimeSystem = TransitionSystem
  { states = Set.fromList [SchedulerState tasks time running | 
                           tasks <- allTaskConfigurations,
                           time <- [0..maxTime],
                           running <- [Nothing] ++ map Just [1..numTasks]]
  , initialStates = Set.singleton (SchedulerState initialTasks 0 Nothing)
  , actions = Set.fromList ["schedule", "execute", "preempt", "complete", "miss_deadline"]
  , transitions = schedulerTransitions
  , atomicPropositions = schedulerAtomicProps
  }

-- 实时系统性质验证
verifyRealTimeProperties :: Bool
verifyRealTimeProperties = 
  let ts = realTimeSystem
      -- 调度性性质：所有任务都能在截止时间前完成
      schedulability = AG (AP "task_ready" `implies` AF (AP "task_completed"))
      -- 无死锁性质：系统总是有任务可以执行
      noDeadlock = AG (EF (AP "task_running"))
      -- 优先级性质：高优先级任务优先执行
      priority = AG (And (AP "high_priority_ready") (AP "low_priority_running") 
                        `implies` AX (AP "high_priority_running"))
      
      scResult = checkCTL ts schedulability
      ndResult = checkCTL ts noDeadlock
      prResult = checkCTL ts priority
  in all (\s -> s `Set.member` scResult) (initialStates ts) &&
     all (\s -> s `Set.member` ndResult) (initialStates ts) &&
     all (\s -> s `Set.member` prResult) (initialStates ts)
```

## 工具和框架

### 模型检查工具

```haskell
-- 模型检查工具接口
class ModelCheckingTool where
  -- 加载模型
  loadModel :: FilePath -> IO (TransitionSystem state action)
  
  -- 指定性质
  specifyProperty :: CTL state -> IO ()
  
  -- 运行模型检查
  runModelChecking :: IO ModelCheckingResult
  
  -- 生成反例
  generateCounterExample :: IO CounterExample

-- 模型检查结果
data ModelCheckingResult
  = Satisfied
  | Violated CounterExample
  | Timeout
  | OutOfMemory

-- 反例
data CounterExample = CounterExample
  { initialState :: String
  , path :: [String]
  , violation :: String
  }

-- SPIN模型检查器
data SPIN = SPIN
  { spinPath :: FilePath
  , options :: [SPINOption]
  }

instance ModelCheckingTool SPIN where
  loadModel spin path = do
    promelaCode <- readFile path
    return (parsePromela promelaCode)
  
  specifyProperty spin property = do
    let ltlFormula = ctlToLTL property
    writeLTLFormula spin ltlFormula
  
  runModelChecking spin = do
    result <- executeSPIN spin
    return (parseSPINResult result)

-- NuSMV模型检查器
data NuSMV = NuSMV
  { nusmvPath :: FilePath
  , configuration :: NuSMVConfig
  }

instance ModelCheckingTool NuSMV where
  loadModel nusmv path = do
    smvCode <- readFile path
    return (parseSMV smvCode)
  
  specifyProperty nusmv property = do
    let ctlFormula = formatCTL property
    writeCTLFormula nusmv ctlFormula
  
  runModelChecking nusmv = do
    result <- executeNuSMV nusmv
    return (parseNuSMVResult result)
```

### 性能优化

```haskell
-- 模型检查性能优化
class ModelCheckingOptimization where
  -- 状态空间抽象
  abstractStates :: TransitionSystem state action -> (state -> abstractState) -> TransitionSystem abstractState action
  
  -- 偏序规约
  partialOrderReduction :: TransitionSystem state action -> TransitionSystem state action
  
  -- 对称规约
  symmetryReduction :: TransitionSystem state action -> TransitionSystem state action
  
  -- 组合推理
  compositionalReasoning :: [TransitionSystem state action] -> CTL state -> Bool

-- 状态抽象
abstractStates ts abstraction = TransitionSystem
  { states = Set.map abstraction (states ts)
  , initialStates = Set.map abstraction (initialStates ts)
  , actions = actions ts
  , transitions = Map.fromList [(abstraction s, [(a, abstraction s') | (a, s') <- transitions ts Map.! s])
                               | s <- states ts]
  , atomicPropositions = Map.fromList [(abstraction s, atomicPropositions ts Map.! s)
                                      | s <- states ts]
  }

-- 偏序规约
partialOrderReduction ts = 
  let independentActions = findIndependentActions ts
      reducedTransitions = removeDependentTransitions ts independentActions
  in ts { transitions = reducedTransitions }

-- 对称规约
symmetryReduction ts = 
  let symmetries = findSymmetries ts
      representatives = chooseRepresentatives ts symmetries
  in ts { states = representatives }
```

---

**相关链接**：

- [形式化验证](./001-Formal-Verification.md)
- [定理证明](./003-Theorem-Proving.md)
- [程序分析](./004-Program-Analysis.md)
- [Haskell实现](../07-Implementation/001-Haskell-Implementation.md)
- [Rust实现](../07-Implementation/002-Rust-Implementation.md)
- [Lean实现](../07-Implementation/003-Lean-Implementation.md)
