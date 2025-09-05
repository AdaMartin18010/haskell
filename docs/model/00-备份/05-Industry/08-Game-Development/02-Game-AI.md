# 游戏AI理论 (Game AI Theory)

## 📋 文档信息

- **文档编号**: 05-08-02
- **所属层级**: 产业层 - 游戏开发
- **创建时间**: 2024年12月19日
- **最后更新**: 2024年12月19日
- **文档状态**: 完成

---

## 🎯 概述

游戏AI是游戏开发中的核心技术，涉及智能体行为控制、路径规划、决策制定等。本文档系统性地介绍游戏AI的理论基础、算法实现和实际应用。

## 📚 理论基础

### 1. 路径规划算法

#### 1.1 A*算法

A*算法的评估函数：

$$f(n) = g(n) + h(n)$$

其中 $g(n)$ 是从起点到节点n的实际代价，$h(n)$ 是从节点n到目标的启发式估计。

#### 1.2 Dijkstra算法

Dijkstra算法的最短路径：

$$d[v] = \min(d[v], d[u] + w(u,v))$$

其中 $w(u,v)$ 是边(u,v)的权重。

#### 1.3 导航网格

导航网格的三角形剖分：

$$T = \{t_1, t_2, \ldots, t_n\}$$

其中每个三角形 $t_i$ 都是可通行的区域。

### 2. 决策理论

#### 2.1 效用理论

效用函数：

$$U(a) = \sum_{s \in S} P(s|a) \cdot V(s)$$

其中 $P(s|a)$ 是执行动作a后状态s的概率，$V(s)$ 是状态s的价值。

#### 2.2 博弈论

纳什均衡：

$$\forall i, \forall s_i': u_i(s_i^*, s_{-i}^*) \geq u_i(s_i', s_{-i}^*)$$

### 3. 机器学习

#### 3.1 强化学习

Q-learning更新规则：

$$Q(s,a) \leftarrow Q(s,a) + \alpha[r + \gamma \max_{a'} Q(s',a') - Q(s,a)]$$

#### 3.2 神经网络

前向传播：

$$y = \sigma(W^T x + b)$$

## 🔧 Haskell实现

### 1. 路径规划

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module GameAI.Pathfinding where

import Data.List
import Data.Maybe
import Control.Monad.State
import Data.PriorityQueue
import Data.Graph
import Data.Vector (Vector)
import qualified Data.Vector as V

-- 游戏世界坐标
type Position = (Int, Int)
type Cost = Double

-- 游戏世界
data GameWorld = GameWorld
  { width :: Int
  , height :: Int
  , obstacles :: [Position]
  , terrain :: Matrix TerrainType
  } deriving Show

-- 地形类型
data TerrainType = 
  Grass
  | Water
  | Mountain
  | Road
  deriving (Show, Eq)

-- 矩阵类型
data Matrix a = Matrix
  { rows :: Int
  , cols :: Int
  , elements :: [[a]]
  } deriving Show

-- 创建游戏世界
createGameWorld :: Int -> Int -> GameWorld
createGameWorld w h = 
  let terrain = Matrix h w (replicate h (replicate w Grass))
  in GameWorld w h [] terrain

-- A*算法节点
data AStarNode = AStarNode
  { position :: Position
  , gCost :: Cost
  , hCost :: Cost
  , fCost :: Cost
  , parent :: Maybe Position
  } deriving Show

-- A*算法实现
aStarPathfinding :: GameWorld -> Position -> Position -> Maybe [Position]
aStarPathfinding world start goal = 
  let -- 初始化开放列表和关闭列表
      initialNode = AStarNode start 0 (heuristic start goal) (heuristic start goal) Nothing
      openList = singleton (fCost initialNode) initialNode
      closedList = []
      
      -- 执行A*搜索
      result = aStarSearch world openList closedList goal
  in result

-- A*搜索
aStarSearch :: GameWorld -> PriorityQueue AStarNode -> [Position] -> Position -> Maybe [Position]
aStarSearch world openList closedList goal = 
  if isEmpty openList
  then Nothing  -- 没有找到路径
  else 
    let (currentNode, remainingOpen) = deleteMin openList
        currentPos = position currentNode
    in if currentPos == goal
       then Just (reconstructPath currentNode)  -- 找到目标
       else 
         let -- 将当前节点加入关闭列表
             newClosedList = currentPos : closedList
             
             -- 获取邻居节点
             neighbors = getNeighbors world currentPos
             validNeighbors = filter (\pos -> not (pos `elem` newClosedList)) neighbors
             
             -- 处理每个邻居
             updatedOpenList = foldl (\open neighbor -> 
                                       processNeighbor currentNode neighbor goal open) 
                                     remainingOpen validNeighbors
         in aStarSearch world updatedOpenList newClosedList goal

-- 启发式函数（曼哈顿距离）
heuristic :: Position -> Position -> Cost
heuristic (x1, y1) (x2, y2) = fromIntegral (abs (x1 - x2) + abs (y1 - y2))

-- 获取邻居节点
getNeighbors :: GameWorld -> Position -> [Position]
getNeighbors world (x, y) = 
  let directions = [(0,1), (1,0), (0,-1), (-1,0)]  -- 四个方向
      neighbors = [(x+dx, y+dy) | (dx, dy) <- directions]
      validNeighbors = filter (isValidPosition world) neighbors
  in validNeighbors

-- 检查位置是否有效
isValidPosition :: GameWorld -> Position -> Bool
isValidPosition world (x, y) = 
  x >= 0 && x < width world && 
  y >= 0 && y < height world && 
  not ((x, y) `elem` obstacles world)

-- 处理邻居节点
processNeighbor :: AStarNode -> Position -> Position -> PriorityQueue AStarNode -> PriorityQueue AStarQueue
processNeighbor currentNode neighbor goal openList = 
  let -- 计算从起点经过当前节点到邻居的代价
      newGCost = gCost currentNode + getMovementCost currentNode neighbor
      
      -- 检查是否已经在开放列表中
      existingNode = findNode openList neighbor
  in case existingNode of
       Just node -> 
         if newGCost < gCost node
         then -- 更新节点
              let updatedNode = node { gCost = newGCost, fCost = newGCost + hCost node, parent = Just (position currentNode) }
              in updateNode openList neighbor updatedNode
         else openList
       Nothing -> 
         -- 添加新节点
         let hCost = heuristic neighbor goal
             newNode = AStarNode neighbor newGCost hCost (newGCost + hCost) (Just (position currentNode))
         in insert (fCost newNode) newNode openList

-- 获取移动代价
getMovementCost :: AStarNode -> Position -> Cost
getMovementCost _ _ = 1.0  -- 简化：统一代价

-- 重建路径
reconstructPath :: AStarNode -> [Position]
reconstructPath node = 
  let path = reverse (buildPath node [])
  in path
  where buildPath (AStarNode pos _ _ _ Nothing) acc = pos : acc
        buildPath (AStarNode pos _ _ _ (Just parent)) acc = 
          buildPath (findParentNode parent) (pos : acc)

-- 查找父节点（简化实现）
findParentNode :: Position -> AStarNode
findParentNode pos = AStarNode pos 0 0 0 Nothing

-- 优先级队列实现
data PriorityQueue a = PriorityQueue [(Double, a)]
  deriving Show

-- 创建空队列
empty :: PriorityQueue a
empty = PriorityQueue []

-- 检查队列是否为空
isEmpty :: PriorityQueue a -> Bool
isEmpty (PriorityQueue []) = True
isEmpty _ = False

-- 插入元素
insert :: Double -> a -> PriorityQueue a -> PriorityQueue a
insert priority value (PriorityQueue queue) = 
  PriorityQueue (insertSorted (priority, value) queue)
  where insertSorted item [] = [item]
        insertSorted item@(p1, _) ((p2, v2):rest) = 
          if p1 <= p2
          then item : (p2, v2) : rest
          else (p2, v2) : insertSorted item rest

-- 删除最小元素
deleteMin :: PriorityQueue a -> (a, PriorityQueue a)
deleteMin (PriorityQueue ((_, value):rest)) = (value, PriorityQueue rest)
deleteMin (PriorityQueue []) = error "Empty queue"

-- 查找节点
findNode :: PriorityQueue AStarNode -> Position -> Maybe AStarNode
findNode (PriorityQueue queue) pos = 
  case find (\(_, node) -> position node == pos) queue of
    Just (_, node) -> Just node
    Nothing -> Nothing

-- 更新节点
updateNode :: PriorityQueue AStarNode -> Position -> AStarNode -> PriorityQueue AStarNode
updateNode (PriorityQueue queue) pos newNode = 
  let filtered = filter (\(_, node) -> position node /= pos) queue
  in PriorityQueue (insertSorted (fCost newNode, newNode) filtered)
  where insertSorted item [] = [item]
        insertSorted item@(p1, _) ((p2, v2):rest) = 
          if p1 <= p2
          then item : (p2, v2) : rest
          else (p2, v2) : insertSorted item rest

-- 单例队列
singleton :: Double -> a -> PriorityQueue a
singleton priority value = PriorityQueue [(priority, value)]
```

### 2. 决策树

```haskell
-- 决策树节点
data DecisionNode = 
  ActionNode GameAction
  | ConditionNode Condition DecisionNode DecisionNode
  deriving Show

-- 游戏动作
data GameAction = 
  Move Position
  | Attack Position
  | Defend
  | UseItem String
  | Wait
  deriving Show

-- 条件
data Condition = 
  HealthBelow Double
  | EnemyNearby Position
  | HasItem String
  | IsInDanger
  | CanAttack Position
  deriving Show

-- 游戏状态
data GameState = GameState
  { playerPosition :: Position
  , playerHealth :: Double
  , playerItems :: [String]
  , enemies :: [Enemy]
  , world :: GameWorld
  } deriving Show

-- 敌人
data Enemy = Enemy
  { enemyPosition :: Position
  , enemyHealth :: Double
  , enemyType :: EnemyType
  } deriving Show

-- 敌人类型
data EnemyType = 
  Goblin
  | Orc
  | Dragon
  deriving Show

-- 决策树
data DecisionTree = DecisionTree
  { root :: DecisionNode
  , name :: String
  } deriving Show

-- 创建简单决策树
createSimpleDecisionTree :: DecisionTree
createSimpleDecisionTree = 
  let -- 根节点：检查健康值
      healthCheck = ConditionNode (HealthBelow 0.3) 
                    (ActionNode Defend)  -- 健康值低时防御
                    (ConditionNode (EnemyNearby (0,0)) 
                      (ActionNode (Attack (0,0)))  -- 有敌人时攻击
                      (ActionNode (Move (1,1))))   -- 否则移动
  in DecisionTree healthCheck "SimpleAI"

-- 执行决策树
executeDecisionTree :: DecisionTree -> GameState -> GameAction
executeDecisionTree (DecisionTree root _) state = 
  evaluateNode root state

-- 评估节点
evaluateNode :: DecisionNode -> GameState -> GameAction
evaluateNode (ActionNode action) _ = action
evaluateNode (ConditionNode condition trueBranch falseBranch) state = 
  if evaluateCondition condition state
  then evaluateNode trueBranch state
  else evaluateNode falseBranch state

-- 评估条件
evaluateCondition :: Condition -> GameState -> Bool
evaluateCondition condition state = case condition of
  HealthBelow threshold -> playerHealth state < threshold
  EnemyNearby pos -> any (\enemy -> distance (playerPosition state) (enemyPosition enemy) < 5) (enemies state)
  HasItem item -> item `elem` playerItems state
  IsInDanger -> any (\enemy -> distance (playerPosition state) (enemyPosition enemy) < 2) (enemies state)
  CanAttack pos -> distance (playerPosition state) pos <= 1

-- 计算距离
distance :: Position -> Position -> Double
distance (x1, y1) (x2, y2) = sqrt (fromIntegral ((x1-x2)^2 + (y1-y2)^2))

-- 创建复杂决策树
createComplexDecisionTree :: DecisionTree
createComplexDecisionTree = 
  let -- 检查是否有治疗物品
      hasHealingItem = ConditionNode (HasItem "Potion") 
                        (ConditionNode (HealthBelow 0.5) 
                          (ActionNode (UseItem "Potion"))  -- 使用治疗物品
                          (combatDecisionTree))           -- 进入战斗决策
                        (combatDecisionTree)              -- 没有治疗物品，直接战斗
  in DecisionTree hasHealingItem "ComplexAI"

-- 战斗决策树
combatDecisionTree :: DecisionNode
combatDecisionTree = 
  ConditionNode IsInDanger
    (ConditionNode (HasItem "Shield") 
      (ActionNode Defend)  -- 有盾牌时防御
      (ActionNode (Move (0,1))))  -- 没有盾牌时逃跑
    (ConditionNode (EnemyNearby (0,0)) 
      (ActionNode (Attack (0,0)))  -- 攻击敌人
      (ActionNode (Move (1,0)))    -- 探索地图
    )

-- 动态决策树
data DynamicDecisionTree = DynamicDecisionTree
  { staticTree :: DecisionTree
  , learningRate :: Double
  , experience :: [(GameState, GameAction, Double)]  -- 状态、动作、奖励
  } deriving Show

-- 创建动态决策树
createDynamicDecisionTree :: DecisionTree -> Double -> DynamicDecisionTree
createDynamicDecisionTree tree rate = 
  DynamicDecisionTree tree rate []

-- 学习新经验
learnFromExperience :: DynamicDecisionTree -> GameState -> GameAction -> Double -> DynamicDecisionTree
learnFromExperience (DynamicDecisionTree tree rate exp) state action reward = 
  let newExperience = (state, action, reward) : exp
      -- 限制经验数量
      limitedExp = take 1000 newExperience
  in DynamicDecisionTree tree rate limitedExp

-- 基于经验改进决策
improveDecision :: DynamicDecisionTree -> GameState -> GameAction
improveDecision (DynamicDecisionTree tree _ exp) state = 
  let -- 查找相似状态的经验
      similarExperiences = filter (\(expState, _, _) -> isSimilarState state expState) exp
      
      -- 如果没有相似经验，使用静态决策树
      baseAction = executeDecisionTree tree state
  in if null similarExperiences
     then baseAction
     else 
       let -- 选择奖励最高的动作
           bestExperience = maximumBy (\(_, _, r1) (_, _, r2) -> compare r1 r2) similarExperiences
           (_, bestAction, _) = bestExperience
       in bestAction

-- 检查状态相似性
isSimilarState :: GameState -> GameState -> Bool
isSimilarState state1 state2 = 
  let healthDiff = abs (playerHealth state1 - playerHealth state2)
      positionDiff = distance (playerPosition state1) (playerPosition state2)
  in healthDiff < 0.2 && positionDiff < 3.0
```

### 3. 行为树

```haskell
-- 行为树节点
data BehaviorNode = 
  SequenceNode [BehaviorNode]
  | SelectorNode [BehaviorNode]
  | ActionNode GameAction
  | ConditionNode Condition
  | DecoratorNode BehaviorDecorator BehaviorNode
  deriving Show

-- 行为装饰器
data BehaviorDecorator = 
  Inverter
  | Repeater Int
  | UntilSuccess
  | UntilFailure
  deriving Show

-- 行为状态
data BehaviorStatus = 
  Success
  | Failure
  | Running
  deriving (Show, Eq)

-- 行为树
data BehaviorTree = BehaviorTree
  { root :: BehaviorNode
  , name :: String
  } deriving Show

-- 创建行为树
createBehaviorTree :: BehaviorTree
createBehaviorTree = 
  let -- 根节点：选择器
      root = SelectorNode [
        -- 优先级1：检查健康值
        SequenceNode [
          ConditionNode (HealthBelow 0.3),
          ActionNode (UseItem "Potion")
        ],
        -- 优先级2：攻击敌人
        SequenceNode [
          ConditionNode (EnemyNearby (0,0)),
          ActionNode (Attack (0,0))
        ],
        -- 优先级3：探索
        ActionNode (Move (1,0))
      ]
  in BehaviorTree root "CombatAI"

-- 执行行为树
executeBehaviorTree :: BehaviorTree -> GameState -> (BehaviorStatus, GameState)
executeBehaviorTree (BehaviorTree root _) state = 
  executeNode root state

-- 执行节点
executeNode :: BehaviorNode -> GameState -> (BehaviorStatus, GameState)
executeNode node state = case node of
  SequenceNode children -> executeSequence children state
  SelectorNode children -> executeSelector children state
  ActionNode action -> executeAction action state
  ConditionNode condition -> executeCondition condition state
  DecoratorNode decorator child -> executeDecorator decorator child state

-- 执行序列节点
executeSequence :: [BehaviorNode] -> GameState -> (BehaviorStatus, GameState)
executeSequence [] state = (Success, state)
executeSequence (child:children) state = 
  let (status, newState) = executeNode child state
  in case status of
       Failure -> (Failure, newState)
       Success -> executeSequence children newState
       Running -> (Running, newState)

-- 执行选择器节点
executeSelector :: [BehaviorNode] -> GameState -> (BehaviorStatus, GameState)
executeSelector [] state = (Failure, state)
executeSelector (child:children) state = 
  let (status, newState) = executeNode child state
  in case status of
       Success -> (Success, newState)
       Failure -> executeSelector children newState
       Running -> (Running, newState)

-- 执行动作
executeAction :: GameAction -> GameState -> (BehaviorStatus, GameState)
executeAction action state = 
  let newState = applyAction action state
  in (Success, newState)

-- 应用动作
applyAction :: GameAction -> GameState -> GameState
applyAction action state = case action of
  Move pos -> state { playerPosition = pos }
  Attack pos -> 
    let -- 减少敌人健康值
        updatedEnemies = map (\enemy -> 
                              if enemyPosition enemy == pos
                              then enemy { enemyHealth = max 0 (enemyHealth enemy - 10) }
                              else enemy) (enemies state)
    in state { enemies = updatedEnemies }
  Defend -> state  -- 防御不改变状态
  UseItem item -> 
    let -- 使用物品
        updatedItems = filter (/= item) (playerItems state)
        updatedHealth = if item == "Potion" 
                        then min 100 (playerHealth state + 30)
                        else playerHealth state
    in state { playerItems = updatedItems, playerHealth = updatedHealth }
  Wait -> state

-- 执行条件
executeCondition :: Condition -> GameState -> (BehaviorStatus, GameState)
executeCondition condition state = 
  let result = evaluateCondition condition state
  in if result then (Success, state) else (Failure, state)

-- 执行装饰器
executeDecorator :: BehaviorDecorator -> BehaviorNode -> GameState -> (BehaviorStatus, GameState)
executeDecorator decorator child state = case decorator of
  Inverter -> 
    let (status, newState) = executeNode child state
    in case status of
         Success -> (Failure, newState)
         Failure -> (Success, newState)
         Running -> (Running, newState)
  
  Repeater count -> 
    if count <= 0
    then (Success, state)
    else 
      let (status, newState) = executeNode child state
      in case status of
           Success -> executeDecorator (Repeater (count-1)) child newState
           Failure -> (Failure, newState)
           Running -> (Running, newState)
  
  UntilSuccess -> 
    let (status, newState) = executeNode child state
    in case status of
         Success -> (Success, newState)
         Failure -> executeDecorator UntilSuccess child newState
         Running -> (Running, newState)
  
  UntilFailure -> 
    let (status, newState) = executeNode child state
    in case status of
         Failure -> (Failure, newState)
         Success -> executeDecorator UntilFailure child newState
         Running -> (Running, newState)

-- 创建复杂行为树
createComplexBehaviorTree :: BehaviorTree
createComplexBehaviorTree = 
  let -- 主选择器
      mainSelector = SelectorNode [
        -- 紧急情况处理
        SequenceNode [
          ConditionNode IsInDanger,
          SelectorNode [
            ActionNode Defend,
            ActionNode (UseItem "TeleportScroll")
          ]
        ],
        -- 战斗行为
        SequenceNode [
          ConditionNode (EnemyNearby (0,0)),
          SelectorNode [
            SequenceNode [
              ConditionNode (HasItem "Sword"),
              ActionNode (Attack (0,0))
            ],
            ActionNode (Move (0,1))  -- 逃跑
          ]
        ],
        -- 探索行为
        DecoratorNode (Repeater 3) (
          SelectorNode [
            ActionNode (Move (1,0)),
            ActionNode (Move (0,1)),
            ActionNode (Move (-1,0)),
            ActionNode (Move (0,-1))
          ]
        )
      ]
  in BehaviorTree mainSelector "ComplexBehaviorAI"
```

### 4. 状态机

```haskell
-- 状态机状态
data AIState = 
  Idle
  | Patrol
  | Chase
  | Attack
  | Flee
  | Search
  deriving (Show, Eq)

-- 状态转换
data StateTransition = StateTransition
  { fromState :: AIState
  , toState :: AIState
  , condition :: GameState -> Bool
  , priority :: Int
  } deriving Show

-- 状态机
data StateMachine = StateMachine
  { currentState :: AIState
  , transitions :: [StateTransition]
  , stateActions :: [(AIState, GameAction)]
  } deriving Show

-- 创建状态机
createStateMachine :: StateMachine
createStateMachine = 
  let transitions = [
        StateTransition Idle Patrol (\state -> True) 1,
        StateTransition Patrol Chase (\state -> any (\enemy -> distance (playerPosition state) (enemyPosition enemy) < 5) (enemies state)) 2,
        StateTransition Chase Attack (\state -> any (\enemy -> distance (playerPosition state) (enemyPosition enemy) < 1) (enemies state)) 3,
        StateTransition Attack Flee (\state -> playerHealth state < 0.3) 4,
        StateTransition Flee Search (\state -> not (any (\enemy -> distance (playerPosition state) (enemyPosition enemy) < 3) (enemies state))) 1,
        StateTransition Search Patrol (\state -> True) 1
      ]
      
      actions = [
        (Idle, Wait),
        (Patrol, Move (1,0)),
        (Chase, Move (0,0)),  -- 朝向敌人移动
        (Attack, Attack (0,0)),
        (Flee, Move (-1,-1)),
        (Search, Move (0,1))
      ]
  in StateMachine Idle transitions actions

-- 执行状态机
executeStateMachine :: StateMachine -> GameState -> (GameAction, StateMachine)
executeStateMachine machine state = 
  let -- 检查状态转换
      validTransitions = filter (\trans -> 
                                  fromState trans == currentState machine && 
                                  condition trans state) (transitions machine)
      
      -- 选择优先级最高的转换
      bestTransition = if null validTransitions
                       then Nothing
                       else Just (maximumBy (\a b -> compare (priority a) (priority b)) validTransitions)
      
      -- 更新状态
      newState = case bestTransition of
                   Just trans -> toState trans
                   Nothing -> currentState machine
      
      -- 执行当前状态的动作
      action = getStateAction newState (stateActions machine)
      
      updatedMachine = machine { currentState = newState }
  in (action, updatedMachine)

-- 获取状态动作
getStateAction :: AIState -> [(AIState, GameAction)] -> GameAction
getStateAction state actions = 
  case lookup state actions of
    Just action -> action
    Nothing -> Wait  -- 默认动作
```

## 📊 应用实例

### 1. 角色AI系统

```haskell
-- 角色AI
data CharacterAI = CharacterAI
  { decisionTree :: DecisionTree
  , behaviorTree :: BehaviorTree
  , stateMachine :: StateMachine
  , pathfinding :: GameWorld -> Position -> Position -> Maybe [Position]
  } deriving Show

-- 创建角色AI
createCharacterAI :: CharacterAI
createCharacterAI = 
  CharacterAI 
    createSimpleDecisionTree
    createBehaviorTree
    createStateMachine
    aStarPathfinding

-- 执行角色AI
executeCharacterAI :: CharacterAI -> GameState -> GameAction
executeCharacterAI ai state = 
  let -- 使用决策树
      decisionAction = executeDecisionTree (decisionTree ai) state
      
      -- 使用行为树
      (behaviorStatus, _) = executeBehaviorTree (behaviorTree ai) state
      
      -- 使用状态机
      (stateAction, _) = executeStateMachine (stateMachine ai) state
      
      -- 选择最终动作（简化：优先使用决策树）
      finalAction = decisionAction
  in finalAction
```

### 2. 群体AI

```haskell
-- 群体AI
data SwarmAI = SwarmAI
  { agents :: [Agent]
  , flockingRules :: [FlockingRule]
  } deriving Show

-- 智能体
data Agent = Agent
  { agentId :: Int
  , agentPosition :: Position
  , agentVelocity :: (Double, Double)
  , agentType :: AgentType
  } deriving Show

-- 智能体类型
data AgentType = 
  Boid
  | Predator
  | Prey
  deriving Show

-- 群体规则
data FlockingRule = 
  Separation Double  -- 分离距离
  | Alignment Double  -- 对齐强度
  | Cohesion Double   -- 凝聚强度
  deriving Show

-- 创建群体AI
createSwarmAI :: Int -> SwarmAI
createSwarmAI numAgents = 
  let agents = [Agent i (i `mod` 10, i `div` 10) (0.0, 0.0) Boid | i <- [0..numAgents-1]]
      rules = [Separation 2.0, Alignment 0.5, Cohesion 0.3]
  in SwarmAI agents rules

-- 执行群体AI
executeSwarmAI :: SwarmAI -> SwarmAI
executeSwarmAI swarm = 
  let updatedAgents = map (updateAgent swarm) (agents swarm)
  in swarm { agents = updatedAgents }

-- 更新智能体
updateAgent :: SwarmAI -> Agent -> Agent
updateAgent swarm agent = 
  let -- 计算群体力
      separationForce = calculateSeparation agent (agents swarm)
      alignmentForce = calculateAlignment agent (agents swarm)
      cohesionForce = calculateCohesion agent (agents swarm)
      
      -- 合成力
      totalForce = addForces [separationForce, alignmentForce, cohesionForce]
      
      -- 更新位置和速度
      newVelocity = addVectors (agentVelocity agent) totalForce
      newPosition = addVectors (agentPosition agent) newVelocity
  in agent { agentPosition = newPosition, agentVelocity = newVelocity }

-- 计算分离力
calculateSeparation :: Agent -> [Agent] -> (Double, Double)
calculateSeparation agent allAgents = 
  let nearbyAgents = filter (\a -> agentId a /= agentId agent && 
                                   distance (agentPosition agent) (agentPosition a) < 2.0) allAgents
      separationVectors = map (\a -> 
                                let diff = subtractVectors (agentPosition agent) (agentPosition a)
                                    dist = distance (agentPosition agent) (agentPosition a)
                                in if dist > 0
                                   then scaleVector (1.0 / dist) diff
                                   else (0.0, 0.0)) nearbyAgents
  in if null separationVectors
     then (0.0, 0.0)
     else scaleVector (1.0 / fromIntegral (length separationVectors)) (sumVectors separationVectors)

-- 计算对齐力
calculateAlignment :: Agent -> [Agent] -> (Double, Double)
calculateAlignment agent allAgents = 
  let nearbyAgents = filter (\a -> agentId a /= agentId agent && 
                                   distance (agentPosition agent) (agentPosition a) < 5.0) allAgents
      averageVelocity = if null nearbyAgents
                        then (0.0, 0.0)
                        else scaleVector (1.0 / fromIntegral (length nearbyAgents)) 
                                        (sumVectors (map agentVelocity nearbyAgents))
  in averageVelocity

-- 计算凝聚力
calculateCohesion :: Agent -> [Agent] -> (Double, Double)
calculateCohesion agent allAgents = 
  let nearbyAgents = filter (\a -> agentId a /= agentId agent && 
                                   distance (agentPosition agent) (agentPosition a) < 5.0) allAgents
      centerOfMass = if null nearbyAgents
                     then agentPosition agent
                     else scaleVector (1.0 / fromIntegral (length nearbyAgents)) 
                                     (sumVectors (map agentPosition nearbyAgents))
      cohesionVector = subtractVectors centerOfMass (agentPosition agent)
  in cohesionVector

-- 向量操作
addVectors :: (Double, Double) -> (Double, Double) -> (Double, Double)
addVectors (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)

subtractVectors :: (Double, Double) -> (Double, Double) -> (Double, Double)
subtractVectors (x1, y1) (x2, y2) = (x1 - x2, y1 - y2)

scaleVector :: Double -> (Double, Double) -> (Double, Double)
scaleVector s (x, y) = (s * x, s * y)

sumVectors :: [(Double, Double)] -> (Double, Double)
sumVectors = foldl addVectors (0.0, 0.0)

addForces :: [(Double, Double)] -> (Double, Double)
addForces = sumVectors
```

### 3. 战术AI

```haskell
-- 战术AI
data TacticalAI = TacticalAI
  { formation :: Formation
  , tactics :: [Tactic]
  , currentTactic :: Maybe Tactic
  } deriving Show

-- 阵型
data Formation = 
  LineFormation
  | CircleFormation
  | WedgeFormation
  deriving Show

-- 战术
data Tactic = 
  Flanking
  | Ambush
  | Defensive
  | Aggressive
  deriving Show

-- 创建战术AI
createTacticalAI :: TacticalAI
createTacticalAI = 
  TacticalAI LineFormation [Flanking, Ambush, Defensive, Aggressive] Nothing

-- 执行战术AI
executeTacticalAI :: TacticalAI -> GameState -> [GameAction]
executeTacticalAI ai state = 
  let -- 选择战术
      selectedTactic = selectTactic ai state
      
      -- 执行战术
      actions = executeTactic selectedTactic state
  in actions

-- 选择战术
selectTactic :: TacticalAI -> GameState -> Tactic
selectTactic ai state = 
  let enemyCount = length (enemies state)
      playerHealth = playerHealth state
  in if playerHealth < 0.3
     then Defensive
     else if enemyCount > 3
          then Flanking
          else Aggressive

-- 执行战术
executeTactic :: Tactic -> GameState -> [GameAction]
executeTactic tactic state = case tactic of
  Flanking -> [Move (1,1), Attack (0,0)]
  Ambush -> [Wait, Attack (0,0)]
  Defensive -> [Defend, Move (0,1)]
  Aggressive -> [Attack (0,0), Move (1,0)]
```

## 🔗 相关理论

- [游戏引擎架构](../08-Game-Development/01-Game-Engine-Architecture.md)
- [图形渲染理论](../07-Computer-Graphics/01-Rendering-Theory.md)
- [物理仿真理论](../07-Computer-Graphics/03-Physics-Simulation.md)
- [机器学习理论](../14-Machine-Learning/01-Supervised-Learning.md)
- [优化算法理论](../10-Mathematical-Physics/03-Optimization-Theory.md)

## 📚 参考文献

1. Millington, I., & Funge, J. (2009). *Artificial Intelligence for Games*. CRC Press.
2. Buckland, M. (2004). *Programming Game AI by Example*. Wordware Publishing.
3. LaMothe, A. (2002). *Tricks of the Windows Game Programming Gurus*. Sams.

---

**文档版本**: 1.0.0  
**维护者**: AI Assistant  
**最后更新**: 2024年12月19日
