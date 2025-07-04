# 博弈论 (Game Theory)

## 概述

博弈论是研究理性决策者之间战略互动的数学理论，广泛应用于经济学、政治学、计算机科学等领域。它分析在竞争或合作环境中，参与者如何做出最优决策。

## 核心概念

### 1. 博弈要素

- **参与者 (Players)**: 做出决策的个体或组织
- **策略 (Strategies)**: 每个参与者可选择的行动方案
- **收益 (Payoffs)**: 每个策略组合对应的结果
- **信息 (Information)**: 参与者对博弈状态的了解程度

### 2. 博弈类型

- **零和博弈**: 一方收益等于另一方损失
- **非零和博弈**: 总收益可变
- **合作博弈**: 参与者可以形成联盟
- **非合作博弈**: 参与者独立决策

## 理论基础

### 1. 纳什均衡

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct Player {
    id: String,
    strategies: Vec<String>,
}

#[derive(Debug, Clone)]
struct Game {
    players: Vec<Player>,
    payoffs: HashMap<(String, String), (f64, f64)>, // (player1_payoff, player2_payoff)
}

impl Game {
    fn new() -> Self {
        Self {
            players: Vec::new(),
            payoffs: HashMap::new(),
        }
    }
    
    fn add_player(&mut self, player: Player) {
        self.players.push(player);
    }
    
    fn set_payoff(&mut self, strategy1: String, strategy2: String, payoff1: f64, payoff2: f64) {
        self.payoffs.insert((strategy1, strategy2), (payoff1, payoff2));
    }
    
    fn find_nash_equilibrium(&self) -> Vec<(String, String)> {
        let mut equilibria = Vec::new();
        
        // 检查每个策略组合是否为纳什均衡
        for player1_strategy in &self.players[0].strategies {
            for player2_strategy in &self.players[1].strategies {
                if self.is_nash_equilibrium(player1_strategy, player2_strategy) {
                    equilibria.push((player1_strategy.clone(), player2_strategy.clone()));
                }
            }
        }
        
        equilibria
    }
    
    fn is_nash_equilibrium(&self, strategy1: &str, strategy2: &str) -> bool {
        let current_payoff = self.payoffs.get(&(strategy1.to_string(), strategy2.to_string()));
        
        // 检查玩家1是否有更好的策略
        for alt_strategy in &self.players[0].strategies {
            if alt_strategy != strategy1 {
                let alt_payoff = self.payoffs.get(&(alt_strategy.clone(), strategy2.to_string()));
                if let (Some(current), Some(alt)) = (current_payoff, alt_payoff) {
                    if alt.0 > current.0 {
                        return false;
                    }
                }
            }
        }
        
        // 检查玩家2是否有更好的策略
        for alt_strategy in &self.players[1].strategies {
            if alt_strategy != strategy2 {
                let alt_payoff = self.payoffs.get(&(strategy1.to_string(), alt_strategy.clone()));
                if let (Some(current), Some(alt)) = (current_payoff, alt_payoff) {
                    if alt.1 > current.1 {
                        return false;
                    }
                }
            }
        }
        
        true
    }
}

// 囚徒困境示例
fn create_prisoners_dilemma() -> Game {
    let mut game = Game::new();
    
    let player1 = Player {
        id: "Player1".to_string(),
        strategies: vec!["Cooperate".to_string(), "Defect".to_string()],
    };
    
    let player2 = Player {
        id: "Player2".to_string(),
        strategies: vec!["Cooperate".to_string(), "Defect".to_string()],
    };
    
    game.add_player(player1);
    game.add_player(player2);
    
    // 设置收益矩阵
    // (Cooperate, Cooperate) -> (3, 3)
    // (Cooperate, Defect) -> (0, 5)
    // (Defect, Cooperate) -> (5, 0)
    // (Defect, Defect) -> (1, 1)
    
    game.set_payoff("Cooperate".to_string(), "Cooperate".to_string(), 3.0, 3.0);
    game.set_payoff("Cooperate".to_string(), "Defect".to_string(), 0.0, 5.0);
    game.set_payoff("Defect".to_string(), "Cooperate".to_string(), 5.0, 0.0);
    game.set_payoff("Defect".to_string(), "Defect".to_string(), 1.0, 1.0);
    
    game
}
```

### 2. 重复博弈

```rust
#[derive(Debug, Clone)]
struct RepeatedGame {
    base_game: Game,
    discount_factor: f64,
    rounds: usize,
}

impl RepeatedGame {
    fn new(base_game: Game, discount_factor: f64, rounds: usize) -> Self {
        Self {
            base_game,
            discount_factor,
            rounds,
        }
    }
    
    fn calculate_total_payoff(&self, strategy_profile: &[(String, String)]) -> (f64, f64) {
        let mut total_payoff1 = 0.0;
        let mut total_payoff2 = 0.0;
        
        for (i, (strategy1, strategy2)) in strategy_profile.iter().enumerate() {
            if let Some((payoff1, payoff2)) = self.base_game.payoffs.get(&(strategy1.clone(), strategy2.clone())) {
                let discount = self.discount_factor.powi(i as i32);
                total_payoff1 += payoff1 * discount;
                total_payoff2 += payoff2 * discount;
            }
        }
        
        (total_payoff1, total_payoff2)
    }
    
    fn tit_for_tat_strategy(&self, opponent_history: &[String]) -> String {
        if opponent_history.is_empty() {
            "Cooperate".to_string()
        } else {
            opponent_history.last().unwrap().clone()
        }
    }
}
```

## Haskell实现示例

```haskell
import Data.Map (Map)
import qualified Data.Map as Map

-- 玩家定义
data Player = Player
    { playerId :: String
    , strategies :: [String]
    }

-- 博弈定义
data Game = Game
    { players :: [Player]
    , payoffs :: Map (String, String) (Double, Double)
    }

-- 创建博弈
createGame :: Game
createGame = Game
    { players = []
    , payoffs = Map.empty
    }

-- 添加玩家
addPlayer :: Game -> Player -> Game
addPlayer game player = game { players = players game ++ [player] }

-- 设置收益
setPayoff :: Game -> String -> String -> Double -> Double -> Game
setPayoff game strategy1 strategy2 payoff1 payoff2 = 
    game { payoffs = Map.insert (strategy1, strategy2) (payoff1, payoff2) (payoffs game) }

-- 检查纳什均衡
isNashEquilibrium :: Game -> String -> String -> Bool
isNashEquilibrium game strategy1 strategy2 = 
    let currentPayoff = Map.lookup (strategy1, strategy2) (payoffs game)
        player1Strategies = strategies (players game !! 0)
        player2Strategies = strategies (players game !! 1)
        
        -- 检查玩家1是否有更好的策略
        player1Better = any (\altStrategy -> 
            if altStrategy /= strategy1
            then case (currentPayoff, Map.lookup (altStrategy, strategy2) (payoffs game)) of
                (Just (current1, _), Just (alt1, _)) -> alt1 > current1
                _ -> False
            else False
        ) player1Strategies
        
        -- 检查玩家2是否有更好的策略
        player2Better = any (\altStrategy -> 
            if altStrategy /= strategy2
            then case (currentPayoff, Map.lookup (strategy1, altStrategy) (payoffs game)) of
                (Just (_, current2), Just (_, alt2)) -> alt2 > current2
                _ -> False
            else False
        ) player2Strategies
        
    in not player1Better && not player2Better

-- 寻找纳什均衡
findNashEquilibria :: Game -> [(String, String)]
findNashEquilibria game = 
    let player1Strategies = strategies (players game !! 0)
        player2Strategies = strategies (players game !! 1)
    in [(s1, s2) | s1 <- player1Strategies, s2 <- player2Strategies, 
                   isNashEquilibrium game s1 s2]

-- 囚徒困境
prisonersDilemma :: Game
prisonersDilemma = 
    let game = createGame
        player1 = Player "Player1" ["Cooperate", "Defect"]
        player2 = Player "Player2" ["Cooperate", "Defect"]
        gameWithPlayers = addPlayer (addPlayer game player1) player2
    in foldl (\g ((s1, s2), (p1, p2)) -> setPayoff g s1 s2 p1 p2) gameWithPlayers
        [ (("Cooperate", "Cooperate"), (3.0, 3.0))
        , (("Cooperate", "Defect"), (0.0, 5.0))
        , (("Defect", "Cooperate"), (5.0, 0.0))
        , (("Defect", "Defect"), (1.0, 1.0))
        ]

-- 重复博弈
data RepeatedGame = RepeatedGame
    { baseGame :: Game
    , discountFactor :: Double
    , rounds :: Int
    }

-- 计算总收益
calculateTotalPayoff :: RepeatedGame -> [(String, String)] -> (Double, Double)
calculateTotalPayoff repeatedGame strategyProfile = 
    let baseGame = baseGame repeatedGame
        discountFactor = discountFactor repeatedGame
        payoffs = payoffs baseGame
        
        calculatePayoff :: Int -> (String, String) -> (Double, Double)
        calculatePayoff round (s1, s2) = 
            case Map.lookup (s1, s2) payoffs of
                Just (p1, p2) -> 
                    let discount = discountFactor ^ round
                    in (p1 * discount, p2 * discount)
                Nothing -> (0.0, 0.0)
        
        payoffsList = zipWith calculatePayoff [0..] strategyProfile
    in foldl (\(acc1, acc2) (p1, p2) -> (acc1 + p1, acc2 + p2)) (0.0, 0.0) payoffsList

-- 以牙还牙策略
titForTat :: [String] -> String
titForTat opponentHistory = 
    case opponentHistory of
        [] -> "Cooperate"
        history -> last history
```

## Lean实现思路

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- 玩家定义
structure Player where
  playerId : String
  strategies : List String

-- 博弈定义
structure Game where
  players : List Player
  payoffs : HashMap (String × String) (Float × Float)

-- 创建博弈
def createGame : Game :=
  { players := []
    payoffs := HashMap.empty
  }

-- 添加玩家
def addPlayer (game : Game) (player : Player) : Game :=
  { game with players := game.players ++ [player] }

-- 设置收益
def setPayoff (game : Game) (strategy1 strategy2 : String) (payoff1 payoff2 : Float) : Game :=
  { game with payoffs := game.payoffs.insert (strategy1, strategy2) (payoff1, payoff2) }

-- 检查纳什均衡
def isNashEquilibrium (game : Game) (strategy1 strategy2 : String) : Bool :=
  let currentPayoff := game.payoffs.find? (strategy1, strategy2)
  let player1Strategies := game.players.head?.map Player.strategies |>.getD []
  let player2Strategies := game.players.get? 1 |>.map Player.strategies |>.getD []
  
  -- 检查玩家1是否有更好的策略
  let player1Better := player1Strategies.any fun altStrategy =>
    if altStrategy != strategy1
    then 
      let altPayoff := game.payoffs.find? (altStrategy, strategy2)
      match currentPayoff, altPayoff with
      | some (current1, _), some (alt1, _) => alt1 > current1
      | _, _ => false
    else false
  
  -- 检查玩家2是否有更好的策略
  let player2Better := player2Strategies.any fun altStrategy =>
    if altStrategy != strategy2
    then 
      let altPayoff := game.payoffs.find? (strategy1, altStrategy)
      match currentPayoff, altPayoff with
      | some (_, current2), some (_, alt2) => alt2 > current2
      | _, _ => false
    else false
  
  not player1Better && not player2Better

-- 寻找纳什均衡
def findNashEquilibria (game : Game) : List (String × String) :=
  let player1Strategies := game.players.head?.map Player.strategies |>.getD []
  let player2Strategies := game.players.get? 1 |>.map Player.strategies |>.getD []
  
  player1Strategies.bind fun s1 =>
    player2Strategies.filter fun s2 =>
      isNashEquilibrium game s1 s2

-- 囚徒困境
def prisonersDilemma : Game :=
  let game := createGame
  let player1 := { playerId := "Player1", strategies := ["Cooperate", "Defect"] }
  let player2 := { playerId := "Player2", strategies := ["Cooperate", "Defect"] }
  let gameWithPlayers := addPlayer (addPlayer game player1) player2
  
  gameWithPlayers
    |> setPayoff "Cooperate" "Cooperate" 3.0 3.0
    |> setPayoff "Cooperate" "Defect" 0.0 5.0
    |> setPayoff "Defect" "Cooperate" 5.0 0.0
    |> setPayoff "Defect" "Defect" 1.0 1.0

-- 重复博弈
structure RepeatedGame where
  baseGame : Game
  discountFactor : Float
  rounds : Nat

-- 计算总收益
def calculateTotalPayoff (repeatedGame : RepeatedGame) (strategyProfile : List (String × String)) : Float × Float :=
  let baseGame := repeatedGame.baseGame
  let discountFactor := repeatedGame.discountFactor
  let payoffs := baseGame.payoffs
  
  let calculatePayoff (round : Nat) (strategy : String × String) : Float × Float :=
    match payoffs.find? strategy with
    | some (p1, p2) => 
      let discount := discountFactor ^ round
      (p1 * discount, p2 * discount)
    | none => (0.0, 0.0)
  
  let payoffsList := strategyProfile.enum.map fun (round, strategy) =>
    calculatePayoff round strategy
  
  payoffsList.foldl (fun (acc1, acc2) (p1, p2) => (acc1 + p1, acc2 + p2)) (0.0, 0.0)

-- 以牙还牙策略
def titForTat (opponentHistory : List String) : String :=
  match opponentHistory with
  | [] => "Cooperate"
  | history => history.getLast |>.getD "Cooperate"
```

## 博弈类型分析

### 1. 零和博弈

- **特点**: 一方收益等于另一方损失
- **例子**: 石头剪刀布、象棋
- **策略**: 最小化最大损失

### 2. 非零和博弈

- **特点**: 总收益可变
- **例子**: 囚徒困境、协调博弈
- **策略**: 寻找纳什均衡

### 3. 合作博弈

- **特点**: 参与者可以形成联盟
- **例子**: 联盟形成、资源分配
- **策略**: 夏普利值、核心

### 4. 重复博弈

- **特点**: 博弈重复进行
- **例子**: 商业竞争、国际关系
- **策略**: 以牙还牙、触发策略

## 应用场景

### 1. 经济学

- 市场均衡分析
- 拍卖机制设计
- 寡头垄断竞争

### 2. 政治学

- 国际关系分析
- 投票机制设计
- 谈判策略

### 3. 计算机科学

- 算法博弈论
- 机制设计
- 多智能体系统

### 4. 生物学

- 进化博弈论
- 种群动态
- 合作演化

## 最佳实践

### 1. 博弈建模

- 明确参与者和策略
- 准确设定收益函数
- 考虑信息结构

### 2. 均衡分析

- 寻找纯策略均衡
- 计算混合策略均衡
- 分析均衡稳定性

### 3. 策略设计

- 考虑重复博弈效应
- 设计激励机制
- 平衡合作与竞争

### 4. 实际应用

- 验证模型假设
- 考虑现实约束
- 评估策略效果

## 性能考虑

### 1. 计算复杂度

- 均衡计算效率
- 策略空间大小
- 算法优化

### 2. 信息处理

- 不完全信息处理
- 动态信息更新
- 不确定性建模

### 3. 可扩展性

- 多参与者博弈
- 复杂策略空间
- 分布式计算

## 总结

博弈论为理解战略互动提供了强大的分析工具。通过深入理解博弈类型、均衡概念和策略设计，可以在各种复杂环境中做出最优决策，为实际应用提供理论指导。
