# 自动机理论

## 概述

自动机理论研究抽象计算模型，包括有限状态自动机、下推自动机、图灵机等。

## 有限状态自动机 (FSA)

### 确定性有限自动机 (DFA)

```haskell
-- 确定性有限自动机
data DFA = DFA
  { states :: Set String
  , alphabet :: Set Char
  , transition :: Map (String, Char) String
  , startState :: String
  , acceptStates :: Set String
  }

-- 示例：识别以ab结尾的字符串
dfaExample :: DFA
dfaExample = DFA
  { states = Set.fromList ["q0", "q1", "q2"]
  , alphabet = Set.fromList ['a', 'b']
  , transition = Map.fromList
    [ (("q0", 'a'), "q1")
    , (("q0", 'b'), "q0")
    , (("q1", 'a'), "q1")
    , (("q1", 'b'), "q2")
    , (("q2", 'a'), "q1")
    , (("q2", 'b'), "q0")
    ]
  , startState = "q0"
  , acceptStates = Set.singleton "q2"
  }
```

### 非确定性有限自动机 (NFA)

```haskell
-- 非确定性有限自动机
data NFA = NFA
  { states :: Set String
  , alphabet :: Set Char
  , transitions :: Map (String, Char) (Set String)
  , startStates :: Set String
  , acceptStates :: Set String
  }

-- 示例：识别包含aa或bb的字符串
nfaExample :: NFA
nfaExample = NFA
  { states = Set.fromList ["q0", "q1", "q2", "q3", "q4"]
  , alphabet = Set.fromList ['a', 'b']
  , transitions = Map.fromList
    [ (("q0", 'a'), Set.fromList ["q0", "q1"])
    , (("q0", 'b'), Set.fromList ["q0", "q3"])
    , (("q1", 'a'), Set.singleton "q2")
    , (("q3", 'b'), Set.singleton "q4")
    ]
  , startStates = Set.singleton "q0"
  , acceptStates = Set.fromList ["q2", "q4"]
  }
```

### 自动机执行

```haskell
-- 执行DFA
runDFA :: DFA -> String -> Bool
runDFA dfa input = 
  let finalState = executeDFA dfa dfa.startState input
  in Set.member finalState dfa.acceptStates

executeDFA :: DFA -> String -> String -> String
executeDFA dfa currentState [] = currentState
executeDFA dfa currentState (c:cs) = 
  let nextState = Map.findWithDefault "" (currentState, c) dfa.transition
  in executeDFA dfa nextState cs

-- 执行NFA
runNFA :: NFA -> String -> Bool
runNFA nfa input = 
  let finalStates = executeNFA nfa nfa.startStates input
  in not (Set.null (Set.intersection finalStates nfa.acceptStates))

executeNFA :: NFA -> Set String -> String -> Set String
executeNFA nfa currentStates [] = currentStates
executeNFA nfa currentStates (c:cs) = 
  let nextStates = Set.unions 
        [ Map.findWithDefault Set.empty (state, c) nfa.transitions 
        | state <- Set.toList currentStates ]
  in executeNFA nfa nextStates cs
```

## 下推自动机 (PDA)

### 下推自动机定义

```haskell
-- 下推自动机
data PDA = PDA
  { states :: Set String
  , inputAlphabet :: Set Char
  , stackAlphabet :: Set Char
  , transitions :: [PDATransition]
  , startState :: String
  , startStack :: Char
  , acceptStates :: Set String
  }

-- PDA转换
data PDATransition = PDATransition
  { fromState :: String
  , inputChar :: Maybe Char
  , stackTop :: Char
  , toState :: String
  , stackPush :: [Char]
  }

-- 示例：识别回文
pdaExample :: PDA
pdaExample = PDA
  { states = Set.fromList ["q0", "q1", "q2"]
  , inputAlphabet = Set.fromList ['a', 'b']
  , stackAlphabet = Set.fromList ['Z', 'A', 'B']
  , transitions = 
    [ PDATransition "q0" (Just 'a') 'Z' "q0" ['A', 'Z']
    , PDATransition "q0" (Just 'b') 'Z' "q0" ['B', 'Z']
    , PDATransition "q0" (Just 'a') 'A' "q0" ['A', 'A']
    , PDATransition "q0" (Just 'b') 'A' "q0" ['B', 'A']
    , PDATransition "q0" (Just 'a') 'B' "q0" ['A', 'B']
    , PDATransition "q0" (Just 'b') 'B' "q0" ['B', 'B']
    , PDATransition "q0" Nothing 'A' "q1" []
    , PDATransition "q0" Nothing 'B' "q1" []
    , PDATransition "q1" (Just 'a') 'A' "q1" []
    , PDATransition "q1" (Just 'b') 'B' "q1" []
    , PDATransition "q1" Nothing 'Z' "q2" []
    ]
  , startState = "q0"
  , startStack = 'Z'
  , acceptStates = Set.singleton "q2"
  }
```

### PDA执行

```haskell
-- PDA配置
data PDAConfig = PDAConfig
  { state :: String
  , input :: String
  , stack :: [Char]
  }

-- 执行PDA
runPDA :: PDA -> String -> Bool
runPDA pda input = 
  let initialConfig = PDAConfig pda.startState input [pda.startStack]
      finalConfigs = executePDA pda [initialConfig]
  in any (\config -> Set.member (state config) pda.acceptStates && 
                     null (input config)) finalConfigs

-- 执行步骤
executePDA :: PDA -> [PDAConfig] -> [PDAConfig]
executePDA pda configs = 
  let nextConfigs = concatMap (stepPDA pda) configs
  in if null nextConfigs then configs else executePDA pda nextConfigs

-- 单步执行
stepPDA :: PDA -> PDAConfig -> [PDAConfig]
stepPDA pda config = 
  [ PDAConfig (toState trans) 
              (drop 1 (input config)) 
              (stackPush trans ++ tail (stack config))
  | trans <- pda.transitions
  , fromState trans == state config
  , maybe True (== head (input config)) (inputChar trans)
  , stackTop trans == head (stack config)
  ]
```

## 图灵机 (TM)

### 图灵机定义

```haskell
-- 图灵机
data TuringMachine = TuringMachine
  { states :: Set String
  , alphabet :: Set Char
  , tapeAlphabet :: Set Char
  , transitions :: Map (String, Char) (String, Char, Direction)
  , startState :: String
  , acceptState :: String
  , rejectState :: String
  }

data Direction = Left | Right | Stay

-- 示例：识别a^n b^n c^n
tmExample :: TuringMachine
tmExample = TuringMachine
  { states = Set.fromList ["q0", "q1", "q2", "q3", "q4", "qaccept", "qreject"]
  , alphabet = Set.fromList ['a', 'b', 'c']
  , tapeAlphabet = Set.fromList ['a', 'b', 'c', 'X', 'Y', 'Z', 'B']
  , transitions = Map.fromList
    [ (("q0", 'a'), ("q1", 'X', Right))
    , (("q1", 'a'), ("q1", 'a', Right))
    , (("q1", 'b'), ("q2", 'Y', Right))
    , (("q2", 'b'), ("q2", 'b', Right))
    , (("q2", 'c'), ("q3", 'Z', Left))
    , (("q3", 'Z'), ("q3", 'Z', Left))
    , (("q3", 'b'), ("q3", 'b', Left))
    , (("q3", 'Y'), ("q3", 'Y', Left))
    , (("q3", 'a'), ("q3", 'a', Left))
    , (("q3", 'X'), ("q0", 'X', Right))
    , (("q0", 'Y'), ("q4", 'Y', Right))
    , (("q4", 'Y'), ("q4", 'Y', Right))
    , (("q4", 'Z'), ("q4", 'Z', Right))
    , (("q4", 'B'), ("qaccept", 'B', Stay))
    ]
  , startState = "q0"
  , acceptState = "qaccept"
  , rejectState = "qreject"
  }
```

### 图灵机执行

```haskell
-- 图灵机配置
data TMConfig = TMConfig
  { state :: String
  , tape :: [Char]
  , head :: Int
  }

-- 执行图灵机
runTM :: TuringMachine -> String -> Bool
runTM tm input = 
  let initialConfig = TMConfig tm.startState (input ++ ['B']) 0
      finalConfig = executeTM tm initialConfig
  in state finalConfig == tm.acceptState

-- 执行步骤
executeTM :: TuringMachine -> TMConfig -> TMConfig
executeTM tm config = 
  case Map.lookup (state config, tape config !! head config) tm.transitions of
    Nothing -> config
    Just (newState, newSymbol, direction) -> 
      let newTape = updateAt (head config) newSymbol (tape config)
          newHead = case direction of
            Left -> max 0 (head config - 1)
            Right -> head config + 1
            Stay -> head config
      in executeTM tm (TMConfig newState newTape newHead)
```

## 自动机等价性

### DFA最小化

```haskell
-- 状态等价性
equivalentStates :: DFA -> String -> String -> Bool
equivalentStates dfa s1 s2 = 
  all (\w -> runDFA dfa w == runDFA dfa w) (generateStrings dfa.alphabet)

-- 最小化DFA
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = 
  let equivalenceClasses = findEquivalenceClasses dfa
      minimizedStates = map (head . snd) equivalenceClasses
      minimizedTransitions = buildMinimizedTransitions dfa equivalenceClasses
  in DFA minimizedStates dfa.alphabet minimizedTransitions 
       (findMinimizedStartState dfa equivalenceClasses)
       (findMinimizedAcceptStates dfa equivalenceClasses)
```

## 应用

### 编译器

```haskell
-- 词法分析器
lexicalAnalyzer :: DFA -> String -> [Token]
lexicalAnalyzer dfa input = 
  let tokens = scanTokens dfa input
  in filter (/= Whitespace) tokens

-- 语法分析器
syntaxAnalyzer :: PDA -> [Token] -> Maybe AST
syntaxAnalyzer pda tokens = 
  if runPDA pda (map tokenToChar tokens) 
  then buildAST tokens 
  else Nothing
```

### 模式匹配

```haskell
-- 字符串匹配
patternMatch :: DFA -> String -> [Int]
patternMatch dfa text = 
  [i | i <- [0..length text - 1], 
       runDFA dfa (drop i text)]

-- 正则表达式匹配
regexMatch :: String -> String -> Bool
regexMatch pattern text = 
  let dfa = regexToDFA pattern
  in runDFA dfa text
```

---

**相关链接**：

- [形式语言理论](./001-Formal-Language-Theory.md)
- [计算复杂性](./012-Computational-Complexity.md)
