# 形式语言理论

## 概述

形式语言理论研究符号串的集合及其生成和识别机制，是计算机科学和语言学的基础理论。

## 基本概念

### 字母表和语言

```haskell
-- 字母表：符号的有限集合
type Alphabet = Set Char

-- 语言：字母表上符号串的集合
type Language = Set String

-- 空语言
emptyLanguage :: Language
emptyLanguage = Set.empty

-- 只包含空串的语言
epsilonLanguage :: Language
epsilonLanguage = Set.singleton ""
```

### 语言操作

```haskell
-- 语言连接
concatenate :: Language -> Language -> Language
concatenate lang1 lang2 = 
  Set.fromList [s1 ++ s2 | s1 <- Set.toList lang1, s2 <- Set.toList lang2]

-- 语言幂运算
power :: Language -> Int -> Language
power lang 0 = epsilonLanguage
power lang n = concatenate lang (power lang (n-1))

-- Kleene星号
kleeneStar :: Language -> Language
kleeneStar lang = Set.unions [power lang n | n <- [0..]]
```

## 文法

### 上下文无关文法

```haskell
-- 产生式
data Production = Production String [String]

-- 上下文无关文法
data CFG = CFG
  { startSymbol :: String
  , productions :: [Production]
  }

-- 示例：简单算术表达式
arithmeticGrammar :: CFG
arithmeticGrammar = CFG
  { startSymbol = "E"
  , productions = 
    [ Production "E" ["E", "+", "T"]
    , Production "E" ["T"]
    , Production "T" ["T", "*", "F"]
    , Production "T" ["F"]
    , Production "F" ["(", "E", ")"]
    , Production "F" ["id"]
    ]
  }
```

### 推导

```haskell
-- 推导步骤
data DerivationStep = DerivationStep String String Production

-- 推导序列
type Derivation = [DerivationStep]

-- 执行推导
derive :: CFG -> String -> [String]
derive cfg start = 
  let productions = cfg.productions
  in derive' start productions
  where
    derive' current prods = 
      case findApplicable current prods of
        Nothing -> [current]
        Just prod -> current : derive' (applyProduction current prod) prods
```

## 自动机

### 有限状态自动机

```haskell
-- 有限状态自动机
data FSA = FSA
  { states :: Set String
  , alphabet :: Alphabet
  , transitions :: Map (String, Char) (Set String)
  , startState :: String
  , acceptStates :: Set String
  }

-- 示例：识别偶数个a的自动机
evenA :: FSA
evenA = FSA
  { states = Set.fromList ["q0", "q1"]
  , alphabet = Set.fromList ['a', 'b']
  , transitions = Map.fromList
    [ (("q0", 'a'), Set.singleton "q1")
    , (("q0", 'b'), Set.singleton "q0")
    , (("q1", 'a'), Set.singleton "q0")
    , (("q1", 'b'), Set.singleton "q1")
    ]
  , startState = "q0"
  , acceptStates = Set.singleton "q0"
  }
```

### 自动机执行

```haskell
-- 执行自动机
runFSA :: FSA -> String -> Bool
runFSA fsa input = 
  let finalStates = execute fsa fsa.startState input
  in not (Set.null (Set.intersection finalStates fsa.acceptStates))

-- 执行步骤
execute :: FSA -> String -> String -> Set String
execute fsa currentState [] = Set.singleton currentState
execute fsa currentState (c:cs) = 
  let nextStates = Map.findWithDefault Set.empty (currentState, c) fsa.transitions
  in Set.unions [execute fsa nextState cs | nextState <- Set.toList nextStates]
```

## 正则表达式

### 正则表达式定义

```haskell
-- 正则表达式
data Regex = Empty
           | Epsilon
           | Char Char
           | Concat Regex Regex
           | Union Regex Regex
           | Star Regex

-- 示例：匹配邮箱地址
emailRegex :: Regex
emailRegex = Concat
  (Concat (Star (Union (Char 'a') (Char 'b'))) (Char '@'))
  (Concat (Star (Union (Char 'a') (Char 'b'))) (Char '.'))
```

### 正则表达式匹配

```haskell
-- 匹配正则表达式
match :: Regex -> String -> Bool
match Empty _ = False
match Epsilon "" = True
match Epsilon _ = False
match (Char c) [x] = c == x
match (Char _) _ = False
match (Concat r1 r2) s = 
  any (\i -> match r1 (take i s) && match r2 (drop i s)) [0..length s]
match (Union r1 r2) s = match r1 s || match r2 s
match (Star r) s = 
  s == "" || any (\i -> match r (take i s) && match (Star r) (drop i s)) [1..length s]
```

## 泵引理

### 正则语言的泵引理

```haskell
-- 泵引理：对于正则语言L，存在泵长度p
-- 对于所有长度≥p的串w∈L，可以写成w=xyz
-- 其中|xy|≤p，|y|≥1，且对所有i≥0，xyⁱz∈L

pumpingLemma :: Language -> Bool
pumpingLemma lang = 
  let p = findPumpLength lang
  in all (\w -> length w >= p -> canPump w p lang) (Set.toList lang)

-- 检查是否可以泵
canPump :: String -> Int -> Language -> Bool
canPump w p lang = 
  any (\i -> length w >= p && 
             let (x, rest) = splitAt i w
                 (y, z) = splitAt 1 rest
             in length (x ++ y) <= p && 
                length y >= 1 && 
                all (\j -> Set.member (x ++ concat (replicate j y) ++ z) lang) [0..])
      [0..length w]
```

## 应用

### 词法分析

```haskell
-- 词法单元
data Token = TInt Int
           | TPlus
           | TMinus
           | TTimes
           | TLParen
           | TRParen
           | TEOF

-- 词法分析器
lexer :: String -> [Token]
lexer = undefined -- 实现词法分析
```

### 语法分析

```haskell
-- 抽象语法树
data AST = Num Int
         | BinOp AST Op AST

data Op = Add | Sub | Mul

-- 递归下降解析器
parse :: [Token] -> Maybe AST
parse = undefined -- 实现语法分析
```

## 工具

- **Flex**: 词法分析器生成器
- **Bison**: 语法分析器生成器
- **ANTLR**: 解析器生成器

---

**相关链接**：

- [自动机理论](./006-Automata-Theory.md)
- [形式逻辑](./005-Formal-Logic.md)
