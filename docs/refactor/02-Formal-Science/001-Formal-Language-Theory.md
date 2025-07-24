# 形式语言理论（Formal Language Theory）

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

## 哲科视角与国际化扩展 Philosophical-Scientific Perspective & Internationalization

### 定义 Definition

- **中文**：形式语言理论是研究符号串集合及其生成、识别和变换机制的理论，是计算机科学、语言学和逻辑学的基础。它关注语法、语义、自动机、文法、正则表达式等形式系统。
- **English**: Formal language theory is the study of sets of strings of symbols and their mechanisms of generation, recognition, and transformation. It is foundational to computer science, linguistics, and logic, focusing on syntax, semantics, automata, grammars, regular expressions, and other formal systems.

### 历史与发展 History & Development

- **中文**：形式语言理论起源于20世纪初，Chomsky提出文法分层，Kleene、Turing等奠定了自动机与可计算性理论。现代形式语言理论与编译原理、自然语言处理、人工智能等深度融合。
- **English**: Formal language theory originated in the early 20th century, with Chomsky's hierarchy of grammars and foundational work by Kleene, Turing, and others on automata and computability. Modern formal language theory is deeply integrated with compiler theory, natural language processing, artificial intelligence, etc.

### 哲学科学特性分析 Philosophical-Scientific Feature Analysis

- **中文**：形式语言理论不仅关注符号系统的技术细节，更关涉语言本质、结构主义、可计算性、信息论等哲学基础。它与证明论、模型论、类型理论等共同构成现代形式科学的基石。
- **English**: Formal language theory is concerned not only with the technical details of symbolic systems, but also with philosophical foundations such as the nature of language, structuralism, computability, and information theory. Together with proof theory, model theory, and type theory, it forms the cornerstone of modern formal science.

### 应用 Applications

- **中文**：编译原理、词法分析、语法分析、正则表达式、自动机、自然语言处理、形式化验证、人工智能等。
- **English**: Compiler theory, lexical analysis, syntax analysis, regular expressions, automata, natural language processing, formal verification, artificial intelligence, etc.

### 例子 Examples

```haskell
-- Haskell: 字母表与语言的建模
import qualified Data.Set as Set

type Alphabet = Set.Set Char
type Language = Set.Set String

-- 语言连接
concatenate :: Language -> Language -> Language
concatenate lang1 lang2 = Set.fromList [s1 ++ s2 | s1 <- Set.toList lang1, s2 <- Set.toList lang2]
```

### 相关理论 Related Theories

- 证明论 Proof Theory
- 模型论 Model Theory
- 类型理论 Type Theory
- 自动机理论 Automata Theory
- 系统理论 System Theory
- 计算复杂性理论 Computational Complexity Theory

### 参考文献 References

- [1] Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
- [2] Chomsky, N. (1956). Three models for the description of language.
- [3] Wikipedia: Formal Language <https://en.wikipedia.org/wiki/Formal_language>
- [4] Types and Programming Languages, Benjamin C. Pierce

---

**相关链接**：

- [自动机理论](./006-Automata-Theory.md)
- [形式逻辑](./005-Formal-Logic.md)
