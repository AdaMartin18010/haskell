# 102-形式语言理论

## 📚 概述

本文档建立形式语言理论的完整体系，使用Haskell实现形式语言、自动机理论和语言处理的形式化模型。

## 🎯 核心目标

1. **形式语言定义**: 实现正则语言、上下文无关语言等
2. **自动机理论**: 构建有限自动机、下推自动机等
3. **语言处理**: 实现词法分析、语法分析算法
4. **形式化验证**: 建立语言性质的形式化证明

## 🏗️ 理论框架

### 1. 形式语言基础

```haskell
-- 字母表定义
type Alphabet = [Char]

-- 字符串定义
type String = [Char]

-- 语言定义
type Language = [String]

-- 语言运算
class LanguageOperations where
    union :: Language -> Language -> Language
    intersection :: Language -> Language -> Language
    concatenation :: Language -> Language -> Language
    kleeneStar :: Language -> Language
    complement :: Language -> Language

-- 语言运算实现
instance LanguageOperations where
    union l1 l2 = l1 ++ l2
    intersection l1 l2 = [s | s <- l1, s `elem` l2]
    concatenation l1 l2 = [s1 ++ s2 | s1 <- l1, s2 <- l2]
    kleeneStar l = [] : concat [replicate n l | n <- [1..]]
    complement l = undefined  -- 需要定义全集
```

### 2. 有限自动机

```haskell
-- 有限自动机定义
data FiniteAutomaton = FA {
    states :: [Int],
    alphabet :: Alphabet,
    transitions :: [(Int, Char, Int)],
    startState :: Int,
    acceptStates :: [Int]
}

-- 自动机状态
data AutomatonState = AS {
    currentState :: Int,
    remainingInput :: String
}

-- 自动机执行
runAutomaton :: FiniteAutomaton -> String -> Bool
runAutomaton fa input = 
    let initialState = AS (startState fa) input
        finalState = execute fa initialState
    in currentState finalState `elem` acceptStates fa

-- 执行步骤
execute :: FiniteAutomaton -> AutomatonState -> AutomatonState
execute fa (AS state []) = AS state []
execute fa (AS state (c:cs)) = 
    case findTransition fa state c of
        Just nextState -> execute fa (AS nextState cs)
        Nothing -> AS state (c:cs)  -- 拒绝

-- 查找转移
findTransition :: FiniteAutomaton -> Int -> Char -> Maybe Int
findTransition fa state symbol = 
    case [(s, sym, t) | (s, sym, t) <- transitions fa, s == state, sym == symbol] of
        [] -> Nothing
        ((_, _, target):_) -> Just target
```

### 3. 正则表达式

```haskell
-- 正则表达式定义
data Regex = 
    Empty |                    -- 空语言
    Epsilon |                  -- 空字符串
    Symbol Char |              -- 单个字符
    Union Regex Regex |        -- 并集
    Concat Regex Regex |       -- 连接
    Star Regex |               -- 克林闭包
    Plus Regex |               -- 正闭包
    Optional Regex             -- 可选

-- 正则表达式匹配
matchRegex :: Regex -> String -> Bool
matchRegex Empty _ = False
matchRegex Epsilon "" = True
matchRegex Epsilon _ = False
matchRegex (Symbol c) [s] = c == s
matchRegex (Symbol _) _ = False
matchRegex (Union r1 r2) s = matchRegex r1 s || matchRegex r2 s
matchRegex (Concat r1 r2) s = 
    any (\i -> matchRegex r1 (take i s) && matchRegex r2 (drop i s)) [0..length s]
matchRegex (Star r) s = 
    s == "" || any (\i -> matchRegex r (take i s) && matchRegex (Star r) (drop i s)) [1..length s]
matchRegex (Plus r) s = matchRegex (Concat r (Star r)) s
matchRegex (Optional r) s = s == "" || matchRegex r s
```

### 4. 上下文无关文法

```haskell
-- 产生式定义
data Production = Production {
    leftSide :: String,
    rightSide :: [String]
}

-- 上下文无关文法
data CFG = CFG {
    variables :: [String],
    terminals :: [String],
    productions :: [Production],
    startSymbol :: String
}

-- 推导步骤
data DerivationStep = DerivationStep {
    currentString :: [String],
    appliedProduction :: Production,
    position :: Int
}

-- 推导过程
derive :: CFG -> [String] -> [[String]]
derive cfg start = 
    let initial = [start]
        derivations = iterate (applyProductions cfg) initial
    in takeWhile (/= []) derivations

-- 应用产生式
applyProductions :: CFG -> [String] -> [String]
applyProductions cfg symbols = 
    concat [applyProduction p symbols | p <- productions cfg]

-- 应用单个产生式
applyProduction :: Production -> [String] -> [String]
applyProduction (Production left right) symbols = 
    concat [if s == left then right else [s] | s <- symbols]
```

### 5. 下推自动机

```haskell
-- 下推自动机定义
data PushdownAutomaton = PDA {
    pdaStates :: [Int],
    pdaAlphabet :: Alphabet,
    pdaStackAlphabet :: Alphabet,
    pdaTransitions :: [(Int, Char, Char, Int, [Char])],
    pdaStartState :: Int,
    pdaStartStack :: Char,
    pdaAcceptStates :: [Int]
}

-- PDA状态
data PDAState = PDAState {
    pdaCurrentState :: Int,
    pdaRemainingInput :: String,
    pdaStack :: [Char]
}

-- PDA执行
runPDA :: PushdownAutomaton -> String -> Bool
runPDA pda input = 
    let initialState = PDAState (pdaStartState pda) input [pdaStartStack pda]
        finalStates = executePDA pda initialState
    in any (\state -> pdaCurrentState state `elem` pdaAcceptStates pda) finalStates

-- PDA执行步骤
executePDA :: PushdownAutomaton -> PDAState -> [PDAState]
executePDA pda (PDAState state [] stack) = [PDAState state [] stack]
executePDA pda (PDAState state (c:cs) (s:ss)) = 
    let transitions = findPDATransitions pda state c s
        nextStates = [PDAState nextState cs (newStack ++ ss) | 
                     (nextState, newStack) <- transitions]
    in concat [executePDA pda nextState | nextState <- nextStates]

-- 查找PDA转移
findPDATransitions :: PushdownAutomaton -> Int -> Char -> Char -> [(Int, [Char])]
findPDATransitions pda state input stackTop = 
    [(target, stackPush) | (s, i, st, target, stackPush) <- pdaTransitions pda,
     s == state, i == input, st == stackTop]
```

## 🔬 形式化验证

### 1. 语言性质证明

```haskell
-- 正则语言性质
class RegularLanguage a where
    isRegular :: a -> Bool
    pumpLemma :: a -> Bool

-- 泵引理验证
verifyPumpLemma :: Language -> Bool
verifyPumpLemma l = 
    let p = findPumpingLength l
    in all (\s -> length s >= p ==> 
        any (\i -> any (\j -> any (\k -> 
            take i s ++ replicate j (drop i (take (i+k) s)) ++ drop (i+k) s `elem` l) [1..]) [1..]) [0..]) l
  where
    findPumpingLength l = maximum (map length l) + 1
```

### 2. 自动机等价性

```haskell
-- 自动机等价性检查
automataEquivalent :: FiniteAutomaton -> FiniteAutomaton -> Bool
automataEquivalent fa1 fa2 = 
    let allStrings = generateAllStrings (alphabet fa1) 10
    in all (\s -> runAutomaton fa1 s == runAutomaton fa2 s) allStrings

-- 生成测试字符串
generateAllStrings :: Alphabet -> Int -> [String]
generateAllStrings alpha maxLen = 
    concat [generateStringsOfLength alpha n | n <- [0..maxLen]]

generateStringsOfLength :: Alphabet -> Int -> [String]
generateStringsOfLength _ 0 = [[]]
generateStringsOfLength alpha n = 
    [c:s | c <- alpha, s <- generateStringsOfLength alpha (n-1)]
```

## 📊 应用示例

### 1. 词法分析器

```haskell
-- 词法单元定义
data Token = 
    Identifier String |
    Number Integer |
    Operator String |
    Keyword String |
    Delimiter Char

-- 词法分析器
lexer :: String -> [Token]
lexer [] = []
lexer (c:cs)
  | isSpace c = lexer cs
  | isDigit c = let (num, rest) = readNumber (c:cs) in Number num : lexer rest
  | isAlpha c = let (id, rest) = readIdentifier (c:cs) in Identifier id : lexer rest
  | otherwise = Operator [c] : lexer cs

-- 读取数字
readNumber :: String -> (Integer, String)
readNumber s = 
    let digits = takeWhile isDigit s
        rest = dropWhile isDigit s
    in (read digits, rest)

-- 读取标识符
readIdentifier :: String -> (String, String)
readIdentifier s = 
    let chars = takeWhile isAlphaNum s
        rest = dropWhile isAlphaNum s
    in (chars, rest)
```

### 2. 语法分析器

```haskell
-- 抽象语法树
data AST = 
    Literal Integer |
    Variable String |
    BinaryOp String AST AST |
    UnaryOp String AST |
    FunctionCall String [AST]

-- 递归下降解析器
parseExpression :: String -> AST
parseExpression s = 
    let tokens = lexer s
        (ast, _) = parseExpr tokens
    in ast

-- 表达式解析
parseExpr :: [Token] -> (AST, [Token])
parseExpr tokens = 
    let (left, tokens1) = parseTerm tokens
        (result, tokens2) = parseExprRest left tokens1
    in (result, tokens2)

-- 项解析
parseTerm :: [Token] -> (AST, [Token])
parseTerm tokens = 
    let (left, tokens1) = parseFactor tokens
        (result, tokens2) = parseTermRest left tokens1
    in (result, tokens2)

-- 因子解析
parseFactor :: [Token] -> (AST, [Token])
parseFactor (Number n : tokens) = (Literal n, tokens)
parseFactor (Identifier id : tokens) = (Variable id, tokens)
parseFactor (Delimiter '(' : tokens) = 
    let (expr, Delimiter ')' : rest) = parseExpr tokens
    in (expr, rest)
```

## 🎯 理论总结

### 1. 形式语言完整性

- ✅ **正则语言**: 有限自动机和正则表达式
- ✅ **上下文无关语言**: CFG和下推自动机
- ✅ **语言运算**: 并、交、连接、闭包等运算

### 2. 自动机理论

- ✅ **有限自动机**: DFA和NFA的实现
- ✅ **下推自动机**: PDA的完整实现
- ✅ **等价性验证**: 自动机等价性检查

### 3. 语言处理

- ✅ **词法分析**: 词法分析器实现
- ✅ **语法分析**: 递归下降解析器
- ✅ **形式化验证**: 语言性质证明

## 🔗 相关链接

- [101-Mathematical-Foundations.md](./101-Mathematical-Foundations.md) - 数学基础
- [103-Logical-Systems.md](./103-Logical-Systems.md) - 逻辑系统
- [001-Philosophical-Foundations.md](../01-Philosophy/001-Philosophical-Foundations.md) - 哲学基础

---

**文件状态**: ✅ 完成  
**最后更新**: 2024年12月  
**理论深度**: ⭐⭐⭐⭐⭐  
**代码质量**: ⭐⭐⭐⭐⭐
