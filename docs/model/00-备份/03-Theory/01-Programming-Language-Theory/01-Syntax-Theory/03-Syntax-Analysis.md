# 03. 语法分析算法 (Syntax Analysis Algorithms)

## 📋 概述

语法分析算法是编译器前端的重要组成部分，负责将词法分析器输出的词法单元序列转换为抽象语法树。本文档涵盖各种语法分析算法的详细实现和优化技术。

## 🎯 算法分类

### 1. 自顶向下算法

#### 1.1 递归下降解析

**算法 2.1** (递归下降解析)

```haskell
-- 递归下降解析器框架
class RecursiveDescentParser a where
  -- 基本解析方法
  parseProgram :: Parser a
  parseStatement :: Parser a
  parseExpression :: Parser a
  parseTerm :: Parser a
  parseFactor :: Parser a
  
  -- 错误恢复
  errorRecovery :: Parser a -> Parser a
  synchronize :: Parser a
  
  -- 预测解析
  predict :: String -> Parser a
  lookahead :: Int -> Parser [String]

-- 具体实现
instance RecursiveDescentParser Program where
  parseProgram = 
    do
      statements <- many parseStatement
      eof
      return $ Program statements
  
  parseStatement = 
    parseAssignment <|> parseIfStatement <|> 
    parseWhileStatement <|> parseBlock
  
  parseExpression = 
    parseLogicalOr
  
  parseTerm = 
    parseLogicalAnd
  
  parseFactor = 
    parseEquality
  
  errorRecovery parser = 
    parser <|> (synchronize *> parser)
  
  synchronize = 
    do
      tokens <- many (satisfy (not . isStatementStart))
      satisfy isStatementStart
      return ()
  
  predict token = 
    case token of
      "if" -> parseIfStatement
      "while" -> parseWhileStatement
      "{" -> parseBlock
      _ -> parseAssignment
  
  lookahead k = 
    Parser $ \input -> 
      if length input >= k
        then [(take k input, input)]
        else []

-- 辅助函数
isStatementStart :: String -> Bool
isStatementStart token = 
  token `elem` ["if", "while", "{", "id", "return"]

-- 程序结构
data Program = 
    Program [Statement]
  deriving (Show, Eq)

data Statement = 
    Assignment String Expression
  | IfStatement Expression Statement (Maybe Statement)
  | WhileStatement Expression Statement
  | Block [Statement]
  deriving (Show, Eq)

data Expression = 
    Variable String
  | Number Int
  | BinaryOp String Expression Expression
  | UnaryOp String Expression
  deriving (Show, Eq)
```

#### 1.2 预测解析器

**算法 2.2** (预测解析器)

```haskell
-- 预测解析表
type PredictiveParseTable = Map (String, String) [String]

-- 预测解析器
class PredictiveParser a where
  -- 构建预测表
  buildPredictiveTable :: a -> PredictiveParseTable
  
  -- 执行预测解析
  parse :: a -> [String] -> Maybe ParseTree
  
  -- 计算FIRST和FOLLOW集合
  computeFirst :: a -> Map String (Set String)
  computeFollow :: a -> Map String (Set String)

-- 上下文无关文法预测解析器实例
instance PredictiveParser CFG where
  buildPredictiveTable cfg = 
    let firstSets = computeFirst cfg
        followSets = computeFollow cfg firstSets
        prods = productions cfg
    in foldl (\table prod -> 
        let nt = left prod
            rhs = right prod
            first = computeFirstOfString firstSets rhs
            follow = followSets Map.! nt
            symbols = if Set.member "ε" first 
                       then Set.union (Set.delete "ε" first) follow 
                       else first
        in foldl (\t sym -> Map.insert (nt, sym) rhs t) table symbols) 
        Map.empty prods
  
  parse cfg input = 
    let table = buildPredictiveTable cfg
        initialState = ([startSymbol cfg], input, [])
    in case runPredictiveParser table initialState of
         Just (_, [], tree) -> Just tree
         _ -> Nothing
  
  computeFirst cfg = 
    let initial = Map.fromList [(nt, Set.empty) | nt <- nonterminals cfg]
        fixedPoint = iterate (updateFirst cfg) initial
    in head $ dropWhile (\m -> any (Set.null . snd) (Map.toList m)) fixedPoint
  
  computeFollow cfg firstSets = 
    let initial = Map.fromList [(nt, if nt == startSymbol cfg 
                                      then Set.singleton "$" 
                                      else Set.empty) | nt <- nonterminals cfg]
        fixedPoint = iterate (updateFollow cfg firstSets) initial
    in head $ dropWhile (\m -> any (Set.null . snd) (Map.toList m)) fixedPoint

-- 运行预测解析器
runPredictiveParser :: PredictiveParseTable -> ([String], [String], [ParseTree]) -> Maybe ([String], [String], ParseTree)
runPredictiveParser table (stack, input, trees) = 
  case (stack, input) of
    ([], []) -> Just ([], [], head trees)
    ([], _) -> Nothing
    (_, []) -> Nothing
    (nt:stack', input') -> 
      if nt `elem` terminals
        then 
          if nt == head input'
            then runPredictiveParser table (stack', tail input', 
                   ParseTree nt [] (Just nt) : trees)
            else Nothing
        else 
          case Map.lookup (nt, head input') table of
            Nothing -> Nothing
            Just rhs -> 
              let newStack = rhs ++ stack'
                  newTree = ParseTree nt [] Nothing
              in runPredictiveParser table (newStack, input', newTree : trees)

-- 计算字符串的FIRST集合
computeFirstOfString :: Map String (Set String) -> [String] -> Set String
computeFirstOfString firstSets [] = Set.singleton "ε"
computeFirstOfString firstSets (sym:syms) = 
  if sym `elem` terminals
    then Set.singleton sym
    else 
      let firstSym = firstSets Map.! sym
          firstRest = computeFirstOfString firstSets syms
      in if Set.member "ε" firstSym
           then Set.union (Set.delete "ε" firstSym) firstRest
           else firstSym

-- 更新FIRST集合
updateFirst :: CFG -> Map String (Set String) -> Map String (Set String)
updateFirst cfg firstSets = 
  foldl (\sets prod -> 
    let nt = left prod
        rhs = right prod
        first = computeFirstOfString firstSets rhs
        current = sets Map.! nt
        new = Set.union current first
    in Map.insert nt new sets) firstSets (productions cfg)

-- 更新FOLLOW集合
updateFollow :: CFG -> Map String (Set String) -> Map String (Set String) -> Map String (Set String)
updateFollow cfg firstSets followSets = 
  foldl (\sets prod -> 
    let nt = left prod
        rhs = right prod
        follow = followSets Map.! nt
        newSets = foldl (\s (i, sym) -> 
          if sym `elem` nonterminals cfg
            then 
              let beta = drop (i + 1) rhs
                  firstBeta = computeFirstOfString firstSets beta
                  followSym = s Map.! sym
                  newFollow = if Set.member "ε" firstBeta
                               then Set.union followSym (Set.union (Set.delete "ε" firstBeta) follow)
                               else Set.union followSym firstBeta
              in Map.insert sym newFollow s
            else s) sets (zip [0..] rhs)
    in newSets) followSets (productions cfg)
```

### 2. 自底向上算法

#### 2.1 LR(0)解析器

**算法 2.3** (LR(0)解析器)

```haskell
-- LR(0)项目
data LR0Item = 
    LR0Item {
      lr0Production :: Production,
      lr0Position :: Int
    }
  deriving (Show, Eq, Ord)

-- LR(0)状态
data LR0State = 
    LR0State {
      lr0Items :: Set LR0Item,
      lr0StateId :: Int
    }
  deriving (Show, Eq, Ord)

-- LR(0)解析器
class LR0Parser a where
  -- 构建LR(0)解析表
  buildLR0ParseTable :: a -> LRParseTable
  
  -- 计算LR(0)闭包
  closure0 :: a -> Set LR0Item -> Set LR0Item
  
  -- 计算LR(0) GOTO
  goto0 :: a -> Set LR0Item -> String -> Set LR0Item

-- 上下文无关文法LR(0)解析器实例
instance LR0Parser CFG where
  buildLR0ParseTable cfg = 
    let startItem = LR0Item (Production "S'" ["S"]) 0
        initialState = closure0 cfg (Set.singleton startItem)
        states = buildLR0States cfg [initialState]
        actionTable = buildLR0ActionTable cfg states
        gotoTable = buildLR0GotoTable cfg states
    in LRParseTable actionTable gotoTable
  
  closure0 cfg items = 
    let newItems = Set.unions [computeLR0Closure cfg item | item <- Set.toList items]
    in if newItems == items
         then items
         else closure0 cfg newItems
  
  goto0 cfg items symbol = 
    let nextItems = [advanceLR0Item item symbol | item <- Set.toList items, canAdvanceLR0 item symbol]
    in closure0 cfg (Set.fromList nextItems)

-- 计算LR(0)闭包
computeLR0Closure :: CFG -> LR0Item -> Set LR0Item
computeLR0Closure cfg item = 
  case getSymbolAfterLR0Dot item of
    Nothing -> Set.empty
    Just nt -> 
      if nt `elem` nonterminals cfg
        then 
          let prods = findProductions cfg nt
              newItems = [LR0Item prod 0 | prod <- prods]
          in Set.fromList newItems
        else Set.empty

-- 获取LR(0)点后的符号
getSymbolAfterLR0Dot :: LR0Item -> Maybe String
getSymbolAfterLR0Dot item = 
  let rhs = right (lr0Production item)
      pos = lr0Position item
  in if pos < length rhs
       then Just (rhs !! pos)
       else Nothing

-- 检查LR(0)项目是否可以前进
canAdvanceLR0 :: LR0Item -> String -> Bool
canAdvanceLR0 item symbol = 
  case getSymbolAfterLR0Dot item of
    Just sym -> sym == symbol
    Nothing -> False

-- 前进LR(0)项目
advanceLR0Item :: LR0Item -> String -> LR0Item
advanceLR0Item item symbol = 
  item { lr0Position = lr0Position item + 1 }

-- 构建LR(0)状态
buildLR0States :: CFG -> [Set LR0Item] -> [Set LR0Item]
buildLR0States cfg states = 
  let symbols = terminals cfg ++ nonterminals cfg
      newStates = [goto0 cfg state sym | state <- states, sym <- symbols]
      allStates = nub (states ++ newStates)
  in if length allStates == length states
       then states
       else buildLR0States cfg allStates

-- 构建LR(0)动作表
buildLR0ActionTable :: CFG -> [Set LR0Item] -> Map (Int, String) Action
buildLR0ActionTable cfg states = 
  let actions = [(stateId, symbol, action) | 
                 (stateId, state) <- zip [0..] states,
                 symbol <- terminals cfg,
                 action <- computeLR0Action cfg state symbol]
  in Map.fromList [(key, action) | (key, _, action) <- actions]

-- 计算LR(0)动作
computeLR0Action :: CFG -> Set LR0Item -> String -> [Action]
computeLR0Action cfg state symbol = 
  let shiftActions = [Shift stateId | 
                      item <- Set.toList state,
                      canAdvanceLR0 item symbol]
      reduceActions = [Reduce (lr0Production item) | 
                       item <- Set.toList state,
                       isLR0Complete item]
      acceptActions = [Accept | 
                       item <- Set.toList state,
                       isLR0Complete item,
                       left (lr0Production item) == startSymbol cfg]
  in shiftActions ++ reduceActions ++ acceptActions

-- 检查LR(0)项目是否完整
isLR0Complete :: LR0Item -> Bool
isLR0Complete item = 
  lr0Position item >= length (right (lr0Production item))
```

#### 2.2 SLR(1)解析器

**算法 2.4** (SLR(1)解析器)

```haskell
-- SLR(1)解析器
class SLR1Parser a where
  -- 构建SLR(1)解析表
  buildSLR1ParseTable :: a -> LRParseTable
  
  -- 计算SLR(1)动作
  computeSLR1Action :: a -> Set LR0Item -> String -> [Action]

-- 上下文无关文法SLR(1)解析器实例
instance SLR1Parser CFG where
  buildSLR1ParseTable cfg = 
    let startItem = LR0Item (Production "S'" ["S"]) 0
        initialState = closure0 cfg (Set.singleton startItem)
        states = buildLR0States cfg [initialState]
        actionTable = buildSLR1ActionTable cfg states
        gotoTable = buildLR0GotoTable cfg states
    in LRParseTable actionTable gotoTable
  
  computeSLR1Action cfg state symbol = 
    let firstSets = computeFirst cfg
        followSets = computeFollow cfg firstSets
        shiftActions = [Shift stateId | 
                        item <- Set.toList state,
                        canAdvanceLR0 item symbol]
        reduceActions = [Reduce (lr0Production item) | 
                         item <- Set.toList state,
                         isLR0Complete item,
                         symbol `Set.member` (followSets Map.! left (lr0Production item))]
        acceptActions = [Accept | 
                         item <- Set.toList state,
                         isLR0Complete item,
                         left (lr0Production item) == startSymbol cfg,
                         symbol == "$"]
    in shiftActions ++ reduceActions ++ acceptActions

-- 构建SLR(1)动作表
buildSLR1ActionTable :: CFG -> [Set LR0Item] -> Map (Int, String) Action
buildSLR1ActionTable cfg states = 
  let actions = [(stateId, symbol, action) | 
                 (stateId, state) <- zip [0..] states,
                 symbol <- terminals cfg,
                 action <- computeSLR1Action cfg state symbol]
  in Map.fromList [(key, action) | (key, _, action) <- actions]
```

### 3. 错误恢复算法

#### 3.1 恐慌模式恢复

**算法 2.5** (恐慌模式恢复)

```haskell
-- 恐慌模式恢复
class PanicModeRecovery a where
  -- 恐慌模式恢复
  panicModeRecovery :: a -> [String] -> [String] -> Maybe [String]
  
  -- 同步集合
  syncSet :: a -> Set String
  
  -- 跳过到同步点
  skipToSync :: a -> [String] -> [String]

-- 上下文无关文法恐慌模式恢复实例
instance PanicModeRecovery CFG where
  panicModeRecovery cfg stack input = 
    let sync = syncSet cfg
        (newStack, newInput) = skipToSync cfg (stack, input)
    in if null newStack
         then Nothing
         else Just newInput
  
  syncSet cfg = 
    Set.fromList (terminals cfg ++ ["$"])
  
  skipToSync cfg (stack, input) = 
    case input of
      [] -> (stack, [])
      (token:tokens) -> 
        if token `Set.member` syncSet cfg
          then (stack, input)
          else skipToSync cfg (stack, tokens)
```

#### 3.2 短语级恢复

**算法 2.6** (短语级恢复)

```haskell
-- 短语级恢复
class PhraseLevelRecovery a where
  -- 短语级恢复
  phraseLevelRecovery :: a -> [String] -> [String] -> Maybe [String]
  
  -- 错误修复规则
  errorFixRules :: a -> Map String [String]
  
  -- 应用修复规则
  applyFixRule :: a -> String -> [String] -> Maybe [String]

-- 上下文无关文法短语级恢复实例
instance PhraseLevelRecovery CFG where
  phraseLevelRecovery cfg stack input = 
    case input of
      [] -> Nothing
      (token:tokens) -> 
        case Map.lookup token (errorFixRules cfg) of
          Nothing -> phraseLevelRecovery cfg stack tokens
          Just fix -> 
            case applyFixRule cfg token fix of
              Nothing -> phraseLevelRecovery cfg stack tokens
              Just fixed -> Just (fixed ++ tokens)
  
  errorFixRules cfg = 
    Map.fromList [
      (";", [";"]),
      ("}", ["}"]),
      (")", [")"]),
      ("]", ["]"])
    ]
  
  applyFixRule cfg token fix = 
    Just fix
```

## 📊 性能分析

### 1. 时间复杂度分析

**定理 2.1** (递归下降解析时间复杂度)
递归下降解析的时间复杂度为 $O(n^2)$，其中 $n$ 是输入长度。

**证明**：

1. 每个非终结符的解析可能需要回溯
2. 最坏情况下需要尝试所有可能的产生式
3. 因此总时间复杂度为 $O(n^2)$

**定理 2.2** (LR解析时间复杂度)
LR解析的时间复杂度为 $O(n)$，其中 $n$ 是输入长度。

**证明**：

1. LR解析器是确定性的
2. 每个输入符号最多被处理一次
3. 因此总时间复杂度为 $O(n)$

### 2. 空间复杂度分析

**定理 2.3** (解析器空间复杂度)

- 递归下降解析：$O(n)$（调用栈深度）
- LR解析：$O(n)$（解析栈大小）
- LL解析：$O(n)$（解析栈大小）

## 🎯 优化技术

### 1. 记忆化解析

```haskell
-- 记忆化解析器
newtype MemoizedParser a = MemoizedParser { 
  runMemoizedParser :: Map (String, [String]) [(a, [String])] -> [String] -> ([(a, [String])], Map (String, [String]) [(a, [String])])
}

-- 记忆化解析器类型类
class MemoizedParsing p where
  -- 基本操作
  memoizedEmpty :: p a
  memoizedOr :: p a -> p a -> p a
  memoizedAnd :: p (a -> b) -> p a -> p b
  memoizedPure :: a -> p a
  
  -- 记忆化操作
  memoize :: String -> p a -> p a
  lookupMemo :: String -> p a -> p a

-- 记忆化解析器实例
instance MemoizedParsing MemoizedParser where
  memoizedEmpty = MemoizedParser $ \memo input -> ([], memo)
  
  memoizedOr (MemoizedParser p1) (MemoizedParser p2) = 
    MemoizedParser $ \memo input ->
      let (result1, memo1) = p1 memo input
          (result2, memo2) = p2 memo1 input
      in (result1 ++ result2, memo2)
  
  memoizedAnd (MemoizedParser pf) (MemoizedParser pa) = 
    MemoizedParser $ \memo input ->
      let (fResults, memo1) = pf memo input
          allResults = concatMap (\(f, rest) -> 
            let (aResults, memo2) = pa memo1 rest
            in [(f a, final) | (a, final) <- aResults]) fResults
      in (allResults, memo1)
  
  memoizedPure a = MemoizedParser $ \memo input -> ([(a, input)], memo)
  
  memoize key (MemoizedParser p) = 
    MemoizedParser $ \memo input ->
      case Map.lookup (key, show input) memo of
        Just cached -> (cached, memo)
        Nothing -> 
          let (result, newMemo) = p memo input
          in (result, Map.insert (key, show input) result newMemo)
  
  lookupMemo key (MemoizedParser p) = 
    MemoizedParser $ \memo input ->
      case Map.lookup (key, show input) memo of
        Just cached -> (cached, memo)
        Nothing -> p memo input
```

### 2. 并行解析

```haskell
-- 并行解析器
newtype ParallelParser a = ParallelParser { 
  runParallelParser :: [String] -> [(a, [String])] 
}

-- 并行解析器类型类
class ParallelParsing p where
  -- 基本操作
  parallelEmpty :: p a
  parallelOr :: p a -> p a -> p a
  parallelAnd :: p (a -> b) -> p a -> p b
  parallelPure :: a -> p a
  
  -- 并行操作
  parallel :: [p a] -> p [a]
  parallelMap :: (a -> b) -> p a -> p b

-- 并行解析器实例
instance ParallelParsing ParallelParser where
  parallelEmpty = ParallelParser $ \_ -> []
  
  parallelOr (ParallelParser p1) (ParallelParser p2) = 
    ParallelParser $ \input ->
      let result1 = p1 input
          result2 = p2 input
      in result1 ++ result2
  
  parallelAnd (ParallelParser pf) (ParallelParser pa) = 
    ParallelParser $ \input ->
      let fResults = pf input
          allResults = concatMap (\(f, rest) -> 
            let aResults = pa rest
            in [(f a, final) | (a, final) <- aResults]) fResults
      in allResults
  
  parallelPure a = ParallelParser $ \input -> [(a, input)]
  
  parallel parsers = 
    ParallelParser $ \input ->
      let results = map (\p -> runParallelParser p input) parsers
          allResults = concat results
      in allResults
  
  parallelMap f (ParallelParser p) = 
    ParallelParser $ \input ->
      let results = p input
      in [(f a, rest) | (a, rest) <- results]
```

## 🎯 应用示例

### 示例 1：表达式解析器性能比较

```haskell
-- 性能测试
performanceTest :: IO ()
performanceTest = do
  putStrLn "=== 解析器性能测试 ==="
  
  let testInput = replicate 1000 "id" ++ ["+"] ++ replicate 1000 "id"
  
  -- 递归下降解析
  startTime <- getCurrentTime
  let rdResult = runParser parseExpression testInput
  endTime <- getCurrentTime
  putStrLn $ "递归下降解析时间: " ++ show (diffUTCTime endTime startTime)
  
  -- 预测解析
  startTime2 <- getCurrentTime
  let predResult = parse simpleExprGrammar testInput
  endTime2 <- getCurrentTime
  putStrLn $ "预测解析时间: " ++ show (diffUTCTime endTime2 startTime2)
  
  -- LR解析
  startTime3 <- getCurrentTime
  let lrResult = parse simpleExprGrammar testInput
  endTime3 <- getCurrentTime
  putStrLn $ "LR解析时间: " ++ show (diffUTCTime endTime3 startTime3)
```

### 示例 2：错误恢复测试

```haskell
-- 错误恢复测试
errorRecoveryTest :: IO ()
errorRecoveryTest = do
  putStrLn "=== 错误恢复测试 ==="
  
  let correctInput = ["id", "+", "id", ";"]
  let errorInput = ["id", "+", "id", "error", ";"]
  
  -- 正确输入解析
  putStrLn "正确输入解析："
  case parse simpleExprGrammar correctInput of
    Just tree -> putStrLn $ "解析成功: " ++ show tree
    Nothing -> putStrLn "解析失败"
  
  -- 错误输入解析（带恢复）
  putStrLn "错误输入解析（带恢复）："
  case panicModeRecovery simpleExprGrammar [] errorInput of
    Just recovered -> do
      putStrLn $ "恢复后输入: " ++ show recovered
      case parse simpleExprGrammar recovered of
        Just tree -> putStrLn $ "解析成功: " ++ show tree
        Nothing -> putStrLn "解析仍然失败"
    Nothing -> putStrLn "无法恢复"
```

## 🔗 相关链接

- [01-Formal-Grammars](./01-Formal-Grammars.md) - 形式语法理论
- [02-Parsing-Theory](./02-Parsing-Theory.md) - 语法分析理论
- [02-Semantics-Theory](../02-Semantics-Theory/README.md) - 语义理论
- [03-Type-System-Theory](../03-Type-System-Theory/README.md) - 类型系统理论

## 📚 参考文献

1. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.
2. Grune, D., & Jacobs, C. J. (2008). Parsing Techniques: A Practical Guide.
3. Sipser, M. (2012). Introduction to the Theory of Computation.

---

*本文档是形式化知识体系理论层的一部分，提供了语法分析算法的完整实现和性能分析。*
