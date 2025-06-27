# 02. 语法分析理论 (Parsing Theory)

## 📋 概述

语法分析理论研究如何将输入字符串解析为语法树，是编译器理论的核心组成部分。本文档涵盖递归下降解析、LL解析、LR解析等主要解析方法。

## 🎯 数学基础

### 1. 解析问题定义

#### 1.1 基本概念

**定义 2.1** (解析问题)
给定上下文无关文法 $G = (V, \Sigma, P, S)$ 和输入字符串 $w \in \Sigma^*$，解析问题是找到所有可能的语法树 $T$，使得 $T$ 是 $w$ 的有效解析树。

**定义 2.2** (解析树)
解析树 $T$ 是一个有根树，其中：

- 每个内部节点标记为非终结符
- 每个叶子节点标记为终结符或 $\epsilon$
- 如果节点 $A$ 有子节点 $\alpha_1, \alpha_2, \ldots, \alpha_n$，则 $A \rightarrow \alpha_1\alpha_2\ldots\alpha_n \in P$

#### 1.2 解析策略分类

**定义 2.3** (自顶向下解析)
从开始符号开始，通过应用产生式逐步推导出输入字符串。

**定义 2.4** (自底向上解析)
从输入字符串开始，通过反向应用产生式逐步归约到开始符号。

### 2. LL解析理论

**定义 2.5** (LL(k)文法)
文法 $G$ 是LL(k)的，如果对于任意两个不同的产生式 $A \rightarrow \alpha$ 和 $A \rightarrow \beta$，有：
$FIRST_k(\alpha FOLLOW(A)) \cap FIRST_k(\beta FOLLOW(A)) = \emptyset$

**定义 2.6** (FIRST集合)
$FIRST_k(\alpha) = \{w \in \Sigma^* \mid |w| \leq k \land \alpha \Rightarrow^* w\gamma\}$

**定义 2.7** (FOLLOW集合)
$FOLLOW(A) = \{a \in \Sigma \mid S \Rightarrow^* \alpha A a \beta\}$

### 3. LR解析理论

**定义 2.8** (LR(k)文法)
文法 $G$ 是LR(k)的，如果对于任意两个不同的右句型 $\alpha A \beta$ 和 $\gamma B \delta$，有：
$FIRST_k(\beta FOLLOW(A)) \cap FIRST_k(\delta FOLLOW(B)) = \emptyset$

## 🛠️ Haskell实现

### 1. 基础解析框架

```haskell
-- 解析器类型
newtype Parser a = Parser { 
  runParser :: [String] -> [(a, [String])] 
}

-- 解析器类型类
class Parsing p where
  -- 基本操作
  empty :: p a
  (<|>) :: p a -> p a -> p a
  (<*>) :: p (a -> b) -> p a -> p b
  pure :: a -> p a
  
  -- 序列操作
  (<*) :: p a -> p b -> p a
  (*>) :: p a -> p b -> p b
  
  -- 重复操作
  many :: p a -> p [a]
  some :: p a -> p [a]
  
  -- 条件操作
  satisfy :: (String -> Bool) -> p String
  char :: String -> p String
  string :: [String] -> p [String]
  eof :: p ()

-- 解析器实例
instance Parsing Parser where
  empty = Parser $ \_ -> []
  
  Parser p1 <|> Parser p2 = Parser $ \input ->
    p1 input ++ p2 input
  
  Parser pf <*> Parser pa = Parser $ \input ->
    [(f a, rest) | (f, rest1) <- pf input, (a, rest) <- pa rest1]
  
  pure a = Parser $ \input -> [(a, input)]
  
  Parser pa <* Parser pb = Parser $ \input ->
    [(a, rest) | (a, rest1) <- pa input, (_, rest) <- pb rest1]
  
  Parser pa *> Parser pb = Parser $ \input ->
    [(b, rest) | (_, rest1) <- pa input, (b, rest) <- pb rest1]
  
  many (Parser p) = Parser $ \input ->
    case p input of
      [] -> [([], input)]
      results -> 
        let (first, rest) = head results
            more = runParser (many (Parser p)) rest
        in [(first:xs, final) | (xs, final) <- more]
  
  some (Parser p) = Parser $ \input ->
    case p input of
      [] -> []
      results ->
        let (first, rest) = head results
            more = runParser (many (Parser p)) rest
        in [(first:xs, final) | (xs, final) <- more]
  
  satisfy pred = Parser $ \input ->
    case input of
      [] -> []
      (x:xs) -> if pred x then [(x, xs)] else []
  
  char c = satisfy (== c)
  
  string [] = pure []
  string (c:cs) = char c *> string cs
  
  eof = Parser $ \input ->
    if null input then [((), [])] else []
```

### 2. 递归下降解析

```haskell
-- 递归下降解析器
class RecursiveDescentParser a where
  -- 基本解析方法
  parseExpression :: Parser a
  parseTerm :: Parser a
  parseFactor :: Parser a
  
  -- 辅助方法
  parseLeftAssociative :: Parser a -> Parser (a -> a -> a) -> Parser a
  parseRightAssociative :: Parser a -> Parser (a -> a -> a) -> Parser a

-- 算术表达式解析器
data ArithmeticExpr = 
    Number Int
  | Add ArithmeticExpr ArithmeticExpr
  | Multiply ArithmeticExpr ArithmeticExpr
  | Parenthesized ArithmeticExpr
  deriving (Show, Eq)

-- 算术表达式解析器实例
instance RecursiveDescentParser ArithmeticExpr where
  parseExpression = parseLeftAssociative parseTerm parseAddOp
  
  parseTerm = parseLeftAssociative parseFactor parseMulOp
  
  parseFactor = 
    parseNumber <|> parseParenthesized
  
  parseLeftAssociative operand operator = 
    do
      first <- operand
      rest <- many (do
        op <- operator
        arg <- operand
        return (op, arg))
      return $ foldl (\acc (op, arg) -> op acc arg) first rest
  
  parseRightAssociative operand operator = 
    do
      first <- operand
      rest <- many (do
        op <- operator
        arg <- operand
        return (op, arg))
      return $ foldr (\(op, arg) acc -> op arg acc) first rest

-- 具体解析器
parseNumber :: Parser ArithmeticExpr
parseNumber = 
  do
    digits <- some (satisfy isDigit)
    return $ Number (read (concat digits))

parseAddOp :: Parser (ArithmeticExpr -> ArithmeticExpr -> ArithmeticExpr)
parseAddOp = 
  char "+" *> pure Add

parseMulOp :: Parser (ArithmeticExpr -> ArithmeticExpr -> ArithmeticExpr)
parseMulOp = 
  char "*" *> pure Multiply

parseParenthesized :: Parser ArithmeticExpr
parseParenthesized = 
  do
    char "("
    expr <- parseExpression
    char ")"
    return $ Parenthesized expr

-- 辅助函数
isDigit :: String -> Bool
isDigit s = s `elem` ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]
```

### 3. LL解析器

```haskell
-- LL解析表
type LLParseTable = Map (String, String) [String]

-- LL解析器状态
data LLParserState = 
    LLParserState {
      stack :: [String],           -- 解析栈
      input :: [String],           -- 输入缓冲区
      parseTree :: ParseTree       -- 解析树
    }
  deriving (Show)

-- LL解析器
class LLParser a where
  -- 构建解析表
  buildParseTable :: a -> LLParseTable
  
  -- 执行解析
  parse :: a -> [String] -> Maybe ParseTree
  
  -- 预测分析
  predict :: a -> String -> String -> Maybe [String]

-- 上下文无关文法LL解析器实例
instance LLParser CFG where
  buildParseTable cfg = 
    let prods = productions cfg
        firstSets = computeFirstSets cfg
        followSets = computeFollowSets cfg firstSets
        table = Map.empty
    in foldl (\tbl prod -> 
        let nt = left prod
            rhs = right prod
            first = computeFirst firstSets rhs
            follow = followSets Map.! nt
            symbols = if null first then follow else first
        in foldl (\t s -> Map.insert (nt, s) rhs t) tbl symbols) 
        table prods
  
  parse cfg input = 
    let initialState = LLParserState [startSymbol cfg] input (ParseTree (startSymbol cfg) [] Nothing)
        finalState = runLLParser cfg initialState
    in case finalState of
         Just state -> Just (parseTree state)
         Nothing -> Nothing
  
  predict cfg nt lookahead = 
    Map.lookup (nt, lookahead) (buildParseTable cfg)

-- 运行LL解析器
runLLParser :: CFG -> LLParserState -> Maybe LLParserState
runLLParser cfg state = 
  case (stack state, input state) of
    ([], []) -> Just state  -- 成功
    ([], _) -> Nothing      -- 栈空但输入未空
    (_, []) -> Nothing      -- 输入空但栈未空
    (nt:stack', input') -> 
      if nt `elem` terminals cfg
        then 
          if nt == head input'
            then runLLParser cfg state { 
                   stack = stack', 
                   input = tail input',
                   parseTree = updateParseTree (parseTree state) nt (head input')
                 }
            else Nothing
        else 
          case predict cfg nt (head input') of
            Nothing -> Nothing
            Just rhs -> 
              let newState = state { 
                    stack = rhs ++ stack',
                    parseTree = updateParseTree (parseTree state) nt rhs
                  }
              in runLLParser cfg newState

-- 计算FIRST集合
computeFirstSets :: CFG -> Map String (Set String)
computeFirstSets cfg = 
  let initial = Map.fromList [(nt, Set.empty) | nt <- nonterminals cfg]
      fixedPoint = iterate (updateFirstSets cfg) initial
  in head $ dropWhile (\m -> any (Set.null . snd) (Map.toList m)) fixedPoint

-- 更新FIRST集合
updateFirstSets :: CFG -> Map String (Set String) -> Map String (Set String)
updateFirstSets cfg firstSets = 
  foldl (\sets prod -> 
    let nt = left prod
        rhs = right prod
        first = computeFirst firstSets rhs
        current = sets Map.! nt
        new = Set.union current first
    in Map.insert nt new sets) firstSets (productions cfg)

-- 计算符号序列的FIRST
computeFirst :: Map String (Set String) -> [String] -> Set String
computeFirst firstSets [] = Set.singleton "ε"
computeFirst firstSets (sym:syms) = 
  if sym `elem` terminals
    then Set.singleton sym
    else 
      let firstSym = firstSets Map.! sym
          firstRest = computeFirst firstSets syms
      in if Set.member "ε" firstSym
           then Set.union (Set.delete "ε" firstSym) firstRest
           else firstSym
```

### 4. LR解析器

```haskell
-- LR项目
data LRItem = 
    LRItem {
      production :: Production,
      position :: Int,      -- 点的位置
      lookahead :: String   -- 展望符
    }
  deriving (Show, Eq, Ord)

-- LR状态
data LRState = 
    LRState {
      items :: Set LRItem,
      stateId :: Int
    }
  deriving (Show, Eq, Ord)

-- LR解析表
data LRParseTable = 
    LRParseTable {
      action :: Map (Int, String) Action,
      goto :: Map (Int, String) Int
    }
  deriving (Show)

-- 动作类型
data Action = 
    Shift Int      -- 移进
  | Reduce Production  -- 归约
  | Accept           -- 接受
  | Error            -- 错误
  deriving (Show, Eq)

-- LR解析器
class LRParser a where
  -- 构建LR解析表
  buildLRParseTable :: a -> LRParseTable
  
  -- 执行LR解析
  parse :: a -> [String] -> Maybe ParseTree
  
  -- 计算闭包
  closure :: a -> Set LRItem -> Set LRItem
  
  -- 计算GOTO
  goto :: a -> Set LRItem -> String -> Set LRItem

-- 上下文无关文法LR解析器实例
instance LRParser CFG where
  buildLRParseTable cfg = 
    let startItem = LRItem (Production "S'" ["S"]) 0 "$"
        initialState = closure cfg (Set.singleton startItem)
        states = buildStates cfg [initialState]
        actionTable = buildActionTable cfg states
        gotoTable = buildGotoTable cfg states
    in LRParseTable actionTable gotoTable
  
  parse cfg input = 
    let table = buildLRParseTable cfg
        initialState = (0, [], [ParseTree (startSymbol cfg) [] Nothing])
        finalState = runLRParser table (input ++ ["$"]) initialState
    in case finalState of
         Just (_, _, tree) -> Just tree
         Nothing -> Nothing
  
  closure cfg items = 
    let newItems = Set.unions [computeClosure cfg item | item <- Set.toList items]
    in if newItems == items
         then items
         else closure cfg newItems
  
  goto cfg items symbol = 
    let nextItems = [advanceItem item symbol | item <- Set.toList items, canAdvance item symbol]
    in closure cfg (Set.fromList nextItems)

-- 计算项目闭包
computeClosure :: CFG -> LRItem -> Set LRItem
computeClosure cfg item = 
  case getSymbolAfterDot item of
    Nothing -> Set.empty
    Just nt -> 
      if nt `elem` nonterminals cfg
        then 
          let prods = findProductions cfg nt
              lookaheads = computeLookaheads cfg item
              newItems = [LRItem prod 0 la | prod <- prods, la <- lookaheads]
          in Set.fromList newItems
        else Set.empty

-- 获取点后的符号
getSymbolAfterDot :: LRItem -> Maybe String
getSymbolAfterDot item = 
  let rhs = right (production item)
      pos = position item
  in if pos < length rhs
       then Just (rhs !! pos)
       else Nothing

-- 检查是否可以前进
canAdvance :: LRItem -> String -> Bool
canAdvance item symbol = 
  case getSymbolAfterDot item of
    Just sym -> sym == symbol
    Nothing -> False

-- 前进项目
advanceItem :: LRItem -> String -> LRItem
advanceItem item symbol = 
  item { position = position item + 1 }

-- 构建LR状态
buildStates :: CFG -> [Set LRItem] -> [Set LRItem]
buildStates cfg states = 
  let symbols = terminals cfg ++ nonterminals cfg
      newStates = [goto cfg state sym | state <- states, sym <- symbols]
      allStates = nub (states ++ newStates)
  in if length allStates == length states
       then states
       else buildStates cfg allStates

-- 构建动作表
buildActionTable :: CFG -> [Set LRItem] -> Map (Int, String) Action
buildActionTable cfg states = 
  let actions = [(stateId, symbol, action) | 
                 (stateId, state) <- zip [0..] states,
                 symbol <- terminals cfg,
                 action <- computeAction cfg state symbol]
  in Map.fromList [(key, action) | (key, _, action) <- actions]

-- 计算动作
computeAction :: CFG -> Set LRItem -> String -> [Action]
computeAction cfg state symbol = 
  let shiftActions = [Shift stateId | 
                      item <- Set.toList state,
                      canAdvance item symbol]
      reduceActions = [Reduce (production item) | 
                       item <- Set.toList state,
                       isComplete item,
                       lookahead item == symbol]
      acceptActions = [Accept | 
                       item <- Set.toList state,
                       isComplete item,
                       left (production item) == startSymbol cfg,
                       lookahead item == symbol]
  in shiftActions ++ reduceActions ++ acceptActions

-- 检查项目是否完整
isComplete :: LRItem -> Bool
isComplete item = 
  position item >= length (right (production item))
```

### 5. 解析树构建

```haskell
-- 更新解析树
updateParseTree :: ParseTree -> String -> [String] -> ParseTree
updateParseTree tree nt rhs = 
  case rhs of
    [] -> tree  -- 空产生式
    [term] -> 
      if term `elem` terminals
        then ParseTree nt [ParseTree term [] (Just term)] Nothing
        else tree
    _ -> 
      let children = [ParseTree sym [] Nothing | sym <- rhs]
      in ParseTree nt children Nothing

-- 构建LR解析树
buildLRParseTree :: [Action] -> [String] -> ParseTree
buildLRParseTree actions input = 
  let (_, tree) = foldl processAction (input, []) actions
  in head tree

-- 处理动作
processAction :: ([String], [ParseTree]) -> Action -> ([String], [ParseTree])
processAction (input, stack) action = 
  case action of
    Shift _ -> 
      case input of
        [] -> (input, stack)
        (sym:syms) -> 
          let tree = ParseTree sym [] (Just sym)
          in (syms, tree:stack)
    
    Reduce prod -> 
      let rhs = right prod
          nt = left prod
          (children, newStack) = splitAt (length rhs) stack
          tree = ParseTree nt (reverse children) Nothing
      in (input, tree:newStack)
    
    Accept -> (input, stack)
    Error -> (input, stack)
```

## 📊 形式化证明

### 定理 2.1 (LL解析正确性)

**定理**：如果文法 $G$ 是LL(k)的，则LL(k)解析器能够正确解析 $L(G)$ 中的所有字符串。

**证明**：

1. 对于LL(k)文法，解析表是无冲突的
2. 每个预测步骤都是确定的
3. 解析过程模拟了最左推导
4. 因此解析结果与语法定义一致

### 定理 2.2 (LR解析完备性)

**定理**：LR(k)解析器能够解析所有确定性上下文无关语言。

**证明**：

1. LR(k)文法包含所有确定性CFL
2. LR解析器能够处理所有LR(k)文法
3. 解析过程模拟了最右推导的逆过程
4. 因此LR解析器是完备的

## 🎯 应用示例

### 示例 1：简单表达式解析器

```haskell
-- 简单表达式文法
simpleExprGrammar :: CFG
simpleExprGrammar = 
  CFG {
    nonterminals = ["E", "T", "F"],
    terminals = ["+", "*", "(", ")", "id"],
    productions = [
      Production "E" ["E", "+", "T"],
      Production "E" ["T"],
      Production "T" ["T", "*", "F"],
      Production "T" ["F"],
      Production "F" ["(", "E", ")"],
      Production "F" ["id"]
    ],
    startSymbol = "E"
  }

-- 测试解析器
testParsers :: IO ()
testParsers = do
  putStrLn "=== 解析器测试 ==="
  
  let input = ["id", "+", "id", "*", "id"]
  
  -- 递归下降解析
  putStrLn "递归下降解析："
  case runParser parseExpression input of
    [] -> putStrLn "解析失败"
    ((expr, rest):_) -> do
      putStrLn $ "解析结果: " ++ show expr
      putStrLn $ "剩余输入: " ++ show rest
  
  -- LL解析
  putStrLn "LL解析："
  case parse simpleExprGrammar input of
    Nothing -> putStrLn "解析失败"
    Just tree -> putStrLn $ "解析树: " ++ show tree
  
  -- LR解析
  putStrLn "LR解析："
  case parse simpleExprGrammar input of
    Nothing -> putStrLn "解析失败"
    Just tree -> putStrLn $ "解析树: " ++ show tree
```

### 示例 2：JSON解析器

```haskell
-- JSON数据类型
data JSONValue = 
    JSONNull
  | JSONBool Bool
  | JSONNumber Double
  | JSONString String
  | JSONArray [JSONValue]
  | JSONObject [(String, JSONValue)]
  deriving (Show, Eq)

-- JSON解析器
parseJSON :: Parser JSONValue
parseJSON = 
  parseNull <|> parseBool <|> parseNumber <|> 
  parseString <|> parseArray <|> parseObject

parseNull :: Parser JSONValue
parseNull = 
  string ["null"] *> pure JSONNull

parseBool :: Parser JSONValue
parseBool = 
  (string ["true"] *> pure (JSONBool True)) <|>
  (string ["false"] *> pure (JSONBool False))

parseNumber :: Parser JSONValue
parseNumber = 
  do
    digits <- some (satisfy isDigit)
    return $ JSONNumber (read (concat digits))

parseString :: Parser JSONValue
parseString = 
  do
    char "\""
    chars <- many (satisfy (/= "\""))
    char "\""
    return $ JSONString (concat chars)

parseArray :: Parser JSONValue
parseArray = 
  do
    char "["
    values <- parseJSON `sepBy` char ","
    char "]"
    return $ JSONArray values

parseObject :: Parser JSONValue
parseObject = 
  do
    char "{"
    pairs <- parsePair `sepBy` char ","
    char "}"
    return $ JSONObject pairs

parsePair :: Parser (String, JSONValue)
parsePair = 
  do
    key <- parseString
    char ":"
    value <- parseJSON
    return (extractString key, value)

-- 辅助函数
extractString :: JSONValue -> String
extractString (JSONString s) = s
extractString _ = ""

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = 
  (p `sepBy1` sep) <|> pure []

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p sep = 
  do
    first <- p
    rest <- many (sep *> p)
    return (first:rest)
```

## 🔗 相关链接

- [01-Formal-Grammars](./01-Formal-Grammars.md) - 形式语法理论
- [03-Syntax-Analysis](./03-Syntax-Analysis.md) - 语法分析算法
- [02-Semantics-Theory](../02-Semantics-Theory/README.md) - 语义理论
- [03-Type-System-Theory](../03-Type-System-Theory/README.md) - 类型系统理论

## 📚 参考文献

1. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.
2. Grune, D., & Jacobs, C. J. (2008). Parsing Techniques: A Practical Guide.
3. Sipser, M. (2012). Introduction to the Theory of Computation.

---

*本文档是形式化知识体系理论层的一部分，提供了语法分析理论的完整数学定义和Haskell实现。*
