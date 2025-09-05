# 03-Haskell控制流 (Haskell Control Flow)

## 📚 概述

Haskell的控制流与传统的命令式编程语言有本质区别。在函数式编程中，控制流主要通过函数组合、模式匹配、递归和高阶函数来实现，而不是通过循环和条件语句。本文档将深入探讨Haskell中的各种控制流机制和模式。

## 🏗️ 控制流架构

### 1. 函数式控制流基础

#### 1.1 函数组合

**定义 1.1 (函数组合)**
函数组合是函数式编程中最基本的控制流机制：

```haskell
-- 函数组合操作符
(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x = f (g x)

-- 函数组合示例
addOne :: Int -> Int
addOne x = x + 1

multiplyByTwo :: Int -> Int
multiplyByTwo x = x * 2

addOneThenMultiply :: Int -> Int
addOneThenMultiply = multiplyByTwo . addOne

-- 管道操作符
(|>) :: a -> (a -> b) -> b
x |> f = f x

-- 反向管道操作符
(<|) :: (a -> b) -> a -> b
f <| x = f x

-- 管道示例
processData :: Int -> String
processData = addOne 
           . multiplyByTwo 
           . show 
           . (++ " processed")

-- 使用管道操作符
processData' :: Int -> String
processData' x = x |> addOne 
                       |> multiplyByTwo 
                       |> show 
                       |> (++ " processed")
```

#### 1.2 高阶函数

**定义 1.2 (高阶函数)**
高阶函数是接受函数作为参数或返回函数的函数：

```haskell
-- map函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- filter函数
filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs)
  | p x = x : filter p xs
  | otherwise = filter p xs

-- foldr函数
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

-- foldl函数
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl _ z [] = z
foldl f z (x:xs) = foldl f (f z x) xs

-- 高阶函数示例
processList :: [Int] -> [String]
processList = map show . filter (> 0) . map (* 2)

-- 自定义高阶函数
applyTwice :: (a -> a) -> a -> a
applyTwice f x = f (f x)

applyNTimes :: Int -> (a -> a) -> a -> a
applyNTimes 0 _ x = x
applyNTimes n f x = applyNTimes (n - 1) f (f x)

-- 函数生成器
makeAdder :: Int -> (Int -> Int)
makeAdder n = (+ n)

makeMultiplier :: Int -> (Int -> Int)
makeMultiplier n = (* n)
```

### 2. 模式匹配

#### 2.1 基本模式匹配

**定义 2.1 (模式匹配)**
模式匹配是Haskell中最重要的控制流机制：

```haskell
-- 列表模式匹配
head' :: [a] -> a
head' (x:_) = x
head' [] = error "Empty list"

tail' :: [a] -> [a]
tail' (_:xs) = xs
tail' [] = error "Empty list"

-- 元组模式匹配
fst' :: (a, b) -> a
fst' (x, _) = x

snd' :: (a, b) -> b
snd' (_, y) = y

-- 自定义数据类型模式匹配
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double

area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = 
  let s = (a + b + c) / 2
  in sqrt (s * (s - a) * (s - b) * (s - c))

-- Maybe类型模式匹配
safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail [] = Nothing
safeTail (_:xs) = Just xs

-- Either类型模式匹配
safeDivide :: Double -> Double -> Either String Double
safeDivide _ 0 = Left "Division by zero"
safeDivide x y = Right (x / y)
```

#### 2.2 高级模式匹配

**定义 2.2 (高级模式)**
高级模式匹配包括：

```haskell
-- 嵌套模式匹配
data Tree a = Leaf a | Node (Tree a) (Tree a)

treeDepth :: Tree a -> Int
treeDepth (Leaf _) = 0
treeDepth (Node left right) = 1 + max (treeDepth left) (treeDepth right)

-- 模式匹配与守卫
absolute :: (Ord a, Num a) => a -> a
absolute x
  | x < 0 = -x
  | otherwise = x

-- 模式匹配与where子句
complexPattern :: [Int] -> String
complexPattern [] = "Empty"
complexPattern [x] = "Single: " ++ show x
complexPattern (x:y:xs) = "Multiple: " ++ show x ++ ", " ++ show y ++ ", rest: " ++ show (length xs)
  where
    total = sum (x:y:xs)
    average = fromIntegral total / fromIntegral (length (x:y:xs))

-- 模式匹配与let表达式
patternWithLet :: (Int, Int) -> Int
patternWithLet (x, y) = 
  let sum = x + y
      product = x * y
      difference = x - y
  in sum + product + difference

-- 模式匹配与case表达式
casePattern :: Maybe Int -> String
casePattern maybeValue = case maybeValue of
  Nothing -> "No value"
  Just 0 -> "Zero"
  Just n | n < 0 -> "Negative: " ++ show n
         | otherwise -> "Positive: " ++ show n
```

### 3. 递归控制流

#### 3.1 基本递归

**定义 3.1 (递归)**
递归是函数式编程中的核心控制流机制：

```haskell
-- 列表递归
length' :: [a] -> Int
length' [] = 0
length' (_:xs) = 1 + length' xs

sum' :: Num a => [a] -> a
sum' [] = 0
sum' (x:xs) = x + sum' xs

product' :: Num a => [a] -> a
product' [] = 1
product' (x:xs) = x * product' xs

-- 树递归
data BinaryTree a = Empty | Node a (BinaryTree a) (BinaryTree a)

treeSize :: BinaryTree a -> Int
treeSize Empty = 0
treeSize (Node _ left right) = 1 + treeSize left + treeSize right

treeSum :: Num a => BinaryTree a -> a
treeSum Empty = 0
treeSum (Node value left right) = value + treeSum left + treeSum right

-- 尾递归
factorial :: Integer -> Integer
factorial n = factorial' n 1
  where
    factorial' 0 acc = acc
    factorial' n acc = factorial' (n - 1) (n * acc)

-- 相互递归
even' :: Int -> Bool
even' 0 = True
even' n = odd' (n - 1)

odd' :: Int -> Bool
odd' 0 = False
odd' n = even' (n - 1)
```

#### 3.2 高级递归模式

**定义 3.2 (高级递归)**
高级递归模式包括：

```haskell
-- 累积递归
reverse' :: [a] -> [a]
reverse' = reverseAcc []
  where
    reverseAcc acc [] = acc
    reverseAcc acc (x:xs) = reverseAcc (x:acc) xs

-- 分治递归
mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort [x] = [x]
mergeSort xs = 
  let (left, right) = splitAt (length xs `div` 2) xs
  in merge (mergeSort left) (mergeSort right)

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys)
  | x <= y = x : merge xs (y:ys)
  | otherwise = y : merge (x:xs) ys

-- 递归模式匹配
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (pivot:xs) = 
  quicksort [x | x <- xs, x <= pivot] ++ 
  [pivot] ++ 
  quicksort [x | x <- xs, x > pivot]

-- 递归数据结构
data List a = Nil | Cons a (List a)

listLength :: List a -> Int
listLength Nil = 0
listLength (Cons _ xs) = 1 + listLength xs

listMap :: (a -> b) -> List a -> List b
listMap _ Nil = Nil
listMap f (Cons x xs) = Cons (f x) (listMap f xs)
```

### 4. 条件控制流

#### 4.1 守卫表达式

**定义 4.1 (守卫)**
守卫表达式提供条件控制流：

```haskell
-- 基本守卫
grade :: Int -> String
grade score
  | score >= 90 = "A"
  | score >= 80 = "B"
  | score >= 70 = "C"
  | score >= 60 = "D"
  | otherwise = "F"

-- 复杂守卫
analyzeNumber :: Int -> String
analyzeNumber n
  | n < 0 = "Negative"
  | n == 0 = "Zero"
  | n `mod` 2 == 0 = "Even positive"
  | otherwise = "Odd positive"

-- 守卫与模式匹配结合
safeDivide' :: Double -> Double -> Maybe Double
safeDivide' x y
  | y == 0 = Nothing
  | x == 0 = Just 0
  | otherwise = Just (x / y)

-- 多重条件守卫
complexGuard :: Int -> Int -> Int -> String
complexGuard a b c
  | a > b && b > c = "Decreasing"
  | a < b && b < c = "Increasing"
  | a == b && b == c = "All equal"
  | otherwise = "Mixed"
```

#### 4.2 if-then-else表达式

**定义 4.2 (条件表达式)**
if-then-else表达式提供简单的条件控制：

```haskell
-- 基本if-then-else
absolute' :: (Ord a, Num a) => a -> a
absolute' x = if x < 0 then -x else x

-- 嵌套if-then-else
maxThree :: Ord a => a -> a -> a -> a
maxThree x y z = if x > y 
                 then if x > z then x else z
                 else if y > z then y else z

-- if-then-else与函数组合
processValue :: Int -> String
processValue n = if n > 0 
                 then "Positive: " ++ show n
                 else if n < 0 
                      then "Negative: " ++ show n
                      else "Zero"

-- 条件表达式与模式匹配
safeHead' :: [a] -> Maybe a
safeHead' xs = if null xs then Nothing else Just (head xs)
```

### 5. 异常处理控制流

#### 5.1 Maybe类型

**定义 5.1 (Maybe控制流)**
Maybe类型提供安全的错误处理：

```haskell
-- Maybe类型操作
maybeHead :: [a] -> Maybe a
maybeHead [] = Nothing
maybeHead (x:_) = Just x

maybeTail :: [a] -> Maybe [a]
maybeTail [] = Nothing
maybeTail (_:xs) = Just xs

-- Maybe链式操作
safeDivideChain :: Double -> Double -> Double -> Maybe Double
safeDivideChain x y z = do
  result1 <- safeDivide x y
  safeDivide result1 z

-- Maybe与模式匹配
processMaybe :: Maybe Int -> String
processMaybe Nothing = "No value"
processMaybe (Just n) = "Value: " ++ show n

-- Maybe与函数组合
maybeMap :: (a -> b) -> Maybe a -> Maybe b
maybeMap _ Nothing = Nothing
maybeMap f (Just x) = Just (f x)

maybeBind :: Maybe a -> (a -> Maybe b) -> Maybe b
maybeBind Nothing _ = Nothing
maybeBind (Just x) f = f x
```

#### 5.2 Either类型

**定义 5.2 (Either控制流)**
Either类型提供更丰富的错误处理：

```haskell
-- Either类型操作
safeDivide' :: Double -> Double -> Either String Double
safeDivide' _ 0 = Left "Division by zero"
safeDivide' x y = Right (x / y)

safeSqrt :: Double -> Either String Double
safeSqrt x
  | x < 0 = Left "Cannot take square root of negative number"
  | otherwise = Right (sqrt x)

-- Either链式操作
complexCalculation :: Double -> Double -> Either String Double
complexCalculation x y = do
  result1 <- safeDivide x y
  result2 <- safeSqrt result1
  return (result2 * 2)

-- Either与模式匹配
processEither :: Either String Int -> String
processEither (Left error) = "Error: " ++ error
processEither (Right value) = "Success: " ++ show value

-- Either与函数组合
eitherMap :: (a -> b) -> (e -> f) -> Either e a -> Either f b
eitherMap f _ (Right x) = Right (f x)
eitherMap _ g (Left e) = Left (g e)
```

### 6. 单子控制流

#### 6.1 IO单子

**定义 6.1 (IO控制流)**
IO单子处理副作用控制流：

```haskell
-- 基本IO操作
getUserInput :: IO String
getUserInput = do
  putStrLn "Enter your name:"
  getLine

processUserInput :: IO ()
processUserInput = do
  name <- getUserInput
  putStrLn $ "Hello, " ++ name ++ "!"

-- IO控制流
interactiveCalculator :: IO ()
interactiveCalculator = do
  putStrLn "Enter first number:"
  num1Str <- getLine
  putStrLn "Enter second number:"
  num2Str <- getLine
  
  let num1 = read num1Str :: Double
      num2 = read num2Str :: Double
      result = num1 + num2
  
  putStrLn $ "Result: " ++ show result

-- IO与错误处理
safeIOOperation :: IO (Either String Int)
safeIOOperation = do
  putStrLn "Enter a number:"
  input <- getLine
  case reads input of
    [(n, "")] -> return (Right n)
    _ -> return (Left "Invalid number")

-- IO循环
interactiveLoop :: IO ()
interactiveLoop = do
  putStrLn "Enter a command (quit to exit):"
  command <- getLine
  case command of
    "quit" -> putStrLn "Goodbye!"
    _ -> do
      putStrLn $ "You entered: " ++ command
      interactiveLoop
```

#### 6.2 状态单子

**定义 6.2 (状态控制流)**
状态单子处理状态管理控制流：

```haskell
-- 状态单子定义
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap f (State g) = State $ \s -> 
    let (a, s') = g s in (f a, s')

instance Applicative (State s) where
  pure a = State $ \s -> (a, s)
  (State f) <*> (State g) = State $ \s ->
    let (h, s') = f s
        (a, s'') = g s'
    in (h a, s'')

instance Monad (State s) where
  return = pure
  (State f) >>= g = State $ \s ->
    let (a, s') = f s
        State h = g a
    in h s'

-- 状态操作
get :: State s s
get = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ \_ -> ((), s)

modify :: (s -> s) -> State s ()
modify f = State $ \s -> ((), f s)

-- 状态控制流示例
counter :: State Int Int
counter = do
  current <- get
  put (current + 1)
  return current

-- 复杂状态操作
stackOperations :: State [Int] ()
stackOperations = do
  push 1
  push 2
  push 3
  pop
  push 4

push :: Int -> State [Int] ()
push x = modify (x:)

pop :: State [Int] (Maybe Int)
pop = do
  stack <- get
  case stack of
    [] -> return Nothing
    (x:xs) -> do
      put xs
      return (Just x)
```

### 7. 高级控制流模式

#### 7.1 延续传递风格 (CPS)

**定义 7.1 (CPS)**
延续传递风格是一种高级控制流模式：

```haskell
-- 基本CPS
type Continuation a r = a -> r

cpsAdd :: Int -> Int -> Continuation Int r -> r
cpsAdd x y k = k (x + y)

cpsMultiply :: Int -> Int -> Continuation Int r -> r
cpsMultiply x y k = k (x * y)

-- CPS链式操作
cpsComplex :: Int -> Int -> Continuation Int r -> r
cpsComplex x y k = 
  cpsAdd x y $ \sum ->
  cpsMultiply sum 2 $ \product ->
  k product

-- CPS与异常处理
cpsSafeDivide :: Double -> Double -> Continuation Double (Either String Double) -> Either String Double
cpsSafeDivide x y k
  | y == 0 = Left "Division by zero"
  | otherwise = k (x / y)

-- CPS与状态
type StateCont s a r = (a -> s -> r) -> s -> r

cpsState :: StateCont s a r -> State s a
cpsState f = State $ \s -> f (\a s' -> (a, s')) s
```

#### 7.2 箭头控制流

**定义 7.2 (箭头)**
箭头提供另一种函数组合控制流：

```haskell
-- 箭头类型类
class Arrow a where
  arr :: (b -> c) -> a b c
  (>>>) :: a b c -> a c d -> a b d
  first :: a b c -> a (b, d) (c, d)

-- 函数箭头实例
instance Arrow (->) where
  arr f = f
  f >>> g = g . f
  first f = \(x, y) -> (f x, y)

-- 箭头操作
arrowAdd :: Arrow a => a (Int, Int) Int
arrowAdd = arr (\(x, y) -> x + y)

arrowMultiply :: Arrow a => a (Int, Int) Int
arrowMultiply = arr (\(x, y) -> x * y)

-- 箭头组合
arrowComplex :: Arrow a => a (Int, Int) Int
arrowComplex = arrowAdd >>> arr (* 2)

-- 箭头与条件
arrowCondition :: Arrow a => a Int String
arrowCondition = arr $ \x -> 
  if x > 0 then "Positive" 
  else if x < 0 then "Negative" 
  else "Zero"
```

### 8. 实际应用

#### 8.1 解析器控制流

```haskell
-- 基本解析器
newtype Parser a = Parser { runParser :: String -> Maybe (a, String) }

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> 
    case p s of
      Just (a, s') -> Just (f a, s')
      Nothing -> Nothing

instance Applicative Parser where
  pure a = Parser $ \s -> Just (a, s)
  (Parser f) <*> (Parser g) = Parser $ \s ->
    case f s of
      Just (h, s') -> 
        case g s' of
          Just (a, s'') -> Just (h a, s'')
          Nothing -> Nothing
      Nothing -> Nothing

instance Monad Parser where
  return = pure
  (Parser p) >>= f = Parser $ \s ->
    case p s of
      Just (a, s') -> runParser (f a) s'
      Nothing -> Nothing

-- 解析器控制流
char :: Char -> Parser Char
char c = Parser $ \s ->
  case s of
    (x:xs) | x == c -> Just (c, xs)
    _ -> Nothing

string :: String -> Parser String
string [] = return []
string (c:cs) = do
  char c
  string cs
  return (c:cs)

-- 解析器组合
parseNumber :: Parser Int
parseNumber = do
  digits <- many1 digit
  return (read digits)

digit :: Parser Char
digit = Parser $ \s ->
  case s of
    (c:cs) | c >= '0' && c <= '9' -> Just (c, cs)
    _ -> Nothing

many1 :: Parser a -> Parser [a]
many1 p = do
  x <- p
  xs <- many p
  return (x:xs)

many :: Parser a -> Parser [a]
many p = many1 p <|> return []
```

#### 8.2 游戏循环控制流

```haskell
-- 游戏状态
data GameState = GameState 
  { playerPosition :: (Int, Int)
  , playerHealth :: Int
  , gameLevel :: Int
  , enemies :: [(Int, Int)]
  }

-- 游戏动作
data GameAction = MoveUp | MoveDown | MoveLeft | MoveRight | Attack | Quit

-- 游戏控制流
gameLoop :: GameState -> IO ()
gameLoop state = do
  displayGame state
  action <- getPlayerAction
  case action of
    Quit -> putStrLn "Game Over"
    _ -> do
      let newState = updateGame state action
      gameLoop newState

-- 游戏更新控制流
updateGame :: GameState -> GameAction -> GameState
updateGame state action = case action of
  MoveUp -> state { playerPosition = movePlayer state (-1, 0) }
  MoveDown -> state { playerPosition = movePlayer state (1, 0) }
  MoveLeft -> state { playerPosition = movePlayer state (0, -1) }
  MoveRight -> state { playerPosition = movePlayer state (0, 1) }
  Attack -> performAttack state
  Quit -> state

-- 移动控制流
movePlayer :: GameState -> (Int, Int) -> (Int, Int)
movePlayer state (dx, dy) = 
  let (x, y) = playerPosition state
      newX = max 0 (min 10 (x + dx))
      newY = max 0 (min 10 (y + dy))
  in (newX, newY)

-- 攻击控制流
performAttack :: GameState -> GameState
performAttack state = 
  let nearbyEnemies = filter (isNearby (playerPosition state)) (enemies state)
  in state { enemies = filter (not . isNearby (playerPosition state)) (enemies state) }

isNearby :: (Int, Int) -> (Int, Int) -> Bool
isNearby (x1, y1) (x2, y2) = abs (x1 - x2) <= 1 && abs (y1 - y2) <= 1
```

## 🔗 交叉引用

### 相关理论

- [[001-Linear-Type-Theory]] - 线性类型理论
- [[002-Affine-Type-Theory]] - 仿射类型理论
- [[003-Temporal-Type-Theory]] - 时态类型理论
- [[002-Formal-Logic]] - 形式逻辑基础

### Haskell实现

- [[haskell/01-Basic-Concepts]] - Haskell基础概念
- [[haskell/02-Type-System]] - Haskell类型系统
- [[haskell/04-Data-Flow]] - Haskell数据流
- [[haskell/05-Design-Patterns]] - Haskell设计模式

## 📚 参考文献

1. Peyton Jones, S. (2003). The Haskell 98 Language and Libraries: The Revised Report. Cambridge University Press.
2. Hutton, G. (2016). Programming in Haskell. Cambridge University Press.
3. Bird, R. (2015). Thinking Functionally with Haskell. Cambridge University Press.
4. Thompson, S. (2011). Haskell: The Craft of Functional Programming. Pearson Education.

---

**文档状态**：✅ 完成  
**最后更新**：2024-12-19  
**版本**：1.0
