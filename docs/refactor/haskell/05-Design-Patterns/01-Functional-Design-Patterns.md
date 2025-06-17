# Haskell 函数式设计模式

## 概述

函数式设计模式是Haskell中构建可维护、可扩展软件的核心模式，基于函数式编程的纯函数、不可变性和高阶函数特性。

## 数学定义

### 函子模式形式化定义

给定范畴 $\mathcal{C}$ 和 $\mathcal{D}$，函子 $F : \mathcal{C} \rightarrow \mathcal{D}$ 定义为：

$$F : \text{Obj}(\mathcal{C}) \rightarrow \text{Obj}(\mathcal{D})$$

满足：

$$F(f \circ g) = F(f) \circ F(g)$$

### 单子模式形式化定义

单子定义为三元组 $(M, \eta, \mu)$，其中：

- $M : \mathcal{C} \rightarrow \mathcal{C}$ 是函子
- $\eta : \text{Id} \rightarrow M$ 是单位自然变换
- $\mu : M \circ M \rightarrow M$ 是乘法自然变换

满足单子律：

$$\mu \circ \eta_M = \text{id}_M = \mu \circ M\eta$$
$$\mu \circ \mu_M = \mu \circ M\mu$$

### 应用函子形式化定义

应用函子定义为四元组 $(F, \eta, \mu, \alpha)$，其中：

- $(F, \eta, \mu)$ 是单子
- $\alpha : F(A \times B) \rightarrow FA \times FB$ 是分配律

## Haskell实现

### 函子模式

```haskell
-- 函子模式模块
module DesignPatterns.Functor where

-- 函子类型类
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- 函子律
-- 1. fmap id = id
-- 2. fmap (f . g) = fmap f . fmap g

-- Maybe函子实例
instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

-- 列表函子实例
instance Functor [] where
  fmap = map

-- 函数函子实例
instance Functor ((->) r) where
  fmap = (.)

-- 元组函子实例
instance Functor ((,) a) where
  fmap f (x, y) = (x, f y)

-- 函子组合
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap f (Compose x) = Compose (fmap (fmap f) x)
```

### 应用函子模式

```haskell
-- 应用函子模式
module DesignPatterns.Applicative where

-- 应用函子类型类
class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

-- 应用函子律
-- 1. pure id <*> v = v
-- 2. pure f <*> pure x = pure (f x)
-- 3. u <*> pure y = pure ($ y) <*> u
-- 4. u <*> (v <*> w) = pure (.) <*> u <*> v <*> w

-- Maybe应用函子实例
instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  Just f <*> x = fmap f x

-- 列表应用函子实例
instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]

-- 函数应用函子实例
instance Applicative ((->) r) where
  pure = const
  f <*> g = \x -> f x (g x)

-- 应用函子组合
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Applicative f, Applicative g) => Applicative (Compose f g) where
  pure x = Compose (pure (pure x))
  Compose f <*> Compose x = Compose (liftA2 (<*>) f x)
```

### 单子模式

```haskell
-- 单子模式
module DesignPatterns.Monad where

-- 单子类型类
class Applicative m => Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- 单子律
-- 1. return a >>= k = k a
-- 2. m >>= return = m
-- 3. m >>= (\x -> k x >>= h) = (m >>= k) >>= h

-- Maybe单子实例
instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just x >>= f = f x

-- 列表单子实例
instance Monad [] where
  return x = [x]
  xs >>= f = concat (map f xs)

-- 函数单子实例
instance Monad ((->) r) where
  return = const
  f >>= g = \x -> g (f x) x

-- 单子组合
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Monad f, Monad g) => Monad (Compose f g) where
  return = Compose . return . return
  Compose f >>= g = Compose $ f >>= \x -> sequence x >>= getCompose . g
```

### 高级设计模式

```haskell
-- 状态单子模式
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap f (State g) = State $ \s -> let (a, s') = g s in (f a, s')

instance Applicative (State s) where
  pure a = State $ \s -> (a, s)
  State f <*> State g = State $ \s -> 
    let (h, s') = f s
        (a, s'') = g s'
    in (h a, s'')

instance Monad (State s) where
  return = pure
  State f >>= g = State $ \s -> 
    let (a, s') = f s
        State h = g a
    in h s'

-- 读取器单子模式
newtype Reader r a = Reader { runReader :: r -> a }

instance Functor (Reader r) where
  fmap f (Reader g) = Reader (f . g)

instance Applicative (Reader r) where
  pure a = Reader $ const a
  Reader f <*> Reader g = Reader $ \r -> f r (g r)

instance Monad (Reader r) where
  return = pure
  Reader f >>= g = Reader $ \r -> runReader (g (f r)) r

-- 写入器单子模式
newtype Writer w a = Writer { runWriter :: (a, w) }

instance Functor (Writer w) where
  fmap f (Writer (a, w)) = Writer (f a, w)

instance Monoid w => Applicative (Writer w) where
  pure a = Writer (a, mempty)
  Writer (f, w1) <*> Writer (a, w2) = Writer (f a, w1 <> w2)

instance Monoid w => Monad (Writer w) where
  return = pure
  Writer (a, w1) >>= f = 
    let Writer (b, w2) = f a
    in Writer (b, w1 <> w2)
```

## 形式化语义

### 函子语义

```haskell
-- 函子语义定义
data FunctorSemantics f a b = 
  FunctorSemantics 
    { functorMap :: (a -> b) -> f a -> f b
    , functorIdentity :: f a -> f a
    , functorComposition :: (b -> c) -> (a -> b) -> f a -> f c
    }

-- 函子语义解释器
interpretFunctor :: FunctorSemantics f a b -> (a -> b) -> f a -> f b
interpretFunctor (FunctorSemantics fmap' _ _) = fmap'

-- 函子的代数性质
class FunctorAlgebra f where
  -- 单位元
  functorUnit :: a -> f a
  -- 映射律
  functorMap :: (a -> b) -> f a -> f b
  -- 组合律
  functorCompose :: (b -> c) -> (a -> b) -> f a -> f c
```

### 单子语义

```haskell
-- 单子语义定义
data MonadSemantics m a b = 
  MonadSemantics 
    { monadReturn :: a -> m a
    , monadBind :: m a -> (a -> m b) -> m b
    , monadJoin :: m (m a) -> m a
    }

-- 单子语义解释器
interpretMonad :: MonadSemantics m a b -> m a -> (a -> m b) -> m b
interpretMonad (MonadSemantics _ bind _) = bind

-- 单子的代数性质
class MonadAlgebra m where
  -- 单位元
  monadUnit :: a -> m a
  -- 乘法
  monadMultiply :: m (m a) -> m a
  -- 结合律
  monadAssociate :: m (m (m a)) -> m a
```

## 类型安全保证

### 函子类型系统

```haskell
-- 函子类型检查
class TypeSafeFunctor f where
  type FunctorInput f a
  type FunctorOutput f b
  
  -- 类型安全的函子映射
  typeSafeFmap :: (a -> b) -> FunctorInput f a -> FunctorOutput f b
  
  -- 类型安全的函子组合
  typeSafeCompose :: (b -> c) -> (a -> b) -> FunctorInput f a -> FunctorOutput f c

-- 实例化
instance TypeSafeFunctor Maybe where
  type FunctorInput Maybe a = Maybe a
  type FunctorOutput Maybe b = Maybe b
  
  typeSafeFmap = fmap
  typeSafeCompose f g = fmap f . fmap g
```

### 单子类型系统

```haskell
-- 单子类型检查
class TypeSafeMonad m where
  type MonadInput m a
  type MonadOutput m b
  
  -- 类型安全的单子返回
  typeSafeReturn :: a -> MonadInput m a
  
  -- 类型安全的单子绑定
  typeSafeBind :: MonadInput m a -> (a -> MonadInput m b) -> MonadOutput m b

-- 实例化
instance TypeSafeMonad Maybe where
  type MonadInput Maybe a = Maybe a
  type MonadOutput Maybe b = Maybe b
  
  typeSafeReturn = Just
  typeSafeBind Nothing _ = Nothing
  typeSafeBind (Just x) f = f x
```

## 性能优化

### 函子优化

```haskell
-- 函子记忆化
memoizedFmap :: (Int -> a) -> (a -> b) -> Int -> b
memoizedFmap f g = g . memoize f
  where memoize f = (map f [0..] !!)

-- 函子并行化
parallelFmap :: (a -> b) -> [a] -> [b]
parallelFmap f xs = 
  -- 在实际实现中，这里会使用并行计算
  map f xs

-- 函子流式处理
streamFmap :: (a -> b) -> Stream a -> Stream b
streamFmap f (Stream x xs) = Stream (f x) (streamFmap f xs)
```

### 单子优化

```haskell
-- 单子记忆化
memoizedMonad :: (Int -> Maybe a) -> (a -> Maybe b) -> Int -> Maybe b
memoizedMonad f g n = 
  case memoize f n of
    Nothing -> Nothing
    Just x -> g x
  where memoize f = (map f [0..] !!)

-- 单子并行化
parallelMonad :: [Maybe a] -> (a -> Maybe b) -> [Maybe b]
parallelMonad xs f = 
  -- 在实际实现中，这里会使用并行计算
  map (\x -> x >>= f) xs

-- 单子流式处理
streamMonad :: Stream (Maybe a) -> (a -> Maybe b) -> Stream (Maybe b)
streamMonad (Stream x xs) f = 
  Stream (x >>= f) (streamMonad xs f)
```

## 实际应用

### 错误处理模式

```haskell
-- Maybe错误处理
safeDivide :: Double -> Double -> Maybe Double
safeDivide x y = if y == 0 then Nothing else Just (x / y)

-- Either错误处理
safeDivideEither :: Double -> Double -> Either String Double
safeDivideEither x y = 
  if y == 0 
    then Left "Division by zero"
    else Right (x / y)

-- 错误处理链
processData :: [String] -> Either String [Double]
processData = 
  mapM readEither >=> 
  mapM (\x -> if x > 0 then Right x else Left "Non-positive number")

-- 错误恢复
recoverFromError :: Either String a -> a -> a
recoverFromError (Left _) default' = default'
recoverFromError (Right x) _ = x
```

### 配置管理模式

```haskell
-- 配置数据类型
data Config = Config 
  { configHost :: String
  , configPort :: Int
  , configTimeout :: Double
  }

-- 配置读取器
type ConfigReader a = Reader Config a

-- 配置读取函数
getHost :: ConfigReader String
getHost = asks configHost

getPort :: ConfigReader Int
getPort = asks configPort

getTimeout :: ConfigReader Double
getTimeout = asks configTimeout

-- 配置验证
validateConfig :: Config -> Either String Config
validateConfig config
  | configPort config < 0 = Left "Invalid port"
  | configTimeout config <= 0 = Left "Invalid timeout"
  | otherwise = Right config

-- 配置应用
runWithConfig :: Config -> ConfigReader a -> a
runWithConfig config reader = runReader reader config
```

### 状态管理模式

```haskell
-- 游戏状态
data GameState = GameState 
  { playerPosition :: (Int, Int)
  , playerHealth :: Int
  , gameScore :: Int
  }

-- 游戏动作
data GameAction = Move (Int, Int) | Heal Int | AddScore Int

-- 状态更新
updateGameState :: GameAction -> State GameState ()
updateGameState (Move (dx, dy)) = do
  state <- get
  let (x, y) = playerPosition state
  put $ state { playerPosition = (x + dx, y + dy) }

updateGameState (Heal amount) = do
  state <- get
  put $ state { playerHealth = min 100 (playerHealth state + amount) }

updateGameState (AddScore points) = do
  state <- get
  put $ state { gameScore = gameScore state + points }

-- 游戏运行
runGame :: [GameAction] -> GameState -> GameState
runGame actions initialState = 
  snd $ runState (mapM updateGameState actions) initialState
```

### 日志记录模式

```haskell
-- 日志级别
data LogLevel = Debug | Info | Warning | Error

-- 日志消息
data LogMessage = LogMessage 
  { logLevel :: LogLevel
  , logMessage :: String
  , logTimestamp :: Integer
  }

-- 日志写入器
type Logger a = Writer [LogMessage] a

-- 日志函数
logMessage :: LogLevel -> String -> Logger ()
logMessage level msg = 
  tell [LogMessage level msg (getCurrentTimestamp)]

-- 日志组合
logDebug :: String -> Logger ()
logDebug = logMessage Debug

logInfo :: String -> Logger ()
logInfo = logMessage Info

logWarning :: String -> Logger ()
logWarning = logMessage Warning

logError :: String -> Logger ()
logError = logMessage Error

-- 带日志的计算
computeWithLogging :: Int -> Logger Int
computeWithLogging n = do
  logInfo $ "Starting computation with " ++ show n
  let result = n * n
  logInfo $ "Computation result: " ++ show result
  return result

-- 运行带日志的计算
runWithLogging :: Logger a -> (a, [LogMessage])
runWithLogging = runWriter
```

## 总结

Haskell的函数式设计模式提供了：

1. **类型安全**：编译时检查确保模式使用正确性
2. **组合性**：易于组合和重用模式
3. **抽象性**：提供高层次的抽象能力
4. **表达力**：简洁而强大的表达方式
5. **可维护性**：清晰的代码结构和语义

函数式设计模式是Haskell中构建高质量软件的核心工具，体现了函数式编程的优雅和强大。

---

**相关链接**：
- [函数式编程基础](../01-Basic-Concepts/函数式编程基础.md)
- [高阶函数](../02-Control-Flow/03-Higher-Order-Functions.md)
- [单子模式](./02-Monad-Patterns.md)
- [函子模式](./03-Functor-Patterns.md) 