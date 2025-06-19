# Haskell 设计模式基础

## 🎯 概述

Haskell作为纯函数式编程语言，其设计模式具有独特的数学基础和函数式特性。本章深入介绍Haskell中的设计模式基础概念、分类和应用，特别关注函数式设计模式、类型级设计模式和软件架构模式。

## 📚 设计模式分类体系

### 1. 函数式设计模式

#### 1.1 纯函数模式

```haskell
-- 纯函数：无副作用，相同输入总是产生相同输出
pureFunction :: Int -> Int
pureFunction x = x * x + 1

-- 函数组合
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g = f . g

-- 高阶函数
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

-- 函数柯里化
curriedAdd :: Int -> Int -> Int
curriedAdd x y = x + y

-- 部分应用
addFive :: Int -> Int
addFive = curriedAdd 5
```

#### 1.2 不可变数据模式

```haskell
-- 不可变数据结构
data Point = Point { x :: Double, y :: Double }
  deriving (Show, Eq)

-- 创建新实例而不是修改
movePoint :: Point -> Double -> Double -> Point
movePoint (Point x y) dx dy = Point (x + dx) (y + dy)

-- 代数数据类型
data Shape = Circle Double | Rectangle Double Double | Triangle Double Double Double
  deriving (Show)

-- 模式匹配
area :: Shape -> Double
area (Circle r) = pi * r * r
area (Rectangle w h) = w * h
area (Triangle a b c) = sqrt (s * (s - a) * (s - b) * (s - c))
  where s = (a + b + c) / 2
```

### 2. 类型级设计模式

#### 2.1 类型类模式

```haskell
-- 类型类：多态接口
class Add a where
  add :: a -> a -> a

instance Add Int where
  add = (+)

instance Add Double where
  add = (+)

instance Add String where
  add = (++)

-- 使用类型类
sum :: (Add a, Foldable t) => t a -> a
sum xs = foldr add (error "empty list") xs

-- 类型类约束
class (Show a, Eq a) => Printable a where
  printValue :: a -> String
  printValue = show
```

#### 2.2 高级类型模式

```haskell
-- 类型族
type family ElementType container where
  ElementType [a] = a
  ElementType (Maybe a) = a
  ElementType (Either a b) = a

-- 关联类型
class Container c where
  type Element c
  empty :: c
  insert :: Element c -> c -> c
  contains :: Element c -> c -> Bool

instance Container [a] where
  type Element [a] = a
  empty = []
  insert = (:)
  contains = elem

-- 类型级编程
data Nat = Zero | Succ Nat

type family Add (n :: Nat) (m :: Nat) :: Nat where
  Add Zero m = m
  Add (Succ n) m = Succ (Add n m)
```

### 3. Monad设计模式

#### 3.1 Monad基础

```haskell
-- Monad类型类
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- Maybe Monad
instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just x >>= f = f x

-- List Monad
instance Monad [] where
  return x = [x]
  xs >>= f = concat (map f xs)

-- IO Monad
instance Monad IO where
  return = return
  (>>=) = (>>=)
```

#### 3.2 Monad变换器

```haskell
-- Monad变换器
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Monad (MaybeT m) where
  return = MaybeT . return . Just
  m >>= k = MaybeT $ do
    a <- runMaybeT m
    case a of
      Nothing -> return Nothing
      Just x -> runMaybeT (k x)

-- 组合Monad
type AppM = MaybeT IO

safeReadFile :: FilePath -> AppM String
safeReadFile path = MaybeT $ do
  exists <- doesFileExist path
  if exists
    then Just <$> readFile path
    else return Nothing
```

### 4. 函数式架构模式

#### 4.1 Free Monad模式

```haskell
-- Free Monad
data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free fa) = Free (fmap (fmap f) fa)

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> Pure a = Pure (f a)
  Pure f <*> Free fa = Free (fmap (fmap f) fa)
  Free ff <*> a = Free (fmap (<*> a) ff)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= k = k a
  Free fa >>= k = Free (fmap (>>= k) fa)

-- 代数效应
data FileSystemF a
  = ReadFile String (String -> a)
  | WriteFile String String a
  | DeleteFile String a

type FileSystem = Free FileSystemF

readFile :: String -> FileSystem String
readFile path = Free (ReadFile path Pure)

writeFile :: String -> String -> FileSystem ()
writeFile path content = Free (WriteFile path content (Pure ()))

deleteFile :: String -> FileSystem ()
deleteFile path = Free (DeleteFile path (Pure ()))
```

#### 4.2 Tagless Final模式

```haskell
-- Tagless Final
class Monad m => FileSystem m where
  readFile :: FilePath -> m String
  writeFile :: FilePath -> String -> m ()
  deleteFile :: FilePath -> m ()

-- 具体实现
newtype IOFileSystem a = IOFileSystem { runIOFileSystem :: IO a }
  deriving (Functor, Applicative, Monad)

instance FileSystem IOFileSystem where
  readFile = IOFileSystem . readFile
  writeFile path = IOFileSystem . writeFile path
  deleteFile = IOFileSystem . removeFile

-- 测试实现
newtype TestFileSystem a = TestFileSystem { runTestFileSystem :: State [(FilePath, String)] a }
  deriving (Functor, Applicative, Monad)

instance FileSystem TestFileSystem where
  readFile path = TestFileSystem $ do
    files <- get
    case lookup path files of
      Just content -> return content
      Nothing -> error "File not found"
  writeFile path content = TestFileSystem $ do
    files <- get
    put ((path, content) : files)
  deleteFile path = TestFileSystem $ do
    files <- get
    put (filter ((/= path) . fst) files)
```

## 🏗️ 软件设计模式

### 1. 依赖注入模式

```haskell
-- 依赖注入
class Monad m => UserRepository m where
  findUser :: UserId -> m (Maybe User)
  saveUser :: User -> m ()
  deleteUser :: UserId -> m Bool

class Monad m => EmailService m where
  sendEmail :: Email -> m Bool

-- 服务层
data UserService m = UserService
  { userRepo :: UserRepository m
  , emailService :: EmailService m
  }

createUser :: (Monad m, UserRepository m, EmailService m) => User -> m User
createUser user = do
  saveUser user
  sendEmail (welcomeEmail user)
  return user

-- 具体实现
newtype AppM a = AppM { runAppM :: ReaderT (UserService AppM) IO a }
  deriving (Functor, Applicative, Monad)

instance UserRepository AppM where
  findUser = userRepo . findUser
  saveUser = userRepo . saveUser
  deleteUser = userRepo . deleteUser

instance EmailService AppM where
  sendEmail = emailService . sendEmail
```

### 2. 观察者模式

```haskell
-- 观察者模式
class Observer a where
  update :: String -> a -> a

class Subject a where
  attach :: Observer b => b -> a -> a
  detach :: Observer b => b -> a -> a
  notify :: String -> a -> a

-- 具体实现
data NewsSubject = NewsSubject
  { observers :: [String -> IO ()]
  , news :: String
  }

instance Subject NewsSubject where
  attach observer subject = subject { observers = observer : observers subject }
  detach observer subject = subject { observers = filter (/= observer) (observers subject) }
  notify news subject = do
    mapM_ ($ news) (observers subject)
    return subject { news = news }
```

### 3. 工厂模式

```haskell
-- 工厂模式
class Product a where
  name :: a -> String
  price :: a -> Double

data Book = Book { title :: String, author :: String, bookPrice :: Double }
data Electronics = Electronics { brand :: String, model :: String, elecPrice :: Double }

instance Product Book where
  name = title
  price = bookPrice

instance Product Electronics where
  name = \e -> brand e ++ " " ++ model e
  price = elecPrice

-- 工厂
class ProductFactory where
  createBook :: String -> String -> Double -> Book
  createElectronics :: String -> String -> Double -> Electronics

instance ProductFactory where
  createBook title author price = Book title author price
  createElectronics brand model price = Electronics brand model price
```

## 🔄 控制流模式

### 1. 异常处理模式

```haskell
-- 异常处理
data AppError = FileNotFound String | ValidationError String | NetworkError String
  deriving (Show, Eq)

type AppM = Either AppError

safeReadFile :: FilePath -> AppM String
safeReadFile path = do
  exists <- liftIO $ doesFileExist path
  if exists
    then liftIO $ readFile path
    else Left (FileNotFound path)

-- 异常转换
class MonadError e m => ErrorHandler e m where
  handleError :: e -> m a
  recover :: m a -> (e -> m a) -> m a

instance ErrorHandler AppError (Either AppError) where
  handleError = Left
  recover (Right a) _ = Right a
  recover (Left e) handler = handler e
```

### 2. 状态管理模式

```haskell
-- 状态管理
class MonadState s m => StateManager s m where
  getState :: m s
  setState :: s -> m ()
  modifyState :: (s -> s) -> m ()

-- 应用状态
data AppState = AppState
  { currentUser :: Maybe User
  , settings :: Settings
  , cache :: Map String String
  }

newtype AppM a = AppM { runAppM :: StateT AppState IO a }
  deriving (Functor, Applicative, Monad)

instance MonadState AppState AppM where
  get = AppM get
  put = AppM . put
  state = AppM . state

-- 状态操作
getCurrentUser :: AppM (Maybe User)
getCurrentUser = currentUser <$> get

setCurrentUser :: User -> AppM ()
setCurrentUser user = modify $ \s -> s { currentUser = Just user }

updateSettings :: (Settings -> Settings) -> AppM ()
updateSettings f = modify $ \s -> s { settings = f (settings s) }
```

## 📊 数据流模式

### 1. 流处理模式

```haskell
-- 流处理
data Stream a = Stream
  { head :: a
  , tail :: Stream a
  }

-- 无限流
naturals :: Stream Integer
naturals = Stream 0 (fmap (+1) naturals)

-- 流操作
mapStream :: (a -> b) -> Stream a -> Stream b
mapStream f (Stream x xs) = Stream (f x) (mapStream f xs)

filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream p (Stream x xs)
  | p x = Stream x (filterStream p xs)
  | otherwise = filterStream p xs

-- 流组合
zipStreams :: Stream a -> Stream b -> Stream (a, b)
zipStreams (Stream x xs) (Stream y ys) = Stream (x, y) (zipStreams xs ys)
```

### 2. 管道模式

```haskell
-- 管道模式
newtype Pipe a b m r = Pipe { runPipe :: a -> m (Either r (b, Pipe a b m r)) }

instance Monad m => Functor (Pipe a b m) where
  fmap f (Pipe p) = Pipe $ \a -> do
    result <- p a
    case result of
      Left r -> return (Left r)
      Right (b, rest) -> return (Right (f b, fmap f rest))

instance Monad m => Applicative (Pipe a b m) where
  pure r = Pipe $ \_ -> return (Left r)
  Pipe f <*> Pipe g = Pipe $ \a -> do
    result1 <- f a
    case result1 of
      Left r -> return (Left r)
      Right (h, rest1) -> do
        result2 <- g a
        case result2 of
          Left r -> return (Left r)
          Right (x, rest2) -> return (Right (h x, rest1 <*> rest2))

instance Monad m => Monad (Pipe a b m) where
  return = pure
  Pipe p >>= k = Pipe $ \a -> do
    result <- p a
    case result of
      Left r -> runPipe (k r) a
      Right (b, rest) -> return (Right (b, rest >>= k))

-- 管道操作
yield :: Monad m => b -> Pipe a b m ()
yield b = Pipe $ \_ -> return (Right (b, return ()))

await :: Monad m => Pipe a b m a
await = Pipe $ \a -> return (Right (a, return ()))

-- 管道组合
(>->) :: Monad m => Pipe a b m r -> Pipe b c m r -> Pipe a c m r
Pipe p1 >-> Pipe p2 = Pipe $ \a -> do
  result1 <- p1 a
  case result1 of
    Left r -> return (Left r)
    Right (b, rest1) -> do
      result2 <- p2 b
      case result2 of
        Left r -> return (Left r)
        Right (c, rest2) -> return (Right (c, rest1 >-> rest2))
```

## 🎯 应用场景

### 1. Web应用开发

- **路由处理**: 使用Monad变换器组合
- **数据库操作**: 使用Reader模式
- **认证授权**: 使用State模式

### 2. 数据处理

- **流式处理**: 使用Stream模式
- **批处理**: 使用管道模式
- **实时处理**: 使用响应式模式

### 3. 系统集成

- **微服务**: 使用Free Monad模式
- **API设计**: 使用Tagless Final模式
- **配置管理**: 使用Reader模式

## 🚀 最佳实践

### 1. 设计原则

- **纯函数优先**: 尽可能使用纯函数
- **类型安全**: 充分利用类型系统
- **组合性**: 设计可组合的组件

### 2. 实现策略

- **渐进式**: 从简单模式开始
- **模块化**: 清晰的模块边界
- **测试驱动**: 先写测试再实现

### 3. 性能考虑

- **惰性求值**: 利用Haskell的惰性特性
- **内存管理**: 注意内存使用模式
- **并发处理**: 使用适当的并发模式

---

**下一节**: [创建型模式](./02-Creational-Patterns.md)

**相关链接**:

- [类型系统](../02-Type-System/)
- [控制流](../03-Control-Flow/)
- [数据流](../04-Data-Flow/)
- [软件设计](../08-Software-Design/)
