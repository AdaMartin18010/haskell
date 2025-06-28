# 范畴论

## 概述

范畴论是数学的一个分支，为函数式编程提供了强大的理论基础。本文档介绍范畴论的核心概念及其在Haskell中的应用。

## 基本概念

### 范畴 (Category)

```haskell
-- 范畴的定义
class Category cat where
  id :: cat a a
  (.) :: cat b c -> cat a b -> cat a c

-- Haskell函数范畴
instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

-- Kleisli范畴
newtype Kleisli m a b = Kleisli { runKleisli :: a -> m b }

instance Monad m => Category (Kleisli m) where
  id = Kleisli return
  Kleisli f . Kleisli g = Kleisli (f <=< g)
```

### 函子 (Functor)

```haskell
-- 函子类型类
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- 函子定律
-- 1. fmap id = id
-- 2. fmap (g . f) = fmap g . fmap f

-- 常见函子实例
instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Functor [] where
  fmap = map

instance Functor (Either e) where
  fmap _ (Left e) = Left e
  fmap f (Right x) = Right (f x)
```

### 应用函子 (Applicative Functor)

```haskell
class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

-- 应用函子定律
-- 1. pure id <*> v = v
-- 2. pure f <*> pure x = pure (f x)
-- 3. u <*> pure y = pure ($ y) <*> u
-- 4. u <*> (v <*> w) = pure (.) <*> u <*> v <*> w

instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  Just f <*> x = fmap f x

instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]
```

### 单子 (Monad)

```haskell
class Applicative m => Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- 单子定律
-- 1. return a >>= k = k a
-- 2. m >>= return = m
-- 3. m >>= (\x -> k x >>= h) = (m >>= k) >>= h

instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just x >>= k = k x

instance Monad [] where
  return x = [x]
  xs >>= f = concat (map f xs)
```

## 高级概念

### 自然变换 (Natural Transformation)

```haskell
-- 自然变换
type Nat f g = forall a. f a -> g a

-- 自然变换的例子
maybeToList :: Nat Maybe []
maybeToList Nothing = []
maybeToList (Just x) = [x]

listToMaybe :: Nat [] Maybe
listToMaybe [] = Nothing
listToMaybe (x:_) = Just x
```

### 伴随函子 (Adjunction)

```haskell
-- 伴随函子的定义
class (Functor f, Functor g) => Adjunction f g where
  unit :: a -> g (f a)
  counit :: f (g a) -> a
  leftAdjunct :: (f a -> b) -> a -> g b
  rightAdjunct :: (a -> g b) -> f a -> b

-- 遗忘函子和自由函子的伴随
instance Adjunction (,) r ((->) r) where
  unit a = \r -> (r, a)
  counit (r, f) = f r
  leftAdjunct f a = \r -> f (r, a)
  rightAdjunct f (r, a) = f a r
```

### 幺半群 (Monoid)

```haskell
class Monoid m where
  mempty :: m
  mappend :: m -> m -> m

-- 幺半群定律
-- 1. mempty `mappend` x = x
-- 2. x `mappend` mempty = x
-- 3. (x `mappend` y) `mappend` z = x `mappend` (y `mappend` z)

instance Monoid [a] where
  mempty = []
  mappend = (++)

instance Monoid (Sum Int) where
  mempty = Sum 0
  mappend (Sum x) (Sum y) = Sum (x + y)
```

## 范畴论在编程中的应用

### 函子组合

```haskell
-- 函子组合
newtype Compose f g a = Compose { getCompose :: f (g a) }

instance (Functor f, Functor g) => Functor (Compose f g) where
  fmap f (Compose x) = Compose (fmap (fmap f) x)

instance (Applicative f, Applicative g) => Applicative (Compose f g) where
  pure = Compose . pure . pure
  Compose f <*> Compose x = Compose (liftA2 (<*>) f x)

instance (Monad f, Monad g) => Monad (Compose f g) where
  return = Compose . return . return
  Compose x >>= f = Compose $ x >>= (fmap getCompose . f)
```

### 自由单子

```haskell
-- 自由单子
data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free x) = Free (fmap (fmap f) x)

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure f <*> x = fmap f x
  Free f <*> x = Free (fmap (<*> x) f)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= f = f a
  Free x >>= f = Free (fmap (>>= f) x)
```

### Yoneda引理

```haskell
-- Yoneda引理
newtype Yoneda f a = Yoneda { runYoneda :: forall b. (a -> b) -> f b }

instance Functor (Yoneda f) where
  fmap f (Yoneda g) = Yoneda (\h -> g (h . f))

-- Yoneda嵌入
yoneda :: Functor f => f a -> Yoneda f a
yoneda fa = Yoneda (\f -> fmap f fa)

-- Yoneda投影
lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda f) = f id
```

## 范畴论模式

### 状态单子

```haskell
-- 状态单子
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
  fmap f (State g) = State (\s -> let (a, s') = g s in (f a, s'))

instance Applicative (State s) where
  pure a = State (\s -> (a, s))
  State f <*> State g = State (\s -> 
    let (h, s') = f s
        (a, s'') = g s'
    in (h a, s''))

instance Monad (State s) where
  return = pure
  State f >>= g = State (\s -> 
    let (a, s') = f s
        State h = g a
    in h s')

-- 状态操作
get :: State s s
get = State (\s -> (s, s))

put :: s -> State s ()
put s = State (\_ -> ((), s))

modify :: (s -> s) -> State s ()
modify f = State (\s -> ((), f s))
```

### Reader单子

```haskell
-- Reader单子
newtype Reader r a = Reader { runReader :: r -> a }

instance Functor (Reader r) where
  fmap f (Reader g) = Reader (f . g)

instance Applicative (Reader r) where
  pure = Reader . const
  Reader f <*> Reader g = Reader (\r -> f r (g r))

instance Monad (Reader r) where
  return = pure
  Reader f >>= g = Reader (\r -> runReader (g (f r)) r)

-- Reader操作
ask :: Reader r r
ask = Reader id

local :: (r -> r) -> Reader r a -> Reader r a
local f (Reader g) = Reader (g . f)
```

### Writer单子

```haskell
-- Writer单子
newtype Writer w a = Writer { runWriter :: (a, w) }

instance Monoid w => Functor (Writer w) where
  fmap f (Writer (a, w)) = Writer (f a, w)

instance Monoid w => Applicative (Writer w) where
  pure a = Writer (a, mempty)
  Writer (f, w1) <*> Writer (a, w2) = Writer (f a, w1 `mappend` w2)

instance Monoid w => Monad (Writer w) where
  return = pure
  Writer (a, w1) >>= f = 
    let Writer (b, w2) = f a
    in Writer (b, w1 `mappend` w2)

-- Writer操作
tell :: Monoid w => w -> Writer w ()
tell w = Writer ((), w)

listen :: Monoid w => Writer w a -> Writer w (a, w)
listen (Writer (a, w)) = Writer ((a, w), w)
```

## 范畴论与类型系统

### 积类型 (Product)

```haskell
-- 积类型
data Product a b = Product a b

-- 积的函子实例
instance Functor (Product a) where
  fmap f (Product a b) = Product a (f b)

-- 积的应用函子实例
instance Monoid a => Applicative (Product a) where
  pure b = Product mempty b
  Product a1 f <*> Product a2 b = Product (a1 `mappend` a2) (f b)
```

### 余积类型 (Coproduct)

```haskell
-- 余积类型（Either）
-- Either a b 是 a 和 b 的余积

-- 余积的函子实例
instance Functor (Either a) where
  fmap _ (Left e) = Left e
  fmap f (Right b) = Right (f b)
```

### 指数类型 (Exponential)

```haskell
-- 指数类型（函数类型）
-- a -> b 是 b^a

-- 指数函子
newtype Exp a b = Exp { runExp :: a -> b }

instance Functor (Exp a) where
  fmap f (Exp g) = Exp (f . g)

instance Applicative (Exp a) where
  pure = Exp . const
  Exp f <*> Exp g = Exp (\a -> f a (g a))
```

## 高级主题

### 单子变换器

```haskell
-- 单子变换器
class MonadTrans t where
  lift :: Monad m => m a -> t m a

-- MaybeT变换器
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Functor (MaybeT m) where
  fmap f (MaybeT m) = MaybeT (fmap (fmap f) m)

instance Monad m => Applicative (MaybeT m) where
  pure = MaybeT . return . Just
  MaybeT f <*> MaybeT x = MaybeT $ do
    mf <- f
    mx <- x
    return (mf <*> mx)

instance Monad m => Monad (MaybeT m) where
  return = pure
  MaybeT m >>= f = MaybeT $ do
    ma <- m
    case ma of
      Nothing -> return Nothing
      Just a -> runMaybeT (f a)

instance MonadTrans MaybeT where
  lift = MaybeT . fmap Just
```

### 自由单子变换器

```haskell
-- 自由单子变换器
data FreeT f m a = Pure a | Free (f (FreeT f m a)) | Lift (m (FreeT f m a))

instance (Functor f, Monad m) => Functor (FreeT f m) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free x) = Free (fmap (fmap f) x)
  fmap f (Lift m) = Lift (fmap (fmap f) m)

instance (Functor f, Monad m) => Monad (FreeT f m) where
  return = Pure
  Pure a >>= f = f a
  Free x >>= f = Free (fmap (>>= f) x)
  Lift m >>= f = Lift (m >>= (>>= f))
```

---

**相关链接**：

- [类型理论](./001-Programming-Language-Theory.md)
- [线性类型理论](./002-Linear-Type-Theory.md)
- [仿射类型理论](./003-Affine-Type-Theory.md)
