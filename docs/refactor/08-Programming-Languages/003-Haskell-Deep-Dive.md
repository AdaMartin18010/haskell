# Haskell深度解析

## 核心概念

### 纯函数
```haskell
add :: Num a => a -> a -> a
add x y = x + y
```

### 类型系统
```haskell
-- 代数数据类型
data Maybe a = Nothing | Just a

-- 类型类
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b
```

### 惰性求值
```haskell
naturals :: [Integer]
naturals = [0..]

take 5 naturals -- [0,1,2,3,4]
```

## 函数式特性

### 高阶函数
```haskell
map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs
```

### Monad系统
```haskell
-- Maybe Monad
safeDiv :: Double -> Double -> Maybe Double
safeDiv _ 0 = Nothing
safeDiv x y = Just (x / y)
```

## 并发编程

### STM
```haskell
import Control.Concurrent.STM

type Account = TVar Double

transfer :: Account -> Account -> Double -> STM ()
transfer from to amount = do
  fromBalance <- readTVar from
  when (fromBalance >= amount) $ do
    writeTVar from (fromBalance - amount)
    toBalance <- readTVar to
    writeTVar to (toBalance + amount)
```

## 应用场景

- **Web开发**: Yesod, Scotty
- **金融系统**: 纯函数计算
- **并发编程**: STM, 异步编程
- **编译器**: GHC本身

---

**相关链接**：
- [语言范式](./001-Language-Paradigms.md)
- [语言对比](./002-Language-Comparison.md) 