# 应用函子模式 (Applicative Patterns)

## 概述

应用函子（Applicative Functor）是 Haskell 中介于 Functor 和 Monad 之间的重要抽象，支持独立效应的组合和多参数函数的应用。它广泛用于解析、验证、配置等场景。

## 1. 形式化定义

### 定义 5.6.1: 应用函子

> 一个类型构造器 $F$ 是应用函子，当且仅当存在操作：
>
> - $\text{pure}: A \to F A$
> - $\langle*\rangle: F (A \to B) \to F A \to F B$
>
> 满足如下定律：
>
> 1. 恒等律：$\text{pure}\ id \langle*\rangle v = v$
> 2. 组合律：$\text{pure}\ (\circ) \langle*\rangle u \langle*\rangle v \langle*\rangle w = u \langle*\rangle (v \langle*\rangle w)$
> 3. 同态律：$\text{pure}\ f \langle*\rangle \text{pure}\ x = \text{pure}\ (f\ x)$
> 4. 交换律：$u \langle*\rangle \text{pure}\ y = \text{pure}\ (\lambda f. f\ y) \langle*\rangle u$

### Haskell 类型类

```haskell
class Functor f => Applicative f where
  pure  :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
```

## 2. 数学模型

- $\text{Applicative}~F = (F, \text{pure}, \langle*\rangle)$
- $\langle*\rangle$ 可视为范畴论中的函子提升

## 3. 典型实例

### Maybe

```haskell
instance Applicative Maybe where
  pure = Just
  Nothing <*> _ = Nothing
  Just f <*> x = fmap f x
```

### List

```haskell
instance Applicative [] where
  pure x = [x]
  fs <*> xs = [f x | f <- fs, x <- xs]
```

### Either

```haskell
instance Applicative (Either e) where
  pure = Right
  Left e <*> _ = Left e
  Right f <*> x = fmap f x
```

## 4. 组合与应用

### 多参数函数应用

```haskell
pure (+) <*> Just 1 <*> Just 2  -- Just 3
liftA2 (,) (Just 1) (Just 2)    -- Just (1,2)
```

### 验证模式

```haskell
validate :: String -> Either String String
validate s | null s    = Left "empty"
           | otherwise = Right s

validateUser :: String -> String -> Either String (String, String)
validateUser n e = (,) <$> validate n <*> validate e
```

### 解析器模式

```haskell
data Parser a = Parser { runParser :: String -> Maybe (a, String) }

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> do (a, s') <- p s; return (f a, s')
instance Applicative Parser where
  pure a = Parser $ \s -> Just (a, s)
  Parser pf <*> Parser pa = Parser $ \s -> do (f, s1) <- pf s; (a, s2) <- pa s1; return (f a, s2)
```

## 5. 最佳实践

1. 优先使用 Applicative 组合独立效应，只有需要依赖前值时才用 Monad。
2. 利用 `liftA2`、`liftA3` 简化多参数函数应用。
3. 解析、验证、配置等场景优先考虑 Applicative。

## 6. 相关链接

- [函数式设计模式](./01-Functional-Design-Patterns.md)
- [类型类模式](./02-Type-Class-Patterns.md)
- [单子变换器模式](./03-Monad-Transformer-Patterns.md)
- [透镜模式](./04-Lens-Patterns.md)
- [自由单子模式](./05-Free-Monad-Patterns.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
