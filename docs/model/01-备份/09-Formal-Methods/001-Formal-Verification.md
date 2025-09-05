# 形式化验证

## 概述

形式化验证使用数学方法证明程序满足其规范。

## 验证方法

### 模型检查

```haskell
-- 状态机验证
data State = Idle | Working | Done
data Event = Start | Complete

transition :: State -> Event -> Maybe State
transition Idle Start = Just Working
transition Working Complete = Just Done
transition _ _ = Nothing
```

### 定理证明

```haskell
-- QuickCheck属性测试
prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs
```

### 类型级验证

```haskell
-- 依赖类型
data Vec (n :: Nat) a where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (n + 1) a
```

## 工具

- **Haskell**: QuickCheck, Liquid Haskell
- **Rust**: MIRAI, Kani, Prusti
- **Lean**: 定理证明器

## 应用场景

- 金融系统验证
- 安全协议验证
- 并发系统验证

---

**相关链接**：

- [模型检查](./002-Model-Checking.md)
- [定理证明](./003-Theorem-Proving.md)
