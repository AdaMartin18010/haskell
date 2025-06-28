# 模型检查

## 概述

模型检查是一种自动验证有限状态系统是否满足时序逻辑规范的技术。

## 基本概念

### 状态机

```haskell
-- 简单的状态机
data State = Idle | Working | Done
data Event = Start | Complete | Reset

transition :: State -> Event -> Maybe State
transition Idle Start = Just Working
transition Working Complete = Just Done
transition Done Reset = Just Idle
transition _ _ = Nothing
```

### 时序逻辑

```haskell
-- 线性时序逻辑（LTL）
-- G p : 总是p为真
-- F p : 最终p为真
-- X p : 下一个时刻p为真
-- p U q : p为真直到q为真

-- 验证属性
alwaysEventually :: State -> Bool
alwaysEventually state = case state of
  Idle -> True
  Working -> True
  Done -> True
```

## 工具

- **Spin**: 并发系统验证
- **NuSMV**: 符号模型检查
- **UPPAAL**: 实时系统验证

## 应用

- 协议验证
- 硬件验证
- 软件系统验证

---

**相关链接**：

- [形式化验证](./001-Formal-Verification.md)
- [定理证明](./003-Theorem-Proving.md)
