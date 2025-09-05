# 定理证明

## 概述

定理证明是使用形式化逻辑系统证明数学定理或程序正确性的技术。

## 证明系统

### 在Haskell中

```haskell
-- QuickCheck属性测试
import Test.QuickCheck

prop_reverse :: [Int] -> Bool
prop_reverse xs = reverse (reverse xs) == xs

prop_sort_length :: [Int] -> Bool
prop_sort_length xs = length (sort xs) == length xs
```

### 在Lean中

```lean
-- 形式化证明
theorem reverse_reverse (xs : List α) : reverse (reverse xs) = xs := by
  induction xs with
  | nil => rw [reverse_nil]
  | cons x xs ih => rw [reverse_cons, reverse_cons, ih]

theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ n ih => rw [Nat.add_succ, ih]
```

## 证明策略

- **归纳法**: 数学归纳
- **重写**: 等式重写
- **自动化**: 自动证明
- **决策过程**: 线性算术等

## 工具

- **Coq**: 交互式定理证明器
- **Isabelle**: 通用证明助手
- **Lean**: 现代定理证明器
- **Agda**: 依赖类型编程语言

---

**相关链接**：

- [形式化验证](./001-Formal-Verification.md)
- [模型检查](./002-Model-Checking.md)
