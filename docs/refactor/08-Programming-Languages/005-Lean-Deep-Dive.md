# Lean深度解析

## 核心概念

### 依赖类型

```lean
-- 依赖类型：类型可以依赖于值
def Vector (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × Vector α n

-- 长度在类型中编码
def empty {α : Type} : Vector α 0 := ()
def cons {α : Type} {n : Nat} (x : α) (v : Vector α n) : Vector α (n + 1) := (x, v)
```

### 命题即类型

```lean
-- 命题即类型：证明就是程序
def Even : Nat → Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even n

-- 证明是构造性的
theorem zero_even : Even 0 := True.intro
theorem two_even : Even 2 := True.intro
```

### 同伦类型论

```lean
-- 类型等价
def Equiv (α β : Type) := (α → β) × (β → α) × (α → β → α) × (β → α → β)

-- 单值类型
def IsContr (α : Type) := Σ (center : α), ∀ (x : α), center = x
```

## 类型系统

### 宇宙层次

```lean
-- 宇宙层次
#check Type -- Type 1
#check Type 1 -- Type 2
#check Type 2 -- Type 3

-- 宇宙多态
def id {α : Type u} (x : α) : α := x
```

### 归纳类型

```lean
-- 自然数
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

-- 列表
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

### 递归函数

```lean
-- 模式匹配
def add : Nat → Nat → Nat
  | 0, n => n
  | succ m, n => succ (add m n)

-- 结构递归
def length {α : Type} : List α → Nat
  | List.nil => 0
  | List.cons _ xs => 1 + length xs
```

## 证明系统

### 策略语言

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ n ih => rw [Nat.add_succ, ih]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ n ih => rw [Nat.add_succ, Nat.succ_add, ih]
```

### 自动化

```lean
-- 自动证明
theorem simple_arithmetic : 2 + 2 = 4 := by simp

-- 决策过程
theorem linear_inequality : 3 * x + 2 > x + 5 := by linarith
```

## 数学形式化

### 集合论

```lean
-- 集合定义
def Set (α : Type) := α → Prop

-- 集合操作
def mem {α : Type} (x : α) (s : Set α) : Prop := s x
def subset {α : Type} (s t : Set α) : Prop := ∀ x, mem x s → mem x t
```

### 代数结构

```lean
-- 群的定义
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_inv : ∀ a, mul a (inv a) = one
```

### 拓扑学

```lean
-- 拓扑空间
class TopologicalSpace (X : Type) where
  open_sets : Set (Set X)
  empty_open : mem ∅ open_sets
  full_open : mem univ open_sets
  intersection_open : ∀ s t, mem s open_sets → mem t open_sets → mem (s ∩ t) open_sets
  union_open : ∀ S, (∀ s, mem s S → mem s open_sets) → mem (⋃₀ S) open_sets
```

## 程序验证

### 规范

```lean
-- 前置条件和后置条件
def sorted_insert (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: xs else y :: sorted_insert x ys

-- 验证插入保持有序
theorem sorted_insert_maintains_order (x : Nat) (xs : List Nat) :
  is_sorted xs → is_sorted (sorted_insert x xs) := by
  intro h
  induction xs with
  | nil => simp [sorted_insert, is_sorted]
  | cons y ys ih => 
    simp [sorted_insert]
    split
    · simp [is_sorted]
    · apply ih
```

### 终止性

```lean
-- 结构递归确保终止
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 证明终止性
theorem factorial_terminates (n : Nat) : factorial n ≠ 0 := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.mul_ne_zero]
```

## 应用场景

- **数学证明**: 形式化数学定理
- **程序验证**: 证明程序正确性
- **类型理论**: 研究类型系统
- **教育**: 数学和计算机科学教学

---

**相关链接**：

- [语言范式](./001-Language-Paradigms.md)
- [语言对比](./002-Language-Comparison.md)
