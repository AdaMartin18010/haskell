# Lean实现

## 核心特性

### 依赖类型

```lean
def Vector (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => α × Vector α n

def empty {α : Type} : Vector α 0 := ()
def cons {α : Type} {n : Nat} (x : α) (v : Vector α n) : Vector α (n + 1) := (x, v)
```

### 命题即类型

```lean
def Even : Nat → Prop
  | 0 => True
  | 1 => False
  | n + 2 => Even n

theorem zero_even : Even 0 := True.intro
theorem two_even : Even 2 := True.intro
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
theorem simple_arithmetic : 2 + 2 = 4 := by simp

theorem linear_inequality : 3 * x + 2 > x + 5 := by linarith
```

## 数学形式化

### 集合论

```lean
def Set (α : Type) := α → Prop

def mem {α : Type} (x : α) (s : Set α) : Prop := s x
def subset {α : Type} (s t : Set α) : Prop := ∀ x, mem x s → mem x t
```

### 代数结构

```lean
class Group (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  mul_inv : ∀ a, mul a (inv a) = one
```

## 工具

- **Lean 4**: 定理证明器
- **Lake**: 构建系统
- **Mathlib**: 数学库

---

**相关链接**：

- [Haskell实现](./001-Haskell-Implementation.md)
- [Rust实现](./002-Rust-Implementation.md)
