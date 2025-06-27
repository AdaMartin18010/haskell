# Lean 语言语法（Syntax）

## 1. 基本语法结构

Lean 兼具编程语言与定理证明助手的语法特性，支持依赖类型、归纳类型、结构体、模式匹配、元编程等。

### 1.1 函数定义

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n
```

### 1.2 结构体定义

```lean
structure Point where
  x : Float
  y : Float
  deriving Repr
```

### 1.3 归纳类型（Inductive Types）

```lean
inductive List (α : Type u)
  | nil : List α
  | cons : α → List α → List α
```

### 1.4 模式匹配

```lean
def headOption {α : Type u} : List α → Option α
  | List.nil      => none
  | List.cons x _ => some x
```

### 1.5 定理声明与证明

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero   => rfl
  | succ n ih => simp [Nat.add_succ, ih]
```

### 1.6 隐式参数与类型注解

```lean
def add {α : Type u} [Add α] (a b : α) : α := a + b
```

### 1.7 宇宙多态

```lean
def id {u} {α : Type u} (x : α) : α := x
```

### 1.8 元编程与宏

```lean
macro "inc!" n:term : term => `(Nat.succ $n)
```

---

## 2. 语法特性小结

- 支持依赖类型、归纳类型、结构体、模式匹配
- 定理声明与 tactic 证明块
- 隐式参数、类型注解、宇宙多态
- 内置元编程与宏系统

[下一节：Lean 语义模型](02-Semantics.md)
