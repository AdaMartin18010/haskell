# Lean 数据流（Data Flow）

## 1. 不可变数据结构

- Lean 以不可变数据结构为主，所有数据流通过函数参数传递。

```lean
structure Point where
  x : Float
  y : Float

def move (p : Point) (dx dy : Float) : Point :=
  { p with x := p.x + dx, y := p.y + dy }
```

## 2. 依赖类型数据流

- 支持类型依赖值的数据结构，如向量（Vector α n）。

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons {n : Nat} : α → Vector α n → Vector α (n+1)

def append {α : Type u} {n m : Nat} (v1 : Vector α n) (v2 : Vector α m) : Vector α (n + m) :=
  match v1 with
  | Vector.nil      => v2
  | Vector.cons x t => Vector.cons x (append t v2)
```

## 3. 归纳与共递归数据流

- Lean 支持有限（归纳）和无限（共递归）数据结构。

```lean
inductive Stream (α : Type)
  | cons : α → Thunk (Stream α) → Stream α
```

## 4. 数据流建模

- 通过归纳类型、递归函数、不可变结构建模数据流。

```lean
def sumVector {α : Type u} [Add α] : {n : Nat} → Vector α n → α
  | 0,   Vector.nil      => 0
  | n+1, Vector.cons x t => x + sumVector t
```

---

## 5. 数据流特性小结

- 不可变数据结构、依赖类型数据流
- 归纳/共递归数据结构
- 递归与模式匹配建模数据流

[下一节：Lean 与 Haskell/Rust 对比](06-Comparison.md)
