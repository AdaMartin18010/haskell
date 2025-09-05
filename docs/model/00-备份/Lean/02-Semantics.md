# Lean 语义模型（Semantics）

## 1. 命题即类型（Curry-Howard 同构）

Lean 采用命题即类型（Propositions as Types）原则：

- 逻辑命题被编码为类型
- 证明即为该类型的一个值

```lean
def Even (n : Nat) : Prop := ∃ k, n = 2 * k
theorem four_is_even : Even 4 := ⟨2, by simp⟩
```

## 2. 证明即程序

- 证明过程就是构造类型的值
- tactic 证明块用于交互式构造证明

```lean
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => simp [Nat.add_succ, ih]
```

## 3. 归纳与递归

- Lean 支持归纳类型和结构递归
- 所有递归都需保证终止性

```lean
inductive Tree (α : Type)
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

def size {α} : Tree α → Nat
  | Tree.leaf      => 0
  | Tree.node _ l r => 1 + size l + size r
```

## 4. 类型依赖值（依赖类型）

- 类型可以依赖于具体值
- 支持向量等依赖类型数据结构

```lean
inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons {n : Nat} : α → Vector α n → Vector α (n+1)
```

## 5. 宇宙层级（Universes）

- 通过 Type u 实现类型的类型，避免悖论

```lean
def id {u} {α : Type u} (x : α) : α := x
```

## 6. 可计算性与规约

- Lean 4 支持可提取的可执行代码
- 证明过程中的项规约即为"执行"

```lean
def double (n : Nat) := 2 * n
#eval double 21  -- 计算结果为42
```

---

## 7. 语义特性小结

- 命题即类型、证明即程序
- 归纳类型与结构递归
- 类型依赖值、宇宙层级
- 可计算性与项规约

[下一节：Lean 控制流](03-Control-Flow.md)
