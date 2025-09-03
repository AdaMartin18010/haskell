# 4.10 形式化证明与论证 Formal Proofs & Arguments #AffineTypeTheory-4.10

## 4.10.1 类型安全定理 Type Safety (Progress & Preservation)

- **中文**：仿射类型允许“至多一次”使用，因此进展性与保持性需要结合弱化（Weakening）但禁止收缩（Contraction）。
- **English**: Affine types allow at-most-once usage, so Progress and Preservation combine Weakening while forbidding Contraction.

### 进展性 Progress

```lean
-- Skeleton: empty context implies value or step
theorem progress {e : Expr} {A : Ty} :
  (⊢ e : A) → (is_value e ∨ ∃ e', step e e') := by
  intro h; induction h <;> try admit
```

### 保持性 Preservation（带弱化）

```haskell
-- Haskell-like: preservation with affine context
preservation :: Ctx -> Expr -> Ty -> Expr -> Bool
preservation gamma e a e' =
  hasType gamma e a && stepsTo e e' ==>
    existsGamma' (\gamma' -> affineResLe gamma' gamma && hasType gamma' e' a)
-- affineResLe 表示 "资源不增加，可丢弃"
```

要点：

- **弱化 Weakening**: 允许丢弃未使用资源；证明中需展示类型派生能在超集环境中重放。
- **禁止收缩 No Contraction**: 不允许复制线性/仿射资源；仅 `!`/能力系统中受控复制。
- **应用/对/let**: 维持上下文的“至多一次”合并，不重复消耗同一资源。

## 4.10.2 操作/指称语义 Operational & Denotational

### 操作语义（带 discard）

```haskell
data Expr = Var Name | Lam Name Expr | App Expr Expr | Pair Expr Expr | LetPair Name Name Expr Expr | Discard Expr

step :: Expr -> Maybe Expr
step (App (Lam x e) v) = Just (subst x v e)
step (LetPair x y (Pair v1 v2) e) = Just (subst2 x v1 y v2 e)
step (Discard v) | isValue v = Just UnitExpr -- 丢弃已用/未用资源
step _ = Nothing
```

### 指称语义（带弱化的指数层）

- 在半笛卡尔结构或具弱化幺余代数的指数层解释 `?A`/`!A`，体现可丢弃但不可复制（或受限复制）。

## 4.10.3 与 Haskell / Rust / Lean / Coq 对齐

### Rust（move 即“至多一次”）

```rust
fn consume_once(s: String) -> usize { s.len() }

fn main() {
    let s = String::from("hi");
    let _n = consume_once(s);
    // consume_once(s); // error: moved value
}
```

### Haskell（Affine 风格占位）

```haskell
{-# LANGUAGE LinearTypes #-}

discardOrUse :: a %1 -> ()
discardOrUse _ = ()  -- 仿射允许丢弃
```

### Lean/Coq（骨架）

```lean
theorem weakening_affine : Γ ⊢ e : A → (Γ ∪ Δ) ⊢ e : A := by admit
```

```coq
Theorem preservation_affine : forall Γ e A e', has_type Γ e A -> step e e' -> exists Γ', le_affine Γ' Γ /\ has_type Γ' e' A.
Proof. Admitted.
```

## 4.10.4 课程与行业案例对标 Courses & Industry Alignment

- **课程**:
  - CMU 15-312/814, MIT 6.821/6.822：线性/仿射资源语义与弱化规则；课程作业含 progress/preservation 推导。
  - Rust 大学课程与“RustBelt”研讨：所有权、借用检查与仿射/线性类型关系。

- **行业**:
  - RustBelt（JACM 2021）与借用检查器实现安全保证。
  - 资源敏感系统：文件句柄、网络连接、GPU/IO 缓冲的“至多一次”释放/使用策略。

参考模板：参见 [`course_case_alignment_template.md`](../course_case_alignment_template.md)

## 4.10.5 交叉引用 Cross References

- [线性类型理论 Linear Type Theory](../LinearTypeTheory/README.md)
- [定理与证明 Theorems & Proofs](../Theorems_Proofs/README.md)
