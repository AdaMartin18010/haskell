# 3.10 形式化证明与论证 Formal Proofs & Arguments #LinearTypeTheory-3.10

## 3.10.1 类型安全定理 Type Safety (Progress & Preservation)

- **中文**：类型安全由两部分组成：进展性（Progress）与保持性（Preservation）。在线性λ演算与含乘法/加法/指数(!/?)的线性类型系统中，我们强调环境的分裂与资源一次性使用约束。
- **English**: Type safety consists of Progress and Preservation. For linear lambda calculus with multiplicative/additive/exponential connectives, we highlight context splitting and one-time usage constraints.

### 进展性 Progress

非正式陈述（Informal): 若 `∅ ⊢ e : A`，则 `e` 要么为值，要么存在 `e'` 使得 `e → e'`。

```lean
-- Lean-style skeleton (pseudo, illustrating linear contexts Γ₁ ⊎ Γ₂)
theorem progress {e : Expr} {A : Ty} :
  (⊢ e : A) → (is_value e ∨ ∃ e', step e e') := by
  intro h
  induction h <;> try first | (exact Or.inl ?val) | (exact Or.inr ?step)
  -- Cases: var impossible in empty ctx; abs is value; app splits contexts; pairs; let-bindings; etc.
  admit
```

### 保持性 Preservation

非正式陈述：若 `Γ ⊢ e : A` 且 `e → e'`，则存在 `Γ'` 与之资源等价，使得 `Γ' ⊢ e' : A`（保持类型与资源平衡）。

```haskell
-- Haskell-like pseudo proof obligations
type Preservation = Context -> Expr -> Ty -> Expr -> Bool
preservation gamma e a e' =
  hasType gamma e a && stepsTo e e' ==> existsGamma' (\gamma' -> resourceEq gamma gamma' && hasType gamma' e' a)
```

要点（Key obligations）:

- **上下文分裂 Context Splitting**: 应用与张量引入/消解保持 `Γ = Γ₁ ⊎ Γ₂` 不重用资源。
- **Beta 约化 Beta-reduction**: `((λx.e) ⊸ v) → e[x:=v]`，同时消费 `v` 对应的线性资源。
- **Pair/Let 规约**: `let (x,y)=⟨v₁,v₂⟩ in e → e[x:=v₁,y:=v₂]`，资源逐一转移。
- **! 指数**: 通过 `!A` 显式解除线性约束，但需要规则侧条件保证复制只发生在 `!` 区域。

## 3.10.2 操作/指称语义 Operational & Denotational Semantics

### 操作语义（小步） Small-step Operational Semantics

```haskell
-- Illustration only
data Expr = Var Name | Lam Name Expr | App Expr Expr | Pair Expr Expr | LetPair Name Name Expr Expr | Bang Expr | Derelict Expr

data Step
  = Beta Expr Expr               -- (Lam x.e) v → e[x:=v]
  | AppL Expr Expr               -- e₁ → e₁' ⇒ e₁ e₂ → e₁' e₂
  | AppR Expr Expr               -- e₂ → e₂' under disjoint ctx
  | LetPairStep Expr             -- let (x,y)=⟨v₁,v₂⟩ in e → e[x:=v₁,y:=v₂]

step :: Expr -> Maybe Expr
step (App (Lam x e) v) = Just (subst x v e)
step (App e1 e2) = App <$> step e1 <*> pure e2 <|> App e1 <$> step e2
step (LetPair x y (Pair v1 v2) e) = Just (subst2 x v1 y v2 e)
step _ = Nothing
```

### 指称语义 Denotational Semantics

在对偶范畴/同态幺半群或线性逻辑的星范畴（*-autonomous category）中解释：

- 乘法 `⊗, ⅋` 与线性蕴含 `⊸` 的解释满足相应伴随结构。
- 指数 `!` 由共幺代数/幂余代数刻画，反映“可复制”的资源层。

```haskell
-- Sketch: categorical interpretation placeholders
data Obj
data Mor a b
(-*) :: Obj -> Obj -> Obj      -- tensor
(~>) :: Obj -> Obj -> Obj      -- linear implication as internal hom
bang :: Obj -> Obj             -- ! exponential
```

## 3.10.3 与 Haskell / Rust / Lean / Coq 对齐 Alignment

### Haskell (GHC ≥ 9.0, LinearTypes)

```haskell
{-# LANGUAGE LinearTypes #-}

useOnce :: a %1 -> (a, ())
useOnce x = (x, ())  -- x 必须被用且仅一次

pairConsume :: (a, b) %1 -> (a, b)
pairConsume (x, y) = (x, y)  -- 线性解构，两个资源都被使用
```

### Rust（所有权/借用）

```rust
fn consume_once(s: String) -> usize { s.len() } // move consumes s

fn main() {
    let s = String::from("hi");
    let n = consume_once(s);
    // println!("{}", s); // compile error: moved value
    println!("{}", n);
}
```

对应关系：Rust 的 move 语义与线性“消耗一次”一致；`&T`/`&mut T` 对应受控借用，相当于限制性指数/能力系统。

### Lean / Coq（证明骨架）

```lean
-- Lean: resource usage as linear contexts (schematic)
structure LCtx := (used : Finset Name)

inductive HasType : LCtx → Expr → Ty → Prop
| var : ... → HasType Γ (Var x) A
| lam : ... → HasType Γ (Lam x e) (A ⊸ B)
| app : ... → HasType (Γ₁ ⊎ Γ₂) (App e₁ e₂) B

theorem preservation : HasType Γ e A → step e e' → ∃ Γ', resourceEq Γ Γ' ∧ HasType Γ' e' A := by
  admit
```

```coq
(* Coq: sketch with linear contexts and progress/preservation statements *)
Theorem progress : forall e A, has_type empty e A -> value e \/ exists e', step e e'.
Proof. (* structured by induction on typing *) Admitted.

Theorem preservation : forall Γ e A e', has_type Γ e A -> step e e' -> exists Γ', res_eq Γ Γ' /\ has_type Γ' e' A.
Proof. (* cases on step; inversion on typing; context algebra *) Admitted.
```

## 3.10.4 典型引理与上下文代数 Lemmas & Context Algebra

- **拆分引理 Splitting Lemma**: 若 `Γ ⊢ e₁ : A ⊸ B` 与 `Δ ⊢ e₂ : A`，且 `Γ ⊥ Δ`，则 `Γ ⊎ Δ ⊢ e₁ e₂ : B`。
- **替换引理 Substitution**: 线性替换要求被替换变量恰好一次出现；指数区允许复制但需通过 `!` 引入/解除。
- **弱化/收缩限制 Structural rules**: 仅在 `!Γ` 中允许弱化与收缩，线性区不允许。

## 3.10.5 课程与行业案例对标 Courses & Industry Alignment

- **课程对齐 Courses**:
  - MIT 6.821/6.822, CMU 15-312/814, Oxford Categorical/Linear Logic courses：引入 Progress/Preservation 的线性变体，作业包含线性 λ 演算小步语义推导与证明。
  - Chalmers/Edinburgh Type Theory courses：将线性类型与资源语义、会话类型并行讲授。

- **行业案例 Industry**:
  - RustBelt（Jung et al., JACM 2021）：对 Rust 所有权/借用的语义与安全性进行机械化验证。
  - GHC LinearTypes（Peyton Jones 等）：提供一次性资源 API 设计（如文件句柄、FFI 缓冲区、安全 IO pipeline）。
  - 金融/网络/嵌入式：零拷贝缓冲、连接生命周期、DMA/Pin 内存管理，线性类型约束减少资源泄漏与数据竞态。

参考模板：参见 [`course_case_alignment_template.md`](../course_case_alignment_template.md)

## 3.10.6 交叉引用 Cross References

- [仿射类型理论 Affine Type Theory](../AffineTypeTheory/README.md)
- [定理与证明 Theorems & Proofs](../Theorems_Proofs/README.md)
- [类型系统 Type Systems](../TypeSystems/README.md)
