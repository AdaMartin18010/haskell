# 1.5 典型例子 Examples

Tag: #SemanticModels-1.5

## 操作语义示例（Haskell 伪） Operational Semantics (Haskell pseudo)

```haskell
{-# LANGUAGE GADTs #-}
data Expr where
  Lit :: Int -> Expr
  Add :: Expr -> Expr -> Expr

data Step = Val Int | Red Expr
step :: Expr -> Step
step (Lit n) = Val n
step (Add (Lit x) (Lit y)) = Val (x+y)
step e = Red e -- 占位示意
```

## 指称语义示例（Lean 伪） Denotational Semantics (Lean pseudo)

```lean
def denote : expr → nat := sorry -- placeholder
```

## 抽象解释占位 Abstract Interpretation (Rust pseudo)

```rust
// lattice/transfer placeholders
```
