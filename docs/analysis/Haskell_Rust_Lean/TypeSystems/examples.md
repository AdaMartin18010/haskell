# 1.5 典型例子 Examples

Tag: #TypeSystems-1.5

## Haskell: GADT 限定表达式类型

```haskell
{-# LANGUAGE GADTs #-}
data Expr a where
  Lit  :: Int -> Expr Int
  Plus :: Expr Int -> Expr Int -> Expr Int
```

## Rust: 所有权与生命周期占位

```rust
fn takes_ownership(s: String) { /* ... */ }
```

## Lean: 依赖类型示意

```lean
def vec (α : Type) : nat → Type := λ n, list α -- placeholder
```
