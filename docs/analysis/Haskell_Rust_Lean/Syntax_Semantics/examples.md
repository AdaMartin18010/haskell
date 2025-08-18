# 1.5 典型例子 Examples

Tag: #SyntaxSemantics-1.5

## Haskell: 简单表达式 AST 与小步语义

```haskell
{-# LANGUAGE GADTs #-}
data Expr where
  Lit :: Int -> Expr
  Add :: Expr -> Expr -> Expr

data Step = Val Int | Red Expr

step :: Expr -> Step
step (Lit n)     = Val n
step (Add (Lit x) (Lit y)) = Val (x+y)
step (Add x y)   = Red (Add' x y) -- 占位，示意
```

## Rust: 表达式求值占位

```rust
enum Expr { Lit(i32), Add(Box<Expr>, Box<Expr>) }
```

## Lean: 语法与归约占位

```lean
inductive expr | lit : nat → expr | add : expr → expr → expr
```
