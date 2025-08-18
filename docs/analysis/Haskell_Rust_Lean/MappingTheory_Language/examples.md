# 1.5 典型例子 Examples

Tag: #MappingTheoryLanguage-1.5

## Haskell：Monad 抽象到语言特性

```haskell
class Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
```

## Rust：所有权语义到API设计（占位）

```rust
fn take(v: Vec<i32>) { /* move */ }
```

## Lean：依赖类型到规范（占位）

```lean
def safe_head {α} : Π (n : nat), vector α (n+1) → α := sorry
```
