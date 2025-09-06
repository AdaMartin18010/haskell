# 1.5 典型例子 Examples

Tag: #PracticalValue-1.5

## Haskell：类型安全收益示例

```haskell
-- 编译期捕获错误，避免运行时异常
data SafeList a = Nil | Cons a (SafeList a)
-- 类型系统确保操作安全
```

## Rust：内存安全收益示例

```rust
// 编译期防止数据竞争
let mut data = vec![1, 2, 3];
// 所有权系统确保线程安全
```

## Lean：形式化验证收益示例

```lean
-- 机器检验的算法正确性
theorem algorithm_correct : ∀ n, algorithm n = expected n := sorry
```
