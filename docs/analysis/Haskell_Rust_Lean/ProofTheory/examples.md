# 7.5 典型例子 Examples of Proof Theory #ProofTheory-7.5

## 7.5.1 归纳证明 Inductive Proof #ProofTheory-7.5.1

### 中文

以自然数加法的交换律为例，证明 n + m = m + n。

### English

Example: Prove the commutativity of addition for natural numbers, n + m = m + n.

#### Haskell

```haskell
-- 归纳证明思想用类型级递归表达
plus :: Nat -> Nat -> Nat
plus Z     n = n
plus (S m) n = S (plus m n)
-- 交换律可用QuickCheck/证明工具辅助验证
```

#### Rust

```rust
// 归纳结构用trait递归模拟
trait Nat {}
struct Z;
struct S<N: Nat>(N);
// 交换律可用proptest等工具辅助测试
```

#### Lean

```lean
-- 形式化归纳证明
lemma add_comm (m n : ℕ) : m + n = n + m :=
  nat.add_comm m n
```

## 7.5.2 证明树 Proof Tree #ProofTheory-7.5.2

- Haskell：GADT表达推理树结构
- Rust：枚举类型+trait表达推理分支
- Lean：内建推理树与战术系统

## 7.5.3 工程案例 Engineering Example #ProofTheory-7.5.3

- Haskell：liquidHaskell用于函数属性证明
- Rust：类型系统保证内存安全
- Lean：形式化数学定理证明

## 7.5.4 相关Tag

`# ProofTheory #ProofTheory-7 #ProofTheory-7.5 #ProofTheory-7.5.1 #ProofTheory-7.5.2 #ProofTheory-7.5.3`
