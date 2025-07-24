# 9.8 形式化证明 Formal Proofs #FormalLanguageTheory-9.8

## 9.8.1 核心定理 Core Theorems #FormalLanguageTheory-9.8.1

- 泵引理（Pumping Lemma）
- Chomsky层级定理
- 正则文法与有限自动机等价定理
- 上下文无关文法与下推自动机等价定理

## 9.8.2 典型证明 Typical Proofs #FormalLanguageTheory-9.8.2

### 中文

以泵引理为例：

- 对于任意足够长的正则语言串，可分为xyz，满足|xy|≤p, |y|>0, 对任意k≥0, x(y^k)z仍在语言中。
- 证明思路：利用有限自动机的状态数，构造循环。

### English

Example: Pumping Lemma:

- For any sufficiently long string in a regular language, it can be divided into xyz, with |xy|≤p, |y|>0, and for any k≥0, x(y^k)z is still in the language.
- Proof idea: Use the number of states in a finite automaton to construct a loop.

## 9.8.3 三语言实现 Proofs in Haskell/Rust/Lean #FormalLanguageTheory-9.8.3

### Haskell

```haskell
-- 用类型和递归表达有限自动机
-- 伪代码，实际可用ADT和递归函数实现
```

### Rust

```rust
// 用enum和trait表达有限自动机
// 伪代码，实际可用trait对象和状态机库实现
```

### Lean

```lean
-- 形式化有限自动机与正则文法等价证明（Lean伪代码）
theorem regular_automaton_equiv : ∀ L, regular_language L ↔ ∃ M, finite_automaton M ∧ accepts M = L :=
by admit -- 详细证明略
```

## 9.8.4 相关Tag

`# FormalLanguageTheory #FormalLanguageTheory-9 #FormalLanguageTheory-9.8 #FormalLanguageTheory-9.8.1 #FormalLanguageTheory-9.8.2 #FormalLanguageTheory-9.8.3`
