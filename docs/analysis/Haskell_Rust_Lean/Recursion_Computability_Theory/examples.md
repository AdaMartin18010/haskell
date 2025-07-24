# 12.5 典型例子 Examples of Recursion & Computability Theory #RecursionComputabilityTheory-12.5

## 12.5.1 斐波那契递归 Fibonacci Recursion #RecursionComputabilityTheory-12.5.1

### 中文

以斐波那契数列为例，展示递归定义与可计算性。

### English

Example: Fibonacci sequence as a demonstration of recursion and computability.

#### Haskell

```haskell
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)
```

#### Rust

```rust
fn fib(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fib(n-1) + fib(n-2),
    }
}
```

#### Lean

```lean
def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := fib n + fib (n+1)
```

## 12.5.2 停机问题 Halting Problem #RecursionComputabilityTheory-12.5.2

- Haskell：可表达不可终止递归（如无限递归函数）。
- Rust：需手动防止死循环，理论上可表达不可终止。
- Lean：可形式化不可判定性证明。

## 12.5.3 工程案例 Engineering Example #RecursionComputabilityTheory-12.5.3

- Haskell：递归函数与高阶函数广泛用于算法建模。
- Rust：trait递归与系统级递归实现。
- Lean：归纳递归与可计算性证明。

## 12.5.4 相关Tag

`# RecursionComputabilityTheory #RecursionComputabilityTheory-12 #RecursionComputabilityTheory-12.5 #RecursionComputabilityTheory-12.5.1 #RecursionComputabilityTheory-12.5.2 #RecursionComputabilityTheory-12.5.3`
