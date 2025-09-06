# 9.5 典型例子 Examples of Formal Language Theory #FormalLanguageTheory-9.5

## 9.5.1 正则文法与有限自动机 Regular Grammar & Finite Automaton #FormalLanguageTheory-9.5.1

### 中文

以正则文法生成二进制偶数串为例，展示文法与自动机的等价性。

### English

Example: Regular grammar generating binary strings representing even numbers, demonstrating equivalence with finite automata.

#### Haskell

```haskell
data State = Even | Odd
accepts :: State -> [Int] -> Bool
accepts Even [] = True
accepts Odd  [] = False
accepts Even (0:xs) = accepts Even xs
accepts Even (1:xs) = accepts Odd xs
accepts Odd  (0:xs) = accepts Odd xs
accepts Odd  (1:xs) = accepts Even xs
```

#### Rust

```rust
enum State { Even, Odd }
fn accepts(state: State, input: &[u8]) -> bool {
    match (state, input) {
        (State::Even, []) => true,
        (State::Odd,  []) => false,
        (State::Even, [0, rest @ ..]) => accepts(State::Even, rest),
        (State::Even, [1, rest @ ..]) => accepts(State::Odd, rest),
        (State::Odd,  [0, rest @ ..]) => accepts(State::Odd, rest),
        (State::Odd,  [1, rest @ ..]) => accepts(State::Even, rest),
        _ => false
    }
}
```

#### Lean

```lean
inductive state | even | odd
open state

def accepts : state → list ℕ → bool
| even [] := tt
| odd  [] := ff
| even (0::xs) := accepts even xs
| even (1::xs) := accepts odd xs
| odd  (0::xs) := accepts odd xs
| odd  (1::xs) := accepts even xs
```

## 9.5.2 工程案例 Engineering Example #FormalLanguageTheory-9.5.2

- Haskell：解析器组合子实现DSL。
- Rust：状态机库实现协议解析。
- Lean：形式化文法与自动机证明。

## 9.5.3 相关Tag

`# FormalLanguageTheory #FormalLanguageTheory-9 #FormalLanguageTheory-9.5 #FormalLanguageTheory-9.5.1 #FormalLanguageTheory-9.5.2`
