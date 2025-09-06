# 10.5 典型例子 Examples of Automata Theory #AutomataTheory-10.5

## 10.5.1 有限自动机识别二进制偶数 Finite Automaton for Even Binary Numbers #AutomataTheory-10.5.1

### 中文

以有限自动机识别二进制偶数为例，展示自动机的状态转移。

### English

Example: Finite automaton recognizing even binary numbers, demonstrating state transitions.

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

## 10.5.2 工程案例 Engineering Example #AutomataTheory-10.5.2

- Haskell：自动机库实现协议分析。
- Rust：状态机库实现控制系统。
- Lean：形式化自动机与模型检测。

## 10.5.3 相关Tag

`# AutomataTheory #AutomataTheory-10 #AutomataTheory-10.5 #AutomataTheory-10.5.1 #AutomataTheory-10.5.2`
