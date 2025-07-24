# 11.5 典型例子 Examples of System Theory #SystemTheory-11.5

## 11.5.1 反馈控制系统 Feedback Control System #SystemTheory-11.5.1

### 中文

以简单的反馈控制系统为例，展示系统的状态转移与反馈。

### English

Example: Simple feedback control system, demonstrating state transitions and feedback.

#### Haskell

```haskell
data System = System { state :: Int, input :: Int }
update :: System -> Int -> System
update sys u = sys { state = state sys + u }
feedback :: System -> Int
feedback sys = - state sys
```

#### Rust

```rust
struct System { state: i32, input: i32 }
impl System {
    fn update(&mut self, u: i32) {
        self.state += u;
    }
    fn feedback(&self) -> i32 {
        -self.state
    }
}
```

#### Lean

```lean
structure system := (state : ℤ) (input : ℤ)
def update (sys : system) (u : ℤ) : system := { sys with state := sys.state + u }
def feedback (sys : system) : ℤ := - sys.state
```

## 11.5.2 工程案例 Engineering Example #SystemTheory-11.5.2

- Haskell：函数式建模反馈控制系统。
- Rust：嵌入式协议栈与状态机控制。
- Lean：形式化系统建模与反馈证明。

## 11.5.3 相关Tag

`# SystemTheory #SystemTheory-11 #SystemTheory-11.5 #SystemTheory-11.5.1 #SystemTheory-11.5.2`
