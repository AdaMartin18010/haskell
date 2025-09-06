# 13.5 典型例子 Examples of Cybernetics #Cybernetics-13.5

## 13.5.1 负反馈控制 Negative Feedback Control #Cybernetics-13.5.1

### 中文

以负反馈控制系统为例，展示系统的调节与稳定性。

### English

Example: Negative feedback control system, demonstrating regulation and stability.

#### Haskell

```haskell
data System = System { state :: Double, input :: Double }
update :: System -> Double -> System
update sys u = sys { state = state sys + u }
feedback :: System -> Double
feedback sys = -0.5 * state sys
```

#### Rust

```rust
struct System { state: f64, input: f64 }
impl System {
    fn update(&mut self, u: f64) {
        self.state += u;
    }
    fn feedback(&self) -> f64 {
        -0.5 * self.state
    }
}
```

#### Lean

```lean
structure system := (state : ℝ) (input : ℝ)
def update (sys : system) (u : ℝ) : system := { sys with state := sys.state + u }
def feedback (sys : system) : ℝ := -0.5 * sys.state
```

## 13.5.2 工程案例 Engineering Example #Cybernetics-13.5.2

- Haskell：函数式建模负反馈控制系统。
- Rust：嵌入式信号处理与反馈调节。
- Lean：形式化反馈系统与稳定性证明。

## 13.5.3 相关Tag

`# Cybernetics #Cybernetics-13 #Cybernetics-13.5 #Cybernetics-13.5.1 #Cybernetics-13.5.2`
