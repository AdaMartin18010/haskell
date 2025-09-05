# Lean 执行流（Execution Flow）

## 1. 求值策略

- Lean 4 采用严格（eager）求值，表达式自左向右依次求值。
- 证明过程中项的规约（reduction）即为"执行"。

```lean
def double (n : Nat) := 2 * n
#eval double 21  -- 计算结果为42
```

## 2. 证明规约

- tactic 块中的每一步都对应项的规约和状态变换。
- 归纳、case 分析、反证等 tactic 控制证明流。

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.add_succ, ih]
```

## 3. IO/Effect 机制

- Lean 4 支持 IO/EIO 类型封装副作用。
- do 记法用于顺序化 IO 操作。

```lean
def greet : IO Unit := do
  IO.println "Hello, Lean!"
```

## 4. 执行流建模

- 通过递归、模式匹配、do 记法建模执行流。
- 证明流与程序流可统一建模。

```lean
def processList (xs : List Int) : IO Unit := do
  for x in xs do
    if x > 0 then IO.println s!"Positive: {x}"
    else IO.println s!"Non-positive: {x}"
```

---

## 5. 执行流特性小结

- 严格求值、项规约
- tactic 证明流与程序流统一
- IO/EIO 封装副作用
- do 记法顺序化执行

[下一节：Lean 数据流](05-Data-Flow.md)
