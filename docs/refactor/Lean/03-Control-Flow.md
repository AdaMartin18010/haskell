# Lean 控制流（Control Flow）

## 1. 条件分支

Lean 支持 if-then-else 表达式：

```lean
def abs (n : Int) : Int :=
  if n < 0 then -n else n
```

## 2. 模式匹配（match）

```lean
def sign (n : Int) : Int :=
  match n with
  | 0   => 0
  | n   => if n > 0 then 1 else -1
```

## 3. 递归与循环

Lean 主要通过递归实现循环：

```lean
def sumTo (n : Nat) : Nat :=
  match n with
  | 0   => 0
  | n+1 => (n+1) + sumTo n
```

## 4. do 记法与 Monad

Lean 4 支持 do 记法用于 IO 和 monad 操作：

```lean
def printList (xs : List Int) : IO Unit := do
  for x in xs do
    IO.println x
```

## 5. tactic 控制流（证明时）

- tactic 块支持分支、归纳、反证、case 分析等

```lean
theorem not_eq_zero_succ (n : Nat) : n.succ ≠ 0 := by
  intro h
  cases h
```

---

## 6. 控制流特性小结

- if-then-else、match、递归为主
- do 记法用于 IO/monad
- tactic 块用于证明时的控制流

[下一节：Lean 执行流](04-Execution-Flow.md)
