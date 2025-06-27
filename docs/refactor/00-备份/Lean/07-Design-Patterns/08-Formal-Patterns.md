# Lean 形式化设计模式

## 🎯 概述

形式化设计模式是Lean的核心特色，通过定理证明、形式化验证和数学规范实现程序正确性的数学保证。

## 🔍 定理证明模式

### 基础定理证明

```lean
-- 定理证明模式
namespace TheoremProving

-- 基础性质
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rw [Nat.zero_add]
  | succ n ih => 
    rw [Nat.succ_add]
    rw [ih]

theorem add_comm (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ b ih =>
    rw [Nat.add_succ, Nat.succ_add, ih]

-- 列表性质
theorem list_length_append {α : Type} (xs ys : List α) : 
  (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => rw [List.nil_append, List.length_nil, Nat.zero_add]
  | cons x xs ih =>
    rw [List.cons_append, List.length_cons, List.length_cons, ih]
    rw [Nat.succ_add]

-- 函数性质
theorem map_id {α : Type} (xs : List α) : List.map id xs = xs := by
  induction xs with
  | nil => rw [List.map_nil]
  | cons x xs ih =>
    rw [List.map_cons, ih]

end TheoremProving
```

### 高级定理证明

```lean
-- 高级定理证明
namespace AdvancedTheoremProving

-- 归纳定义
inductive Even : Nat → Prop
  | zero : Even 0
  | step : {n : Nat} → Even n → Even (n + 2)

inductive Odd : Nat → Prop
  | one : Odd 1
  | step : {n : Nat} → Odd n → Odd (n + 2)

-- 互斥性证明
theorem even_not_odd (n : Nat) : Even n → Odd n → False := by
  intro h_even h_odd
  induction h_even with
  | zero => 
    cases h_odd
  | step n h_even ih =>
    cases h_odd with
    | one => contradiction
    | step n h_odd =>
      apply ih h_odd

-- 完备性证明
theorem even_or_odd (n : Nat) : Even n ∨ Odd n := by
  induction n with
  | zero => left; constructor
  | succ n ih =>
    cases ih with
    | inl h_even => right; constructor; exact h_even
    | inr h_odd => left; constructor; exact h_odd

-- 函数正确性
def isSorted {α : Type} [LE α] : List α → Prop
  | [] => True
  | [x] => True
  | x :: y :: xs => x ≤ y ∧ isSorted (y :: xs)

theorem sorted_append {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] 
  (xs ys : List α) : isSorted xs → isSorted ys → 
  (∀ x y, x ∈ xs → y ∈ ys → x ≤ y) → isSorted (xs ++ ys) := by
  induction xs with
  | nil => intro _ h_ys _; exact h_ys
  | cons x xs ih =>
    intro h_xs h_ys h_bound
    cases xs with
    | nil => 
      rw [List.cons_nil_append]
      exact h_ys
    | cons y xs =>
      rw [List.cons_append]
      constructor
      · exact h_xs.left
      · apply ih
        · exact h_xs.right
        · exact h_ys
        · intro a b ha hb
          apply h_bound
          · exact List.mem_cons_of_mem x ha
          · exact hb

end AdvancedTheoremProving
```

## ✅ 形式化验证模式

### 程序规范

```lean
-- 形式化验证模式
namespace FormalVerification

-- 前置条件和后置条件
def sorted_insert {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] 
  (x : α) (xs : List α) : List α :=
  match xs with
  | [] => [x]
  | y :: ys => 
    if x ≤ y then x :: xs else y :: sorted_insert x ys

-- 规范
theorem sorted_insert_spec {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] 
  (x : α) (xs : List α) : 
  isSorted xs → isSorted (sorted_insert x xs) := by
  induction xs with
  | nil => 
    intro _; constructor
  | cons y ys ih =>
    intro h_sorted
    simp [sorted_insert]
    split
    · constructor
      · assumption
      · exact h_sorted
    · constructor
      · exact h_sorted.left
      · apply ih h_sorted.right

-- 长度保持
theorem sorted_insert_length {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] 
  (x : α) (xs : List α) : 
  (sorted_insert x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rw [sorted_insert, List.length_singleton]
  | cons y ys ih =>
    simp [sorted_insert]
    split
    · rw [List.length_cons, Nat.succ_add]
    · rw [List.length_cons, ih, Nat.succ_add]

end FormalVerification
```

### 状态机验证

```lean
-- 状态机验证
namespace StateMachineVerification

-- 状态机定义
inductive State : Type
  | Idle : State
  | Running : State
  | Paused : State
  | Stopped : State

inductive Event : Type
  | Start : Event
  | Pause : Event
  | Resume : Event
  | Stop : Event

-- 状态转换
inductive Transition : State → Event → State → Prop
  | StartIdle : Transition State.Idle Event.Start State.Running
  | PauseRunning : Transition State.Running Event.Pause State.Paused
  | ResumePaused : Transition State.Paused Event.Resume State.Running
  | StopAny : {s : State} → Transition s Event.Stop State.Stopped

-- 状态机实现
def stateMachine (s : State) (e : Event) : Option State :=
  match s, e with
  | State.Idle, Event.Start => some State.Running
  | State.Running, Event.Pause => some State.Paused
  | State.Running, Event.Stop => some State.Stopped
  | State.Paused, Event.Resume => some State.Running
  | State.Paused, Event.Stop => some State.Stopped
  | _, _ => none

-- 正确性证明
theorem stateMachine_correct (s : State) (e : Event) (s' : State) :
  stateMachine s e = some s' ↔ Transition s e s' := by
  constructor
  · intro h
    cases s, e with
    | Idle, Start => 
      simp [stateMachine] at h
      injection h
      constructor
    | Running, Pause =>
      simp [stateMachine] at h
      injection h
      constructor
    | Running, Stop =>
      simp [stateMachine] at h
      injection h
      constructor
    | Paused, Resume =>
      simp [stateMachine] at h
      injection h
      constructor
    | Paused, Stop =>
      simp [stateMachine] at h
      injection h
      constructor
    | _, _ =>
      simp [stateMachine] at h
      contradiction
  · intro h
    cases h with
    | StartIdle => simp [stateMachine]
    | PauseRunning => simp [stateMachine]
    | ResumePaused => simp [stateMachine]
    | StopAny => simp [stateMachine]

-- 不变性
def invariant (s : State) : Prop :=
  match s with
  | State.Idle => True
  | State.Running => True
  | State.Paused => True
  | State.Stopped => True

theorem transition_preserves_invariant (s s' : State) (e : Event) :
  Transition s e s' → invariant s → invariant s' := by
  intro h_trans h_inv
  cases h_trans with
  | StartIdle => exact h_inv
  | PauseRunning => exact h_inv
  | ResumePaused => exact h_inv
  | StopAny => exact h_inv

end StateMachineVerification
```

## 📋 规范模式

### 抽象数据类型规范

```lean
-- 规范模式
namespace SpecificationPattern

-- 栈抽象数据类型
class Stack (α : Type) where
  empty : Stack α
  push : α → Stack α → Stack α
  pop : Stack α → Option (α × Stack α)
  isEmpty : Stack α → Bool

-- 栈规范
class StackSpec (α : Type) [Stack α] where
  -- 空栈性质
  empty_is_empty : isEmpty (empty : Stack α) = true
  
  -- 推送性质
  push_not_empty : (x : α) → (s : Stack α) → 
    isEmpty (push x s) = false
  
  -- 弹出性质
  pop_empty : pop (empty : Stack α) = none
  
  pop_push : (x : α) → (s : Stack α) → 
    pop (push x s) = some (x, s)

-- 列表实现
def ListStack (α : Type) := List α

instance {α : Type} : Stack (ListStack α) where
  empty := []
  push x s := x :: s
  pop s := 
    match s with
    | [] => none
    | x :: xs => some (x, xs)
  isEmpty s := s.isEmpty

-- 实现正确性证明
instance {α : Type} : StackSpec (ListStack α) where
  empty_is_empty := rfl
  
  push_not_empty x s := by
    simp [Stack.push, Stack.isEmpty, List.isEmpty]
  
  pop_empty := rfl
  
  pop_push x s := rfl

end SpecificationPattern
```

### 契约模式

```lean
-- 契约模式
namespace ContractPattern

-- 前置条件
def Pre (α : Type) := α → Prop

-- 后置条件
def Post (α β : Type) := α → β → Prop

-- 契约函数
structure ContractFunction (α β : Type) where
  pre : Pre α
  post : Post α β
  func : (x : α) → (h : pre x) → β

-- 契约验证
def ContractFunction.verify {α β : Type} (cf : ContractFunction α β) 
  (x : α) (h : cf.pre x) : cf.post x (cf.func x h) := by
  -- 这里需要具体的实现证明
  sorry

-- 除法契约
def safe_divide : ContractFunction (Nat × Nat) Nat where
  pre := fun (x, y) => y ≠ 0
  post := fun (x, y) result => result * y ≤ x ∧ x < (result + 1) * y
  func := fun (x, y) h => x / y

-- 列表查找契约
def list_find {α : Type} [DecidableEq α] : 
  ContractFunction (α × List α) (Option Nat) where
  pre := fun (x, xs) => True
  post := fun (x, xs) result => 
    match result with
    | none => x ∉ xs
    | some i => i < xs.length ∧ xs.get? i = some x
  func := fun (x, xs) _ => 
    List.findIndex (· == x) xs

end ContractPattern
```

## 🔒 安全模式

### 类型安全

```lean
-- 安全模式
namespace SafetyPattern

-- 类型安全引用
structure SafeRef (α : Type) where
  value : IO.Ref α
  invariant : α → Prop

-- 安全操作
def SafeRef.read {α : Type} (ref : SafeRef α) : IO α := do
  let value ← ref.value.get
  -- 运行时检查不变性
  if ref.invariant value then
    return value
  else
    panic "Invariant violated"

def SafeRef.write {α : Type} (ref : SafeRef α) (newValue : α) : IO Unit := do
  -- 检查新值是否满足不变性
  if ref.invariant newValue then
    ref.value.set newValue
  else
    panic "New value violates invariant"

-- 非负整数引用
def NonNegativeRef := SafeRef { n : Nat // n ≥ 0 }

def createNonNegativeRef (initialValue : Nat) (h : initialValue ≥ 0) : 
  IO NonNegativeRef := do
  let ref ← IO.mkRef ⟨initialValue, h⟩
  return { 
    value := ref, 
    invariant := fun ⟨n, _⟩ => n ≥ 0 
  }

-- 使用安全引用
def safeExample : IO Unit := do
  let ref ← createNonNegativeRef 5 (by decide)
  
  let value ← SafeRef.read ref
  IO.println s!"Value: {value.val}"
  
  SafeRef.write ref ⟨10, by decide⟩

end SafetyPattern
```

### 资源安全

```lean
-- 资源安全
namespace ResourceSafety

-- 资源句柄
structure ResourceHandle (α : Type) where
  resource : α
  isOpen : IO.Ref Bool

-- 资源管理
def ResourceHandle.open {α : Type} (resource : α) : IO (ResourceHandle α) := do
  let isOpen ← IO.mkRef true
  return { resource := resource, isOpen := isOpen }

def ResourceHandle.close {α : Type} (handle : ResourceHandle α) : IO Unit := do
  let open ← handle.isOpen.get
  if open then
    handle.isOpen.set false
  else
    panic "Resource already closed"

def ResourceHandle.use {α β : Type} (handle : ResourceHandle α) 
  (f : α → IO β) : IO β := do
  let open ← handle.isOpen.get
  if open then
    f handle.resource
  else
    panic "Resource is closed"

-- 自动资源管理
def withResource {α β : Type} (resource : α) (f : ResourceHandle α → IO β) : IO β := do
  let handle ← ResourceHandle.open resource
  try
    f handle
  finally
    ResourceHandle.close handle

-- 使用资源安全
def resourceExample : IO Unit := do
  let result ← withResource "file.txt" (fun handle => do
    ResourceHandle.use handle (fun content => do
      IO.println s!"Using resource: {content}"
      return "processed"))
  
  IO.println s!"Result: {result}"

end ResourceSafety
```

## 🎯 应用场景

### 1. 算法验证

```lean
-- 算法验证
namespace AlgorithmVerification

-- 排序算法规范
def isSorted {α : Type} [LE α] : List α → Prop
  | [] => True
  | [x] => True
  | x :: y :: xs => x ≤ y ∧ isSorted (y :: xs)

def isPermutation {α : Type} [DecidableEq α] : List α → List α → Prop
  | [], [] => True
  | x :: xs, ys => 
    x ∈ ys ∧ isPermutation xs (List.erase ys x)
  | _, _ => False

-- 插入排序
def insertSort {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] : 
  List α → List α
  | [] => []
  | x :: xs => sorted_insert x (insertSort xs)

-- 正确性证明
theorem insertSort_correct {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] 
  (xs : List α) : 
  isSorted (insertSort xs) ∧ isPermutation xs (insertSort xs) := by
  induction xs with
  | nil => 
    constructor
    · constructor
    · constructor
  | cons x xs ih =>
    constructor
    · rw [insertSort]
      apply sorted_insert_spec
      exact ih.left
    · rw [insertSort]
      -- 需要证明插入保持排列
      sorry

end AlgorithmVerification
```

### 2. 系统规范

```lean
-- 系统规范
namespace SystemSpecification

-- 银行账户系统
structure Account where
  balance : Nat
  owner : String

-- 账户操作
def Account.deposit (account : Account) (amount : Nat) : Account :=
  { account with balance := account.balance + amount }

def Account.withdraw (account : Account) (amount : Nat) : Option Account :=
  if amount ≤ account.balance then
    some { account with balance := account.balance - amount }
  else
    none

-- 系统不变性
def Account.invariant (account : Account) : Prop :=
  account.balance ≥ 0

-- 操作规范
theorem deposit_preserves_invariant (account : Account) (amount : Nat) :
  Account.invariant account → Account.invariant (Account.deposit account amount) := by
  intro h
  simp [Account.deposit, Account.invariant]
  exact Nat.le_add_left account.balance amount

theorem withdraw_preserves_invariant (account : Account) (amount : Nat) :
  Account.invariant account → 
  (Account.withdraw account amount = none ∨ 
   (∃ newAccount, Account.withdraw account amount = some newAccount ∧ 
    Account.invariant newAccount)) := by
  intro h
  simp [Account.withdraw, Account.invariant]
  split
  · left; rfl
  · right; exists { account with balance := account.balance - amount }
    constructor
    · rfl
    · exact Nat.le_sub_of_add_le h

end SystemSpecification
```

## 🚀 最佳实践

### 1. 设计原则

- **形式化**: 使用数学语言描述规范
- **可证明性**: 确保规范可以被证明
- **实用性**: 平衡形式化和实用性

### 2. 实现策略

- **渐进式**: 从简单规范开始
- **模块化**: 清晰的模块边界
- **可维护性**: 保持规范的可读性

### 3. 验证考虑

- **完备性**: 确保规范覆盖所有情况
- **一致性**: 避免规范间的矛盾
- **可执行性**: 确保规范可以执行

---

**下一节**: [高级模式](./09-Advanced-Patterns.md)

**相关链接**:

- [并发模式](./07-Concurrent-Patterns.md)
- [设计模式基础](./01-Design-Patterns-Basics.md)
- [软件设计](../08-Software-Design/)
