# Lean 形式模型基础

## 🎯 概述

Lean作为定理证明助手，天然支持数学形式化建模。本章介绍Lean中的各种形式化模型，包括状态机、Petri网、进程代数等，以及它们在软件系统建模中的应用。

## 🧮 数学基础

### 1. 集合论基础

```lean
-- 集合论基础定义
namespace SetTheory

-- 集合类型
def Set (α : Type) := α → Prop

-- 集合操作
def Set.member {α : Type} (x : α) (s : Set α) : Prop := s x

def Set.empty {α : Type} : Set α := fun _ => False

def Set.universal {α : Type} : Set α := fun _ => True

def Set.union {α : Type} (s t : Set α) : Set α := fun x => s x ∨ t x

def Set.intersection {α : Type} (s t : Set α) : Set α := fun x => s x ∧ t x

def Set.complement {α : Type} (s : Set α) : Set α := fun x => ¬(s x)

-- 集合关系
def Set.subset {α : Type} (s t : Set α) : Prop := ∀ x, s x → t x

def Set.equal {α : Type} (s t : Set α) : Prop := ∀ x, s x ↔ t x

end SetTheory
```

### 2. 关系论基础

```lean
-- 关系论基础定义
namespace RelationTheory

-- 二元关系
def Relation (α : Type) := α → α → Prop

-- 关系性质
def Relation.reflexive {α : Type} (r : Relation α) : Prop := ∀ x, r x x

def Relation.symmetric {α : Type} (r : Relation α) : Prop := ∀ x y, r x y → r y x

def Relation.transitive {α : Type} (r : Relation α) : Prop := ∀ x y z, r x y → r y z → r x z

def Relation.equivalence {α : Type} (r : Relation α) : Prop := 
  Relation.reflexive r ∧ Relation.symmetric r ∧ Relation.transitive r

-- 关系操作
def Relation.compose {α : Type} (r s : Relation α) : Relation α := 
  fun x z => ∃ y, r x y ∧ s y z

def Relation.inverse {α : Type} (r : Relation α) : Relation α := 
  fun x y => r y x

end RelationTheory
```

## 🔄 状态机模型

### 1. 有限状态机 (FSM)

```lean
-- 有限状态机定义
namespace FiniteStateMachine

-- 状态机结构
structure FSM (State : Type) (Input : Type) (Output : Type) where
  initial : State
  transition : State → Input → State
  output : State → Output

-- 状态机执行
def FSM.execute {State Input Output : Type} (fsm : FSM State Input Output) 
  (inputs : List Input) : List Output :=
  let rec execute' (state : State) (inputs : List Input) : List Output :=
    match inputs with
    | [] => []
    | input :: rest => 
      let newState := fsm.transition state input
      let output := fsm.output newState
      output :: execute' newState rest
  execute' fsm.initial inputs

-- 示例：简单的开关状态机
inductive SwitchState
  | On
  | Off

inductive SwitchInput
  | Toggle
  | TurnOn
  | TurnOff

def switchFSM : FSM SwitchState SwitchInput Bool :=
  { initial := SwitchState.Off
    transition := fun state input =>
      match state, input with
      | SwitchState.Off, SwitchInput.Toggle => SwitchState.On
      | SwitchState.Off, SwitchInput.TurnOn => SwitchState.On
      | SwitchState.Off, SwitchInput.TurnOff => SwitchState.Off
      | SwitchState.On, SwitchInput.Toggle => SwitchState.Off
      | SwitchState.On, SwitchInput.TurnOn => SwitchState.On
      | SwitchState.On, SwitchInput.TurnOff => SwitchState.Off
    output := fun state => 
      match state with
      | SwitchState.On => true
      | SwitchState.Off => false
  }

end FiniteStateMachine
```

### 2. 状态转换系统

```lean
-- 状态转换系统
namespace StateTransitionSystem

-- 状态转换系统定义
structure STS (State : Type) (Action : Type) where
  states : Set State
  actions : Set Action
  transitions : Set (State × Action × State)
  initial : State

-- 可达性
def STS.reachable {State Action : Type} (sts : STS State Action) 
  (s1 s2 : State) : Prop :=
  ∃ path : List Action, 
    List.foldl (fun state action => 
      match sts.transitions (state, action, _) with
      | some nextState => nextState
      | none => state) s1 path = s2

-- 安全性性质
def STS.safety {State Action : Type} (sts : STS State Action) 
  (property : State → Prop) : Prop :=
  ∀ s, STS.reachable sts sts.initial s → property s

-- 活性性质
def STS.liveness {State Action : Type} (sts : STS State Action) 
  (property : State → Prop) : Prop :=
  ∀ s, STS.reachable sts sts.initial s → 
    ∃ s', STS.reachable sts s s' ∧ property s'

end StateTransitionSystem
```

## 🕸️ Petri网模型

### 1. Petri网基础

```lean
-- Petri网定义
namespace PetriNet

-- 库所和变迁
structure Place where
  id : Nat
  tokens : Nat

structure Transition where
  id : Nat
  inputPlaces : List Nat
  outputPlaces : List Nat

-- Petri网结构
structure PetriNet where
  places : List Place
  transitions : List Transition

-- 标记（Marking）
def Marking := List (Nat × Nat) -- (place_id, token_count)

-- 变迁启用条件
def Transition.enabled (t : Transition) (marking : Marking) : Bool :=
  List.all t.inputPlaces (fun placeId =>
    match List.find? marking (fun (id, _) => id == placeId) with
    | some (_, tokens) => tokens > 0
    | none => false)

-- 变迁执行
def Transition.fire (t : Transition) (marking : Marking) : Option Marking :=
  if t.enabled marking then
    let newMarking := 
      -- 移除输入库所的令牌
      let afterInput := List.foldl (fun m placeId =>
        List.map m (fun (id, tokens) =>
          if id == placeId then (id, tokens - 1) else (id, tokens))) marking t.inputPlaces
      -- 添加输出库所的令牌
      List.foldl (fun m placeId =>
        List.map m (fun (id, tokens) =>
          if id == placeId then (id, tokens + 1) else (id, tokens))) afterInput t.outputPlaces
    some newMarking
  else none

end PetriNet
```

### 2. Petri网分析

```lean
-- Petri网分析
namespace PetriNetAnalysis

-- 可达性分析
def PetriNet.reachable (pn : PetriNet) (m1 m2 : Marking) : Prop :=
  ∃ path : List Transition, 
    List.foldl (fun marking trans =>
      match Transition.fire trans marking with
      | some newMarking => newMarking
      | none => marking) m1 path = m2

-- 有界性分析
def PetriNet.bounded (pn : PetriNet) (k : Nat) : Prop :=
  ∀ marking, PetriNet.reachable pn pn.initial marking →
    ∀ (placeId, tokens) ∈ marking, tokens ≤ k

-- 活性分析
def PetriNet.live (pn : PetriNet) : Prop :=
  ∀ transition, ∀ marking, PetriNet.reachable pn pn.initial marking →
    ∃ marking', PetriNet.reachable pn marking marking' ∧ 
      Transition.enabled transition marking'

end PetriNetAnalysis
```

## 🔗 进程代数

### 1. CCS (Calculus of Communicating Systems)

```lean
-- CCS进程代数
namespace CCS

-- 进程表达式
inductive Process
  | Nil : Process
  | Action : String → Process
  | Prefix : String → Process → Process
  | Sum : Process → Process → Process
  | Parallel : Process → Process → Process
  | Restriction : Process → List String → Process
  | Relabeling : Process → (String → String) → Process

-- 语义关系
inductive Transition : Process → String → Process → Prop
  | Act : ∀ a p, Transition (Process.Prefix a p) a p
  | SumL : ∀ p q a p', Transition p a p' → Transition (Process.Sum p q) a p'
  | SumR : ∀ p q a q', Transition q a q' → Transition (Process.Sum p q) a q'
  | ParL : ∀ p q a p', Transition p a p' → Transition (Process.Parallel p q) a (Process.Parallel p' q)
  | ParR : ∀ p q a q', Transition q a q' → Transition (Process.Parallel p q) a (Process.Parallel p q')
  | Com : ∀ p q a p' q', Transition p a p' → Transition q a q' → 
           Transition (Process.Parallel p q) "τ" (Process.Parallel p' q')

-- 强等价
def Process.strongEquiv (p q : Process) : Prop :=
  ∀ a p', Transition p a p' → ∃ q', Transition q a q' ∧ Process.strongEquiv p' q' ∧
  ∀ a q', Transition q a q' → ∃ p', Transition p a p' ∧ Process.strongEquiv p' q'

end CCS
```

### 2. CSP (Communicating Sequential Processes)

```lean
-- CSP进程代数
namespace CSP

-- CSP进程
inductive CSPProcess
  | Stop : CSPProcess
  | Skip : CSPProcess
  | Prefix : String → CSPProcess → CSPProcess
  | Choice : CSPProcess → CSPProcess → CSPProcess
  | Parallel : CSPProcess → CSPProcess → List String → CSPProcess
  | Sequential : CSPProcess → CSPProcess → CSPProcess

-- 迹语义
def Trace := List String

def CSPProcess.traces (p : CSPProcess) : Set Trace :=
  match p with
  | CSPProcess.Stop => { [] }
  | CSPProcess.Skip => { [], ["✓"] }
  | CSPProcess.Prefix a q => 
    { trace | ∃ t ∈ CSPProcess.traces q, trace = a :: t }
  | CSPProcess.Choice p q =>
    CSPProcess.traces p ∪ CSPProcess.traces q
  | CSPProcess.Parallel p q sync =>
    { trace | ∃ tp ∈ CSPProcess.traces p, ∃ tq ∈ CSPProcess.traces q,
        trace = interleave tp tq sync }
  | CSPProcess.Sequential p q =>
    { trace | trace ∈ CSPProcess.traces p ∨ 
        ∃ tp ∈ CSPProcess.traces p, ∃ tq ∈ CSPProcess.traces q,
        tp.endsWith ["✓"] ∧ trace = tp.dropLast ++ tq }

-- 迹等价
def CSPProcess.traceEquiv (p q : CSPProcess) : Prop :=
  CSPProcess.traces p = CSPProcess.traces q

end CSP
```

## ⏰ 时态逻辑

### 1. 线性时态逻辑 (LTL)

```lean
-- 线性时态逻辑
namespace LinearTemporalLogic

-- LTL公式
inductive LTLFormula (State : Type)
  | Atomic : (State → Prop) → LTLFormula State
  | Not : LTLFormula State → LTLFormula State
  | And : LTLFormula State → LTLFormula State → LTLFormula State
  | Or : LTLFormula State → LTLFormula State → LTLFormula State
  | Next : LTLFormula State → LTLFormula State
  | Until : LTLFormula State → LTLFormula State → LTLFormula State
  | Always : LTLFormula State → LTLFormula State
  | Eventually : LTLFormula State → LTLFormula State

-- 路径
def Path (State : Type) := List State

-- 语义
def LTLFormula.satisfies {State : Type} (path : Path State) (formula : LTLFormula State) : Prop :=
  match formula with
  | LTLFormula.Atomic p => 
    match path with
    | [] => False
    | s :: _ => p s
  | LTLFormula.Not φ => ¬(LTLFormula.satisfies path φ)
  | LTLFormula.And φ ψ => LTLFormula.satisfies path φ ∧ LTLFormula.satisfies path ψ
  | LTLFormula.Or φ ψ => LTLFormula.satisfies path φ ∨ LTLFormula.satisfies path ψ
  | LTLFormula.Next φ =>
    match path with
    | [] => False
    | _ :: rest => LTLFormula.satisfies rest φ
  | LTLFormula.Until φ ψ =>
    ∃ i, i < path.length ∧ LTLFormula.satisfies (path.drop i) ψ ∧
      ∀ j, j < i → LTLFormula.satisfies (path.drop j) φ
  | LTLFormula.Always φ =>
    ∀ i, i < path.length → LTLFormula.satisfies (path.drop i) φ
  | LTLFormula.Eventually φ =>
    ∃ i, i < path.length ∧ LTLFormula.satisfies (path.drop i) φ

end LinearTemporalLogic
```

### 2. 计算树逻辑 (CTL)

```lean
-- 计算树逻辑
namespace ComputationTreeLogic

-- CTL公式
inductive CTLFormula (State : Type)
  | Atomic : (State → Prop) → CTLFormula State
  | Not : CTLFormula State → CTLFormula State
  | And : CTLFormula State → CTLFormula State → CTLFormula State
  | Or : CTLFormula State → CTLFormula State → CTLFormula State
  | EX : CTLFormula State → CTLFormula State
  | AX : CTLFormula State → CTLFormula State
  | EU : CTLFormula State → CTLFormula State → CTLFormula State
  | AU : CTLFormula State → CTLFormula State → CTLFormula State
  | EG : CTLFormula State → CTLFormula State
  | AG : CTLFormula State → CTLFormula State
  | EF : CTLFormula State → CTLFormula State
  | AF : CTLFormula State → CTLFormula State

-- Kripke结构
structure KripkeStructure (State : Type) where
  states : Set State
  transitions : Relation State
  labeling : State → Set String

-- CTL语义
def CTLFormula.satisfies {State : Type} (ks : KripkeStructure State) 
  (state : State) (formula : CTLFormula State) : Prop :=
  match formula with
  | CTLFormula.Atomic p => p state
  | CTLFormula.Not φ => ¬(CTLFormula.satisfies ks state φ)
  | CTLFormula.And φ ψ => CTLFormula.satisfies ks state φ ∧ CTLFormula.satisfies ks state ψ
  | CTLFormula.Or φ ψ => CTLFormula.satisfies ks state φ ∨ CTLFormula.satisfies ks state ψ
  | CTLFormula.EX φ => 
    ∃ nextState, ks.transitions state nextState ∧ CTLFormula.satisfies ks nextState φ
  | CTLFormula.AX φ =>
    ∀ nextState, ks.transitions state nextState → CTLFormula.satisfies ks nextState φ
  | CTLFormula.EU φ ψ =>
    ∃ path, path.startsWith state ∧ 
      ∃ i, CTLFormula.satisfies ks (path.get i) ψ ∧
        ∀ j, j < i → CTLFormula.satisfies ks (path.get j) φ
  | CTLFormula.AU φ ψ =>
    ∀ path, path.startsWith state →
      ∃ i, CTLFormula.satisfies ks (path.get i) ψ ∧
        ∀ j, j < i → CTLFormula.satisfies ks (path.get j) φ
  | CTLFormula.EG φ =>
    ∃ path, path.startsWith state ∧ 
      ∀ i, CTLFormula.satisfies ks (path.get i) φ
  | CTLFormula.AG φ =>
    ∀ path, path.startsWith state →
      ∀ i, CTLFormula.satisfies ks (path.get i) φ
  | CTLFormula.EF φ =>
    ∃ path, path.startsWith state ∧ 
      ∃ i, CTLFormula.satisfies ks (path.get i) φ
  | CTLFormula.AF φ =>
    ∀ path, path.startsWith state →
      ∃ i, CTLFormula.satisfies ks (path.get i) φ

end ComputationTreeLogic
```

## 🔄 模型检查

### 1. 模型检查算法

```lean
-- 模型检查
namespace ModelChecking

-- 状态空间搜索
def StateSpaceSearch {State : Type} (initial : State) 
  (transitions : State → List State) : List State :=
  let rec search (visited : Set State) (frontier : List State) : List State :=
    match frontier with
    | [] => visited.toList
    | current :: rest =>
      if visited.contains current then
        search visited rest
      else
        let newVisited := visited.insert current
        let newFrontier := rest ++ transitions current
        search newVisited newFrontier
  search Set.empty [initial]

-- 可达性分析
def ReachabilityAnalysis {State : Type} (initial : State) 
  (transitions : State → List State) (property : State → Prop) : Bool :=
  let reachableStates := StateSpaceSearch initial transitions
  List.all reachableStates property

-- 循环检测
def CycleDetection {State : Type} (initial : State) 
  (transitions : State → List State) : Bool :=
  let rec dfs (visited : Set State) (current : State) (path : List State) : Bool :=
    if path.contains current then
      true -- 发现循环
    else if visited.contains current then
      false
    else
      let newVisited := visited.insert current
      let newPath := current :: path
      List.any (transitions current) (fun next => dfs newVisited next newPath)
  dfs Set.empty initial []

end ModelChecking
```

## 🎯 应用场景

### 1. 协议验证

- **通信协议**: 验证协议正确性
- **安全协议**: 验证安全性质
- **分布式协议**: 验证一致性

### 2. 系统建模

- **并发系统**: 建模并发行为
- **实时系统**: 建模时间约束
- **嵌入式系统**: 建模硬件交互

### 3. 软件验证

- **程序验证**: 验证程序性质
- **算法验证**: 验证算法正确性
- **系统验证**: 验证系统行为

## 🚀 最佳实践

### 1. 建模原则

- **抽象性**: 适当的抽象层次
- **精确性**: 准确反映系统行为
- **简洁性**: 避免不必要的复杂性

### 2. 验证策略

- **性质定义**: 明确验证目标
- **模型构建**: 构建合适模型
- **工具使用**: 选择合适的验证工具

### 3. 结果分析

- **正确性**: 验证结果正确性
- **完整性**: 覆盖所有重要性质
- **可解释性**: 结果易于理解

---

**下一节**: [状态机模型](./02-State-Machine-Model.md)

**相关链接**:

- [应用模型](../09-Application-Models/)
- [软件设计](../08-Software-Design/)
- [设计模式](../07-Design-Patterns/)
- [执行流](../11-Execution-Flow/)
