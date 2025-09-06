# 05-Coq 示例与实战（Coq Examples & Practice）

> **中英双语核心定义 | Bilingual Core Definitions**

## 1. 定义 Definition

### 1.1 核心定义 Core Definition

- **中文**：Coq 示例是通过具体的代码实例来展示 Coq 的各种功能和应用。包括基础定义、归纳类型、证明构造、程序提取和自动化等，帮助理解 Coq 的实际使用方法。
- **English**: Coq examples demonstrate various features and applications of Coq through specific code instances. This includes basic definitions, inductive types, proof construction, program extraction, and automation, helping to understand the practical use of Coq.

## 2. 基础与归纳 Basic & Induction

### 2.1 自然数定义 Natural Number Definition

```coq
(* 自然数的归纳定义 *)
Inductive nat : Set := 
  | O : nat                    (* 零 *)
  | S (n : nat) : nat.         (* 后继 *)

(* 加法函数定义 *)
Fixpoint add (a b : nat) : nat :=
  match a with
  | O => b                     (* 0 + b = b *)
  | S a' => S (add a' b)       (* (S a') + b = S (a' + b) *)
  end.

(* 加法右单位元证明 *)
Theorem add_O_r : forall a, add a O = a.
Proof.
  induction a; simpl; [reflexivity| now rewrite IHa].
Qed.
```

### 2.2 列表定义 List Definition

```coq
(* 列表的归纳定义 *)
Inductive list (A : Type) : Type :=
  | nil : list A               (* 空列表 *)
  | cons (x : A) (xs : list A) : list A.  (* 构造列表 *)

(* 列表长度函数 *)
Fixpoint length (A : Type) (l : list A) : nat :=
  match l with
  | nil => O
  | cons _ xs => S (length A xs)
  end.

(* 列表连接函数 *)
Fixpoint append (A : Type) (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (append A xs l2)
  end.
```

## 3. 等式与重写 Equality & Rewrite

### 3.1 基础等式证明 Basic Equality Proofs

```coq
(* 加法左后继性质 *)
Theorem add_S_l : forall a b, add (S a) b = S (add a b).
Proof. reflexivity. Qed.

(* 加法交换律 *)
Theorem add_comm : forall a b, add a b = add b a.
Proof.
  induction a; simpl; intros.
  - induction b; simpl; [reflexivity| now rewrite IHb].
  - now rewrite IHa, add_S_l.
Qed.

(* 加法结合律 *)
Theorem add_assoc : forall a b c, add (add a b) c = add a (add b c).
Proof.
  induction a; simpl; intros.
  - reflexivity.
  - now rewrite IHa.
Qed.
```

### 3.2 列表等式证明 List Equality Proofs

```coq
(* 列表连接长度 *)
Theorem append_length (A : Type) (l1 l2 : list A) :
  length A (append A l1 l2) = add (length A l1) (length A l2).
Proof.
  induction l1; simpl.
  - reflexivity.
  - now rewrite IHl1.
Qed.

(* 列表连接结合律 *)
Theorem append_assoc (A : Type) (l1 l2 l3 : list A) :
  append A (append A l1 l2) l3 = append A l1 (append A l2 l3).
Proof.
  induction l1; simpl.
  - reflexivity.
  - now rewrite IHl1.
Qed.
```

## 4. 依赖类型 Dependent Types

### 4.1 向量定义 Vector Definition

```coq
(* 依赖类型：向量 *)
Inductive vector (A : Type) : nat -> Type :=
  | vnil : vector A 0
  | vcons (n : nat) (x : A) (v : vector A n) : vector A (S n).

(* 向量连接 *)
Fixpoint vappend (A : Type) (n m : nat) 
  (v1 : vector A n) (v2 : vector A m) : vector A (add n m) :=
  match v1 with
  | vnil => v2
  | vcons n' x v1' => vcons (add n' m) x (vappend A n' m v1' v2)
  end.

(* 向量连接长度 *)
Theorem vappend_length (A : Type) (n m : nat) 
  (v1 : vector A n) (v2 : vector A m) :
  length A (vappend A n m v1 v2) = add n m.
Proof.
  induction v1; simpl.
  - reflexivity.
  - now rewrite IHv1.
Qed.
```

## 5. 程序提取 Program Extraction

### 5.1 Haskell 提取 Haskell Extraction

```coq
Require Import Extraction.

(* 设置提取语言为 Haskell *)
Extraction Language Haskell.

(* 定义自然数到 Haskell Integer 的映射 *)
Extract Inductive nat => "Prelude.Integer" 
  ["0" "(\x -> x + 1)"]
  "(\fO fS n -> if n == 0 then fO () else fS (n - 1))".

(* 提取加法函数 *)
Recursive Extraction add.

(* 提取列表函数 *)
Recursive Extraction append.
```

### 5.2 OCaml 提取 OCaml Extraction

```coq
(* 设置提取语言为 OCaml *)
Extraction Language OCaml.

(* 定义自然数到 OCaml int 的映射 *)
Extract Inductive nat => "int" 
  ["0" "succ"]
  "fun fO fS n -> if n = 0 then fO () else fS (n - 1)".

(* 提取函数 *)
Recursive Extraction add append.
```

## 6. 自动化与决策过程 Automation & Decision Procedures

### 6.1 线性算术自动化 Linear Arithmetic Automation

```coq
Require Import Lia.

(* 线性算术自动证明 *)
Goal forall x y : Z, x <= y + 1 -> x - y <= 1.
Proof. intros; lia. Qed.

(* 更复杂的线性算术 *)
Goal forall x y z : Z, x + y <= z -> x <= z - y.
Proof. intros; lia. Qed.

(* 整数不等式 *)
Goal forall x y : Z, x < y -> x + 1 <= y.
Proof. intros; lia. Qed.
```

### 6.2 环理论自动化 Ring Theory Automation

```coq
Require Import Ring.

(* 环理论自动证明 *)
Goal forall x y : Z, (x + y) * (x - y) = x * x - y * y.
Proof. intros; ring. Qed.

(* 多项式等式 *)
Goal forall x y z : Z, (x + y + z) * (x + y + z) = 
  x * x + 2 * x * y + 2 * x * z + y * y + 2 * y * z + z * z.
Proof. intros; ring. Qed.
```

### 6.3 一阶逻辑自动化 First-Order Logic Automation

```coq
Require Import Classical.

(* 一阶逻辑自动证明 *)
Goal forall (P Q R : Prop), 
  (P -> Q) -> (Q -> R) -> P -> R.
Proof. firstorder. Qed.

(* 量词处理 *)
Goal forall (A : Type) (P Q : A -> Prop),
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof. firstorder. Qed.
```

## 7. 高级示例 Advanced Examples

### 7.1 排序算法 Sorting Algorithm

```coq
(* 插入排序 *)
Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | nil => cons nat n (nil nat)
  | cons m l' => 
    if leb n m then cons nat n l
    else cons nat m (insert n l')
  end.

Fixpoint insert_sort (l : list nat) : list nat :=
  match l with
  | nil => nil nat
  | cons n l' => insert n (insert_sort l')
  end.

(* 排序正确性 *)
Definition is_sorted (l : list nat) : Prop :=
  forall i j, i < j < length nat l -> 
  nth i l 0 <= nth j l 0.

Theorem insert_sort_correct (l : list nat) : 
  is_sorted (insert_sort l).
Proof.
  (* 证明过程 *)
Admitted.
```

### 7.2 二叉树 Binary Tree

```coq
(* 二叉树定义 *)
Inductive tree (A : Type) : Type :=
  | leaf : tree A
  | node (l : tree A) (x : A) (r : tree A) : tree A.

(* 树的高度 *)
Fixpoint height (A : Type) (t : tree A) : nat :=
  match t with
  | leaf => O
  | node l _ r => S (max (height A l) (height A r))
  end.

(* 树的节点数 *)
Fixpoint size (A : Type) (t : tree A) : nat :=
  match t with
  | leaf => O
  | node l _ r => S (add (size A l) (size A r))
  end.
```

## 8. 对比分析 Comparison

### 8.1 证明风格对比

| 风格 | 优点 | 缺点 | 适用场景 |
|------|------|------|----------|
| 基础战术 | 直观易懂 | 冗长 | 简单证明 |
| 自动化 | 快速高效 | 黑盒 | 标准问题 |
| SSReflect | 简洁优雅 | 学习曲线陡峭 | 复杂证明 |

## 9. 争议与批判 Controversies & Critique

### 9.1 提取效率

- **中文**：提取的代码可能不是最优的，需要手动优化
- **English**: Extracted code may not be optimal and requires manual optimization

### 9.2 自动化限制

- **中文**：自动化战术有其局限性，不能解决所有问题
- **English**: Automation tactics have limitations and cannot solve all problems

## 10. 前沿趋势 Frontier Trends

### 10.1 智能提取

- **中文**：发展更智能的代码提取技术
- **English**: Developing more intelligent code extraction techniques

### 10.2 证明自动化

- **中文**：提高证明自动化的能力和效率
- **English**: Improving the capability and efficiency of proof automation

## 11. 交叉引用 Cross References

- [Coq 形式系统 Coq Formal System](./01-Coq-Formal-System.md)
- [Coq 自动化 Coq Automation](./02-Coq-Automation.md)
- [Coq 生态 Coq Ecosystem](./03-Coq-Ecosystem.md)
- [Coq 战术 Coq Tactics](./04-Coq-Tactics.md)
- [Coq 定义 Coq Definitions](./04-Coq-Definitions.md)

## 12. 参考文献 References

### 12.1 核心文档 Core Documentation

- **Software Foundations**: 软件基础教程 (Software Foundations tutorial)
- **Coq Reference Manual**: 官方参考手册 (Official reference manual)
- **SSReflect 文档**: SSReflect 手册 (SSReflect manual)
- **Coq-stdpp/Iris/VST**: 相关项目文档 (Related project documentation)

### 12.2 在线资源 Online Resources

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Coq Examples](https://coq.inria.fr/refman/examples.html)

---

## 总结 Summary

Coq 示例展示了从基础定义到高级应用的完整过程，通过具体的代码实例帮助理解 Coq 的各种功能。从简单的自然数运算到复杂的依赖类型，从基础证明到自动化决策，这些示例为实际应用提供了重要的参考。

---

`# Coq #Examples #Practice #FormalVerification #DependentTypes #Extraction #Automation`
