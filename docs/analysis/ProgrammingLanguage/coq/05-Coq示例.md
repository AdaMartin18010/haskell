# Coq 示例（Examples）

> 基础定义、归纳、证明、提取与自动化示例；中英双语。

## 1. 基础与归纳 Basic & Induction

```coq
Inductive nat : Set := O | S (n : nat).

Fixpoint add (a b : nat) : nat :=
  match a with
  | O => b
  | S a' => S (add a' b)
  end.

Theorem add_O_r : forall a, add a O = a.
Proof.
  induction a; simpl; [reflexivity| now rewrite IHa].
Qed.
```

## 2. 等式与重写 Equality & Rewrite

```coq
Theorem add_S_l : forall a b, add (S a) b = S (add a b).
Proof. reflexivity. Qed.

Theorem add_comm : forall a b, add a b = add b a.
Proof.
  induction a; simpl; intros.
  - induction b; simpl; [reflexivity| now rewrite IHb].
  - now rewrite IHa, add_S_l.
Qed.
```

## 3. 提取与运行 Extraction

```coq
Require Import Extraction.
Extraction Language Haskell.

Extract Inductive nat => "Prelude.Integer" ["0" "(\x -> x + 1)"]
  "(\fO fS n -> if n == 0 then fO () else fS (n - 1))".

Recursive Extraction add.
```

## 4. 自动化与决策过程 Automation & Decision Procedures

```coq
Require Import Lia.
Goal forall x y : Z, x <= y + 1 -> x - y <= 1.
Proof. intros; lia. Qed.
```

## 5. 参考 References

- Software Foundations；Coq Refman；Ssreflect 文档；Coq-stdpp/Iris/VST
