# 1.8 形式化证明 Formal Proofs

Tag: #TypeSystems-1.8

## 健全性与保型 Soundness & Preservation（骨架）

- 目标：若 Γ ⊢ e : T 且 e → e'，则 Γ ⊢ e' : T
- 方法：对推导树与归约步进行联合归纳

## 进展 Progress（骨架）

- 目标：良类型项要么是值要么可前进
- 依赖：规范化值的定义与构造器不变式

## 参数多态 Parametricity（骨架）

- 陈述：多态函数不可区分参数结构
- 方法：逻辑关系/自由定理（Haskell 侧示例）
