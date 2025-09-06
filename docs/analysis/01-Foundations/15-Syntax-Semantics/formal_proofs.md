# 1.8 形式化证明 Formal Proofs

Tag: #SyntaxSemantics-1.8

## 进展与保型 Progress & Preservation（骨架）

- 定义：语法良构项在小步语义下非值则可前进（进展），步进保持类型不变（保型）
- Haskell（伪）：以 GADT/TypeFamilies 约束构造器保证保型
- Lean：以归纳定义与定理证明形式化两个性质

## 语义等价 Semantic Equivalence（骨架）

- 定义：≈ 为双向模拟/上下文等价
- 证明思路：共同不动点、合流性或逻辑关系

## 参考

- #Cross: #SyntaxSemantics-1.11
