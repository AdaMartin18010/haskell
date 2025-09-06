# 14.5 典型例子 Examples of Information Theory #InformationTheory-14.5

## 14.5.1 熵的计算 Entropy Calculation #InformationTheory-14.5.1

### 中文

以二元分布熵为例，展示信息量的度量。

### English

Example: Entropy of a binary distribution, demonstrating information measurement.

#### Haskell

```haskell
import Data.List (foldl')
import Data.Map (fromListWith, toList)
import Data.Maybe (fromMaybe)
import Data.Function (on)
import Data.Foldable (sum)
import Data.Ord (comparing)
import Data.List (sort)
import Data.Bifunctor (bimap)
import Data.Tuple (swap)
import Data.Char (ord)
import Data.Functor ((<&>))
import Data.Foldable (foldl')
import Data.List (group, sort)
import Data.Map (fromListWith, toList)
import Data.Maybe (fromMaybe)
import Data.Function (on)
import Data.Foldable (sum)
import Data.Ord (comparing)
import Data.List (sort)
import Data.Bifunctor (bimap)
import Data.Tuple (swap)
import Data.Char (ord)
import Data.Functor ((<&>))

entropy :: [Double] -> Double
entropy ps = negate $ sum [p * logBase 2 p | p <- ps, p > 0]
```

#### Rust

```rust
fn entropy(ps: &[f64]) -> f64 {
    -ps.iter().filter(|&&p| p > 0.0).map(|&p| p * p.log2()).sum::<f64>()
}
```

#### Lean

```lean
import data.real.basic

def entropy (ps : list ℝ) : ℝ :=
  - (ps.filter (λ p, p > 0)).sum (λ p, p * real.logb 2 p)
```

## 14.5.2 工程案例 Engineering Example #InformationTheory-14.5.2

- Haskell：熵计算与数据压缩。
- Rust：高效编码与信道实现。
- Lean：形式化熵与编码证明。

## 14.5.3 相关Tag

`# InformationTheory #InformationTheory-14 #InformationTheory-14.5 #InformationTheory-14.5.1 #InformationTheory-14.5.2`
