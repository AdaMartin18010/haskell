# 207 信息论（Information Theory）

## 1. 概述

信息论是研究信息的度量、传输、编码与压缩的理论体系，是现代通信、计算机科学、人工智能等领域的基础。信息论为数据压缩、信道编码、加密等提供了理论依据。

## 2. 主要分支与核心问题

- 香农信息论（Shannon Information Theory）
- 熵与互信息
- 信道容量与编码定理
- 数据压缩与无损/有损编码
- 信息与复杂性、Kolmogorov复杂性

## 3. 理论体系与形式化表达

- 信息熵定义：
  \[
  H(X) = -\sum_{i} p(x_i) \log_2 p(x_i)
  \]
- 互信息、条件熵、信道容量等公式
- 香农编码、霍夫曼编码原理

## 4. Haskell实现示例

```haskell
import qualified Data.Map as M
import Data.List (group, sort)
import Data.Maybe (fromMaybe)

-- 计算熵的函数
entropy :: (Ord a, Floating b) => [a] -> b
entropy xs = negate . sum $ map probLog2 grouped
  where
    grouped = map (  -> fromIntegral (length t) / n) . group . sort $ xs
    n = fromIntegral (length xs)
    probLog2 p = p * logBase 2 p
```

## 5. 理论证明与推导

- 香农熵的最优性证明思路
- 信道容量定理的推导
- 霍夫曼编码的最优性证明

## 6. 应用领域与案例

- 通信系统中的信道编码与纠错
- 数据压缩（如ZIP、JPEG）
- 机器学习中的特征选择与信息增益

## 7. 相关理论对比

| 特性         | Haskell           | Rust              | Lean                |
|--------------|-------------------|-------------------|---------------------|
| 信息度量     | 支持（自定义函数）| 支持（库/自定义） | 可形式化证明        |
| 编码实现     | 支持              | 支持              | 可形式化建模        |
| 主要应用     | 算法、数据分析    | 系统编程、压缩    | 形式化信息理论      |

## 8. 参考文献

- [1] Shannon, C. E. (1948). A Mathematical Theory of Communication.
- [2] Cover, T. M., & Thomas, J. A. (2006). Elements of Information Theory.
- [3] Li, M., & Vitányi, P. (2008). An Introduction to Kolmogorov Complexity and Its Applications.
