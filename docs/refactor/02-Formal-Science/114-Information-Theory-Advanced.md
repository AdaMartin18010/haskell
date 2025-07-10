# 高级信息论 (Advanced Information Theory)

## 概述

高级信息论是研究信息传输、存储和处理的数学理论，涵盖熵、互信息、信道容量、编码理论等核心概念。它为通信系统、数据压缩、密码学等领域提供理论基础。

## 核心概念

### 1. 信息熵

- **香农熵**: 信息不确定性的度量
- **条件熵**: 给定条件下信息的不确定性
- **相对熵**: 两个概率分布之间的差异

### 2. 互信息

- **互信息**: 两个随机变量之间的信息共享
- **条件互信息**: 给定条件下两个变量的信息共享
- **信道容量**: 信道传输信息的最大速率

## 理论基础

### 1. 熵计算

```rust
use std::collections::HashMap;

fn shannon_entropy(probabilities: &[f64]) -> f64 {
    probabilities.iter()
        .filter(|&&p| p > 0.0)
        .map(|&p| -p * p.log2())
        .sum()
}

fn conditional_entropy(joint_prob: &HashMap<(char, char), f64>, 
                      marginal_prob: &HashMap<char, f64>) -> f64 {
    let mut entropy = 0.0;
    
    for ((x, y), p_xy) in joint_prob {
        if let Some(&p_x) = marginal_prob.get(x) {
            if p_x > 0.0 {
                entropy -= p_xy * (p_xy / p_x).log2();
            }
        }
    }
    
    entropy
}

fn mutual_information(joint_prob: &HashMap<(char, char), f64>,
                     marginal_x: &HashMap<char, f64>,
                     marginal_y: &HashMap<char, f64>) -> f64 {
    let mut mi = 0.0;
    
    for ((x, y), p_xy) in joint_prob {
        if let (Some(&p_x), Some(&p_y)) = (marginal_x.get(x), marginal_y.get(y)) {
            if p_x > 0.0 && p_y > 0.0 && p_xy > 0.0 {
                mi += p_xy * (p_xy / (p_x * p_y)).log2();
            }
        }
    }
    
    mi
}

// 信道容量计算
fn channel_capacity(transition_matrix: &Vec<Vec<f64>>) -> f64 {
    // 简化实现：使用迭代方法计算信道容量
    let mut capacity = 0.0;
    let mut input_dist = vec![1.0 / transition_matrix.len() as f64; transition_matrix.len()];
    
    for _ in 0..100 {
        // 计算输出分布
        let mut output_dist = vec![0.0; transition_matrix[0].len()];
        for i in 0..input_dist.len() {
            for j in 0..output_dist.len() {
                output_dist[j] += input_dist[i] * transition_matrix[i][j];
            }
        }
        
        // 计算互信息
        let mut mi = 0.0;
        for i in 0..input_dist.len() {
            for j in 0..output_dist.len() {
                if input_dist[i] > 0.0 && output_dist[j] > 0.0 && transition_matrix[i][j] > 0.0 {
                    mi += input_dist[i] * transition_matrix[i][j] * 
                          (transition_matrix[i][j] / output_dist[j]).log2();
                }
            }
        }
        
        capacity = mi;
        
        // 更新输入分布（简化）
        for i in 0..input_dist.len() {
            input_dist[i] = 1.0 / input_dist.len() as f64;
        }
    }
    
    capacity
}
```

### 2. 编码理论

```rust
use std::collections::HashMap;

#[derive(Debug, Clone)]
struct HuffmanNode {
    symbol: Option<char>,
    frequency: u32,
    left: Option<Box<HuffmanNode>>,
    right: Option<Box<HuffmanNode>>,
}

impl HuffmanNode {
    fn new(symbol: Option<char>, frequency: u32) -> Self {
        Self {
            symbol,
            frequency,
            left: None,
            right: None,
        }
    }
    
    fn is_leaf(&self) -> bool {
        self.left.is_none() && self.right.is_none()
    }
}

fn build_huffman_tree(frequencies: &HashMap<char, u32>) -> HuffmanNode {
    use std::collections::BinaryHeap;
    use std::cmp::Ordering;
    
    #[derive(Eq, PartialEq)]
    struct NodeWrapper {
        node: HuffmanNode,
    }
    
    impl Ord for NodeWrapper {
        fn cmp(&self, other: &Self) -> Ordering {
            other.node.frequency.cmp(&self.node.frequency)
        }
    }
    
    impl PartialOrd for NodeWrapper {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    
    let mut heap = BinaryHeap::new();
    
    // 创建叶子节点
    for (&symbol, &frequency) in frequencies {
        heap.push(NodeWrapper {
            node: HuffmanNode::new(Some(symbol), frequency),
        });
    }
    
    // 构建树
    while heap.len() > 1 {
        let left = heap.pop().unwrap().node;
        let right = heap.pop().unwrap().node;
        
        let parent = HuffmanNode {
            symbol: None,
            frequency: left.frequency + right.frequency,
            left: Some(Box::new(left)),
            right: Some(Box::new(right)),
        };
        
        heap.push(NodeWrapper { node: parent });
    }
    
    heap.pop().unwrap().node
}

fn generate_huffman_codes(root: &HuffmanNode) -> HashMap<char, String> {
    let mut codes = HashMap::new();
    let mut current_code = String::new();
    
    fn traverse(node: &HuffmanNode, code: &mut String, codes: &mut HashMap<char, String>) {
        if node.is_leaf() {
            if let Some(symbol) = node.symbol {
                codes.insert(symbol, code.clone());
            }
        } else {
            if let Some(ref left) = node.left {
                code.push('0');
                traverse(left, code, codes);
                code.pop();
            }
            
            if let Some(ref right) = node.right {
                code.push('1');
                traverse(right, code, codes);
                code.pop();
            }
        }
    }
    
    traverse(root, &mut current_code, &mut codes);
    codes
}

// 香农-范诺编码
fn shannon_fano_encode(symbols: &[(char, u32)]) -> HashMap<char, String> {
    let mut codes = HashMap::new();
    
    fn encode_recursive(symbols: &[(char, u32)], code: &mut String, codes: &mut HashMap<char, String>) {
        if symbols.len() <= 1 {
            if let Some((symbol, _)) = symbols.first() {
                codes.insert(*symbol, code.clone());
            }
            return;
        }
        
        let total_freq: u32 = symbols.iter().map(|(_, freq)| freq).sum();
        let mut current_freq = 0;
        let mut split_index = 0;
        
        for (i, (_, freq)) in symbols.iter().enumerate() {
            current_freq += freq;
            if current_freq * 2 >= total_freq {
                split_index = i + 1;
                break;
            }
        }
        
        // 左子树
        code.push('0');
        encode_recursive(&symbols[..split_index], code, codes);
        code.pop();
        
        // 右子树
        code.push('1');
        encode_recursive(&symbols[split_index..], code, codes);
        code.pop();
    }
    
    let mut sorted_symbols = symbols.to_vec();
    sorted_symbols.sort_by(|a, b| b.1.cmp(&a.1));
    
    encode_recursive(&sorted_symbols, &mut String::new(), &mut codes);
    codes
}
```

## Haskell实现示例

```haskell
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (sortBy)
import Data.Ord (comparing)

-- 香农熵计算
shannonEntropy :: [Double] -> Double
shannonEntropy probabilities = 
    sum [ -p * logBase 2 p | p <- probabilities, p > 0 ]

-- 条件熵计算
conditionalEntropy :: Map (Char, Char) Double -> Map Char Double -> Double
conditionalEntropy jointProb marginalProb = 
    sum [ -p_xy * logBase 2 (p_xy / p_x) 
          | ((x, y), p_xy) <- Map.toList jointProb
          , let p_x = Map.findWithDefault 0 x marginalProb
          , p_x > 0 ]

-- 互信息计算
mutualInformation :: Map (Char, Char) Double -> Map Char Double -> Map Char Double -> Double
mutualInformation jointProb marginalX marginalY = 
    sum [ p_xy * logBase 2 (p_xy / (p_x * p_y))
          | ((x, y), p_xy) <- Map.toList jointProb
          , let p_x = Map.findWithDefault 0 x marginalX
          , let p_y = Map.findWithDefault 0 y marginalY
          , p_x > 0 && p_y > 0 && p_xy > 0 ]

-- 霍夫曼编码
data HuffmanNode = Leaf Char Int | Node Int HuffmanNode HuffmanNode

buildHuffmanTree :: [(Char, Int)] -> HuffmanNode
buildHuffmanTree frequencies = 
    let nodes = map (\(symbol, freq) -> Leaf symbol freq) frequencies
        buildTree nodes = 
            if length nodes == 1 
            then head nodes
            else 
                let sorted = sortBy (comparing getFreq) nodes
                    (node1:node2:rest) = sorted
                    newNode = Node (getFreq node1 + getFreq node2) node1 node2
                in buildTree (newNode : rest)
    in buildTree nodes
  where
    getFreq (Leaf _ freq) = freq
    getFreq (Node freq _ _) = freq

generateHuffmanCodes :: HuffmanNode -> Map Char String
generateHuffmanCodes root = 
    let go node code = 
            case node of
                Leaf symbol _ -> Map.singleton symbol code
                Node _ left right -> 
                    Map.union (go left (code ++ "0")) (go right (code ++ "1"))
    in go root ""

-- 香农-范诺编码
shannonFanoEncode :: [(Char, Int)] -> Map Char String
shannonFanoEncode symbols = 
    let sortedSymbols = sortBy (fun a b => compare b.snd a.snd) symbols
        encode symbols code = 
            case symbols of
                [] -> Map.empty
                [(symbol, _)] -> Map.singleton symbol code
                _ -> 
                    let totalFreq = sum (map snd symbols)
                        (left, right) = splitAtOptimal symbols totalFreq
                        leftCodes = encode left (code ++ "0")
                        rightCodes = encode right (code ++ "1")
                    in Map.union leftCodes rightCodes
    in encode sortedSymbols ""

splitAtOptimal :: [(Char, Int)] -> Int -> ([(Char, Int)], [(Char, Int)])
splitAtOptimal symbols totalFreq = 
    let rec go (symbols : List (Char × Nat)) (currentFreq : Nat) : List (Char × Nat) × List (Char × Nat) :=
        match symbols with
        | [] => ([], [])
        | (symbol, freq) :: rest => 
          if (currentFreq + freq) * 2 >= totalFreq
          then ([], symbols)
          else 
            let (left, right) := go rest (currentFreq + freq)
            ((symbol, freq) :: left, right)
    
    go symbols 0

-- 信道容量计算
channelCapacity :: [[Double]] -> Double
channelCapacity transitionMatrix = 
    let inputSize = length transitionMatrix
        outputSize = length (head transitionMatrix)
        
        -- 简化实现：使用均匀输入分布
        uniformInput = map (\i -> 1.0 / fromIntegral inputSize) [0..inputSize-1]
        
        -- 计算输出分布
        outputDist = 
            [ sum [ uniformInput !! i * (transitionMatrix !! i !! j) 
                   | i <- [0..inputSize-1] ]
              | j <- [0..outputSize-1] ]
        
        -- 计算互信息
        mutualInfo = 
            sum [ uniformInput !! i * (transitionMatrix !! i !! j) * 
                  logBase 2 ((transitionMatrix !! i !! j) / (outputDist !! j))
                  | i <- [0..inputSize-1], j <- [0..outputSize-1]
                  , uniformInput !! i > 0 && outputDist !! j > 0 && transitionMatrix !! i !! j > 0 ]
    in mutualInfo.foldl (· + ·) 0
```

## Lean实现思路

```lean
import Lean.Data.HashMap
import Lean.Data.HashMap.Basic

-- 香农熵计算
def shannonEntropy (probabilities : List Float) : Float :=
  probabilities.filter (· > 0)
    |>.map fun p => -p * (Float.log2 p)
    |>.foldl (· + ·) 0

-- 条件熵计算
def conditionalEntropy (jointProb : HashMap (Char × Char) Float) 
                       (marginalProb : HashMap Char Float) : Float :=
  jointProb.toList.foldl (fun acc ((x, y), p_xy) =>
    match marginalProb.find? x with
    | some p_x => 
      if p_x > 0 then acc - p_xy * (Float.log2 (p_xy / p_x)) else acc
    | none => acc
  ) 0

-- 互信息计算
def mutualInformation (jointProb : HashMap (Char × Char) Float)
                      (marginalX : HashMap Char Float)
                      (marginalY : HashMap Char Float) : Float :=
  jointProb.toList.foldl (fun acc ((x, y), p_xy) =>
    match (marginalX.find? x, marginalY.find? y) with
    | (some p_x, some p_y) => 
      if p_x > 0 && p_y > 0 && p_xy > 0 
      then acc + p_xy * (Float.log2 (p_xy / (p_x * p_y)))
      else acc
    | _ => acc
  ) 0

-- 霍夫曼编码
inductive HuffmanNode where
  | leaf : Char → Nat → HuffmanNode
  | node : Nat → HuffmanNode → HuffmanNode → HuffmanNode

def getFreq : HuffmanNode → Nat
  | HuffmanNode.leaf _ freq => freq
  | HuffmanNode.node freq _ _ => freq

def buildHuffmanTree (frequencies : List (Char × Nat)) : HuffmanNode :=
  let nodes := frequencies.map fun (symbol, freq) => HuffmanNode.leaf symbol freq
  
  let rec buildTree (nodes : List HuffmanNode) : HuffmanNode :=
    match nodes with
    | [node] => node
    | node1 :: node2 :: rest => 
      let newNode := HuffmanNode.node (getFreq node1 + getFreq node2) node1 node2
      buildTree (newNode :: rest)
    | _ => HuffmanNode.leaf 'a' 0 -- 默认情况
  
  buildTree nodes

def generateHuffmanCodes (root : HuffmanNode) : HashMap Char String :=
  let rec traverse (node : HuffmanNode) (code : String) : HashMap Char String :=
    match node with
    | HuffmanNode.leaf symbol _ => HashMap.singleton symbol code
    | HuffmanNode.node _ left right => 
      let leftCodes := traverse left (code ++ "0")
      let rightCodes := traverse right (code ++ "1")
      leftCodes.union rightCodes
  
  traverse root ""

-- 香农-范诺编码
def shannonFanoEncode (symbols : List (Char × Nat)) : HashMap Char String :=
  let sortedSymbols := symbols.sortBy (fun a b => compare b.snd a.snd)
  
  let rec encode (symbols : List (Char × Nat)) (code : String) : HashMap Char String :=
    match symbols with
    | [] => HashMap.empty
    | [(symbol, _)] => HashMap.singleton symbol code
    | _ => 
      let totalFreq := symbols.map (·.snd) |>.foldl (· + ·) 0
      let (left, right) := splitAtOptimal symbols totalFreq
      let leftCodes := encode left (code ++ "0")
      let rightCodes := encode right (code ++ "1")
      leftCodes.union rightCodes
  
  encode sortedSymbols ""

def splitAtOptimal (symbols : List (Char × Nat)) (totalFreq : Nat) : List (Char × Nat) × List (Char × Nat) :=
  let rec go (symbols : List (Char × Nat)) (currentFreq : Nat) : List (Char × Nat) × List (Char × Nat) :=
    match symbols with
    | [] => ([], [])
    | (symbol, freq) :: rest => 
      if (currentFreq + freq) * 2 >= totalFreq
      then ([], symbols)
      else 
        let (left, right) := go rest (currentFreq + freq)
        ((symbol, freq) :: left, right)
  
  go symbols 0

-- 信道容量计算
def channelCapacity (transitionMatrix : List (List Float)) : Float :=
  let inputSize := transitionMatrix.length
  let outputSize := transitionMatrix.head?.map (·.length) |>.getD 0
  
  -- 均匀输入分布
  let uniformInput := List.range inputSize |>.map fun _ => 1.0 / inputSize.toFloat
  
  -- 计算输出分布
  let outputDist := List.range outputSize |>.map fun j =>
    List.range inputSize |>.foldl (fun acc i =>
      acc + (uniformInput.get? i |>.getD 0) * 
            (transitionMatrix.get? i |>.bind (·.get? j) |>.getD 0)
    ) 0
  
  -- 计算互信息
  let mutualInfo := 
    List.range inputSize |>.bind fun i =>
      List.range outputSize |>.map fun j =>
        let p_input := uniformInput.get? i |>.getD 0
        let p_output := outputDist.get? j |>.getD 0
        let p_transition := transitionMatrix.get? i |>.bind (·.get? j) |>.getD 0
        
        if p_input > 0 && p_output > 0 && p_transition > 0
        then p_input * p_transition * (Float.log2 (p_transition / p_output))
        else 0
  
  mutualInfo.foldl (· + ·) 0
```

## 应用场景

### 1. 数据压缩

- **无损压缩**: 霍夫曼编码、算术编码
- **有损压缩**: JPEG、MP3、视频编码
- **压缩算法**: LZ77、LZ78、LZW

### 2. 通信系统

- **信道编码**: 纠错码、卷积码
- **调制解调**: QAM、PSK、FSK
- **多路复用**: 时分、频分、码分

### 3. 密码学

- **熵源**: 随机数生成
- **密钥生成**: 基于熵的密钥派生
- **信息隐藏**: 隐写术、水印

### 4. 机器学习

- **特征选择**: 基于互信息的特征选择
- **信息增益**: 决策树构建
- **聚类分析**: 信息论聚类

## 最佳实践

### 1. *熵计算*

- 处理零概率情况
- 使用对数底数一致性
- 考虑数值稳定性

### 2. 编码设计

- 选择合适编码算法
- 平衡压缩率和计算复杂度
- 考虑编码效率

### 3. 信道建模

- 准确建模信道特性
- 考虑噪声和干扰
- 优化传输参数

### 4. 实际应用

- 验证理论假设
- 考虑实现约束
- 评估性能指标

## 性能考虑

### 1. 计算效率

- 算法复杂度优化
- 内存使用优化
- 并行化处理

### 2. 数值稳定性

- 避免数值溢出
- 处理精度问题
- 使用稳定算法

### 3. 可扩展性

- 大规模数据处理
- 分布式计算
- 实时处理能力

## 总结

高级信息论为现代通信和数据处理提供了坚实的理论基础。通过深入理解熵、互信息、编码理论等核心概念，可以设计出高效、可靠的信息处理系统，为实际应用提供理论指导。
