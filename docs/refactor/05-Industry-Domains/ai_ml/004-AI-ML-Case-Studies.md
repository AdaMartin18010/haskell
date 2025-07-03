# AI/ML案例分析（Case Studies in AI/ML）

## 概述

AI/ML案例分析通过具体项目实例展示人工智能与机器学习在实际业务中的应用，涵盖需求分析、技术选型、实现方案、效果评估与经验总结。

## 案例1：推荐系统

### 业务背景

电商平台需要为用户推荐个性化商品，提升用户满意度和转化率。

### 技术方案

- **数据源**：用户行为日志、商品信息、用户画像
- **算法**：协同过滤、矩阵分解、深度学习
- **架构**：实时推荐API、离线训练、在线服务

### Haskell实现

```haskell
-- 用户-商品交互矩阵
type UserItemMatrix = Map Int (Map Int Double)

-- 协同过滤推荐
collaborativeFiltering :: UserItemMatrix -> Int -> [Int]
collaborativeFiltering matrix userId = 
  let userRatings = fromMaybe Map.empty (Map.lookup userId matrix)
      similarUsers = findSimilarUsers matrix userId
      recommendations = aggregateRecommendations matrix similarUsers userRatings
  in take 10 $ sortBy (comparing snd) recommendations

-- 计算用户相似度
findSimilarUsers :: UserItemMatrix -> Int -> [(Int, Double)]
findSimilarUsers matrix userId = 
  let userRatings = fromMaybe Map.empty (Map.lookup userId matrix)
      similarities = map (\otherId -> 
        (otherId, cosineSimilarity userRatings (fromMaybe Map.empty $ Map.lookup otherId matrix)))
        (Map.keys matrix)
  in filter ((/= userId) . fst) $ sortBy (comparing snd) similarities

-- 余弦相似度
cosineSimilarity :: Map Int Double -> Map Int Double -> Double
cosineSimilarity ratings1 ratings2 = 
  let dotProduct = sum [r1 * r2 | (item, r1) <- Map.toList ratings1, 
                                 r2 <- maybeToList (Map.lookup item ratings2)]
      norm1 = sqrt $ sum [r^2 | r <- Map.elems ratings1]
      norm2 = sqrt $ sum [r^2 | r <- Map.elems ratings2]
  in if norm1 * norm2 == 0 then 0 else dotProduct / (norm1 * norm2)
```

### Rust实现

```rust
use std::collections::HashMap;
use std::collections::BTreeMap;

type UserItemMatrix = HashMap<u32, HashMap<u32, f64>>;

struct RecommendationEngine {
    matrix: UserItemMatrix,
}

impl RecommendationEngine {
    fn new() -> Self {
        Self {
            matrix: HashMap::new(),
        }
    }
    
    fn collaborative_filtering(&self, user_id: u32) -> Vec<u32> {
        if let Some(user_ratings) = self.matrix.get(&user_id) {
            let similar_users = self.find_similar_users(user_id);
            let recommendations = self.aggregate_recommendations(&similar_users, user_ratings);
            recommendations.into_iter().take(10).collect()
        } else {
            Vec::new()
        }
    }
    
    fn find_similar_users(&self, user_id: u32) -> Vec<(u32, f64)> {
        let user_ratings = self.matrix.get(&user_id).unwrap_or(&HashMap::new());
        let mut similarities: Vec<(u32, f64)> = self.matrix
            .iter()
            .filter(|(id, _)| **id != user_id)
            .map(|(other_id, other_ratings)| {
                let similarity = self.cosine_similarity(user_ratings, other_ratings);
                (*other_id, similarity)
            })
            .collect();
        
        similarities.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
        similarities
    }
    
    fn cosine_similarity(&self, ratings1: &HashMap<u32, f64>, ratings2: &HashMap<u32, f64>) -> f64 {
        let mut dot_product = 0.0;
        let mut norm1_sq = 0.0;
        let mut norm2_sq = 0.0;
        
        for (item, &rating1) in ratings1 {
            norm1_sq += rating1 * rating1;
            if let Some(&rating2) = ratings2.get(item) {
                dot_product += rating1 * rating2;
            }
        }
        
        for (_, &rating2) in ratings2 {
            norm2_sq += rating2 * rating2;
        }
        
        let norm1 = norm1_sq.sqrt();
        let norm2 = norm2_sq.sqrt();
        
        if norm1 * norm2 == 0.0 {
            0.0
        } else {
            dot_product / (norm1 * norm2)
        }
    }
}
```

### Lean实现

```lean
-- 用户-商品交互矩阵
def UserItemMatrix := List (Nat × List (Nat × Float))

-- 协同过滤推荐
def collaborativeFiltering (matrix : UserItemMatrix) (userId : Nat) : List Nat :=
  let userRatings := matrix.find? (λ (id, _) => id = userId)
  let similarUsers := findSimilarUsers matrix userId
  let recommendations := aggregateRecommendations matrix similarUsers userRatings
  recommendations.take 10

-- 计算用户相似度
def findSimilarUsers (matrix : UserItemMatrix) (userId : Nat) : List (Nat × Float) :=
  let userRatings := matrix.find? (λ (id, _) => id = userId)
  let similarities := matrix.map (λ (otherId, otherRatings) => 
    (otherId, cosineSimilarity userRatings otherRatings))
  similarities.filter (λ (id, _) => id ≠ userId)

-- 余弦相似度
def cosineSimilarity (ratings1 : List (Nat × Float)) (ratings2 : List (Nat × Float)) : Float :=
  let dotProduct := ratings1.foldl (λ acc (item, r1) => 
    acc + (ratings2.find? (λ (i, _) => i = item) |>.map (λ (_, r2) => r1 * r2) |>.getD 0.0)) 0.0
  let norm1 := (ratings1.foldl (λ acc (_, r) => acc + r * r) 0.0).sqrt
  let norm2 := (ratings2.foldl (λ acc (_, r) => acc + r * r) 0.0).sqrt
  if norm1 * norm2 = 0.0 then 0.0 else dotProduct / (norm1 * norm2)
```

## 案例2：自然语言处理

### 业务背景

客服系统需要自动分类用户问题，提高响应效率和服务质量。

### 技术方案

- **数据源**：历史客服对话、问题分类标签
- **算法**：TF-IDF、词向量、BERT、Transformer
- **架构**：文本预处理、特征提取、分类模型、API服务

### Haskell实现

```haskell
-- 文本预处理
preprocessText :: String -> [String]
preprocessText text = 
  let words = words $ map toLower text
      stopWords = ["the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for", "of", "with", "by"]
  in filter (`notElem` stopWords) words

-- TF-IDF特征提取
tfidf :: [[String]] -> [[Double]]
tfidf documents = 
  let vocab = nub $ concat documents
      tf = map (\doc -> map (\word -> fromIntegral (count word doc) / fromIntegral (length doc)) vocab) documents
      idf = map (\word -> log (fromIntegral (length documents) / fromIntegral (countDocsWithWord word documents))) vocab
  in zipWith (zipWith (*)) tf (repeat idf)

-- 朴素贝叶斯分类
naiveBayes :: [[Double]] -> [String] -> [Double] -> String
naiveBayes features labels testFeatures = 
  let classes = nub labels
      classProbabilities = map (\cls -> 
        (cls, fromIntegral (count cls labels) / fromIntegral (length labels))) classes
      featureProbabilities = map (\cls -> 
        calculateFeatureProbabilities features labels cls testFeatures) classes
      scores = zipWith (\cls (_, prob) -> (cls, prob * (fromJust $ lookup cls classProbabilities))) 
                      classes featureProbabilities
  in fst $ maximumBy (comparing snd) scores
```

### Rust实现

```rust
use std::collections::HashMap;

struct TextProcessor {
    stop_words: HashSet<String>,
}

impl TextProcessor {
    fn new() -> Self {
        let mut stop_words = HashSet::new();
        stop_words.insert("the".to_string());
        stop_words.insert("a".to_string());
        stop_words.insert("an".to_string());
        // ... 更多停用词
        
        Self { stop_words }
    }
    
    fn preprocess_text(&self, text: &str) -> Vec<String> {
        text.to_lowercase()
            .split_whitespace()
            .filter(|word| !self.stop_words.contains(*word))
            .map(|s| s.to_string())
            .collect()
    }
}

struct TFIDFVectorizer {
    vocabulary: Vec<String>,
    idf: Vec<f64>,
}

impl TFIDFVectorizer {
    fn fit(&mut self, documents: &[Vec<String>]) {
        // 构建词汇表
        let mut vocab_set = HashSet::new();
        for doc in documents {
            for word in doc {
                vocab_set.insert(word.clone());
            }
        }
        self.vocabulary = vocab_set.into_iter().collect();
        
        // 计算IDF
        self.idf = self.vocabulary.iter().map(|word| {
            let doc_count = documents.iter()
                .filter(|doc| doc.contains(word))
                .count();
            (documents.len() as f64 / doc_count as f64).ln()
        }).collect();
    }
    
    fn transform(&self, documents: &[Vec<String>]) -> Vec<Vec<f64>> {
        documents.iter().map(|doc| {
            self.vocabulary.iter().map(|word| {
                let tf = doc.iter().filter(|w| w == word).count() as f64 / doc.len() as f64;
                let idf = self.idf[self.vocabulary.iter().position(|w| w == word).unwrap()];
                tf * idf
            }).collect()
        }).collect()
    }
}

struct NaiveBayesClassifier {
    class_priors: HashMap<String, f64>,
    feature_probs: HashMap<String, Vec<f64>>,
}

impl NaiveBayesClassifier {
    fn fit(&mut self, features: &[Vec<f64>], labels: &[String]) {
        // 计算类别先验概率
        let mut class_counts = HashMap::new();
        for label in labels {
            *class_counts.entry(label.clone()).or_insert(0) += 1;
        }
        
        let total = labels.len() as f64;
        for (class, count) in class_counts {
            self.class_priors.insert(class, count as f64 / total);
        }
        
        // 计算特征条件概率
        let classes: Vec<_> = self.class_priors.keys().cloned().collect();
        for class in classes {
            let class_features: Vec<_> = features.iter()
                .zip(labels.iter())
                .filter(|(_, label)| label == &class)
                .map(|(feat, _)| feat.clone())
                .collect();
            
            let feature_probs = self.calculate_feature_probabilities(&class_features);
            self.feature_probs.insert(class, feature_probs);
        }
    }
    
    fn predict(&self, features: &[f64]) -> String {
        let mut best_class = String::new();
        let mut best_score = f64::NEG_INFINITY;
        
        for (class, prior) in &self.class_priors {
            let feature_probs = &self.feature_probs[class];
            let mut score = prior.ln();
            
            for (feature, prob) in features.iter().zip(feature_probs) {
                score += (feature * prob + (1.0 - feature) * (1.0 - prob)).ln();
            }
            
            if score > best_score {
                best_score = score;
                best_class = class.clone();
            }
        }
        
        best_class
    }
}
```

### Lean实现

```lean
-- 文本预处理
def preprocessText (text : String) : List String :=
  let words := text.splitOn " "
  let stopWords := ["the", "a", "an", "and", "or", "but", "in", "on", "at", "to", "for", "of", "with", "by"]
  words.filter (λ word => ¬(stopWords.contains word))

-- TF-IDF特征提取
def tfidf (documents : List (List String)) : List (List Float) :=
  let vocab := documents.join.eraseDups
  let tf := documents.map (λ doc => 
    vocab.map (λ word => 
      (doc.count word).toFloat / doc.length.toFloat))
  let idf := vocab.map (λ word => 
    (documents.length.toFloat / (documents.count (λ doc => doc.contains word)).toFloat).log)
  tf.map (λ docTf => 
    docTf.zipWith idf (λ t idf => t * idf))

-- 朴素贝叶斯分类
def naiveBayes (features : List (List Float)) (labels : List String) (testFeatures : List Float) : String :=
  let classes := labels.eraseDups
  let classProbabilities := classes.map (λ cls => 
    (cls, (labels.count cls).toFloat / labels.length.toFloat))
  let featureProbabilities := classes.map (λ cls => 
    calculateFeatureProbabilities features labels cls testFeatures)
  let scores := classProbabilities.zipWith featureProbabilities (λ (cls, prob) featProb => 
    (cls, prob * featProb))
  scores.maximumBy (λ a b => a.snd.compare b.snd) |>.fst
```

## 案例3：计算机视觉

### 业务背景

制造业需要自动检测产品质量，提高生产效率和产品质量。

### 技术方案

- **数据源**：产品图像、缺陷标注、质量标准
- **算法**：CNN、YOLO、ResNet、图像分割
- **架构**：图像预处理、特征提取、检测模型、结果输出

### Haskell实现

```haskell
-- 图像数据结构
data Image = Image {
  width :: Int,
  height :: Int,
  channels :: Int,
  data :: [Double]
} deriving (Show)

-- 图像预处理
normalizeImage :: Image -> Image
normalizeImage img = img { data = map (/255.0) (data img) }

-- 卷积操作
convolve :: [[Double]] -> [[Double]] -> [[Double]]
convolve image kernel = 
  let kernelSize = length kernel
      imageHeight = length image
      imageWidth = length (head image)
      outputHeight = imageHeight - kernelSize + 1
      outputWidth = imageWidth - kernelSize + 1
  in [[sum [image !! (i + ki) !! (j + kj) * kernel !! ki !! kj | 
             ki <- [0..kernelSize-1], kj <- [0..kernelSize-1]] |
       j <- [0..outputWidth-1]] |
     i <- [0..outputHeight-1]]

-- 最大池化
maxPooling :: [[Double]] -> Int -> [[Double]]
maxPooling image poolSize = 
  let height = length image
      width = length (head image)
      outputHeight = height `div` poolSize
      outputWidth = width `div` poolSize
  in [[maximum [image !! (i * poolSize + di) !! (j * poolSize + dj) |
                di <- [0..poolSize-1], dj <- [0..poolSize-1]] |
        j <- [0..outputWidth-1]] |
      i <- [0..outputHeight-1]]
```

### Rust实现

```rust
#[derive(Debug, Clone)]
struct Image {
    width: usize,
    height: usize,
    channels: usize,
    data: Vec<f64>,
}

impl Image {
    fn new(width: usize, height: usize, channels: usize) -> Self {
        Self {
            width,
            height,
            channels,
            data: vec![0.0; width * height * channels],
        }
    }
    
    fn normalize(&mut self) {
        for pixel in &mut self.data {
            *pixel /= 255.0;
        }
    }
    
    fn get_pixel(&self, x: usize, y: usize, channel: usize) -> f64 {
        let index = (y * self.width + x) * self.channels + channel;
        self.data[index]
    }
    
    fn set_pixel(&mut self, x: usize, y: usize, channel: usize, value: f64) {
        let index = (y * self.width + x) * self.channels + channel;
        self.data[index] = value;
    }
}

struct ConvolutionLayer {
    kernel: Vec<Vec<f64>>,
    bias: f64,
}

impl ConvolutionLayer {
    fn new(kernel: Vec<Vec<f64>>, bias: f64) -> Self {
        Self { kernel, bias }
    }
    
    fn forward(&self, input: &Image) -> Image {
        let kernel_size = self.kernel.len();
        let output_width = input.width - kernel_size + 1;
        let output_height = input.height - kernel_size + 1;
        let mut output = Image::new(output_width, output_height, input.channels);
        
        for y in 0..output_height {
            for x in 0..output_width {
                for c in 0..input.channels {
                    let mut sum = 0.0;
                    for ky in 0..kernel_size {
                        for kx in 0..kernel_size {
                            sum += input.get_pixel(x + kx, y + ky, c) * self.kernel[ky][kx];
                        }
                    }
                    output.set_pixel(x, y, c, sum + self.bias);
                }
            }
        }
        
        output
    }
}

struct MaxPoolingLayer {
    pool_size: usize,
}

impl MaxPoolingLayer {
    fn new(pool_size: usize) -> Self {
        Self { pool_size }
    }
    
    fn forward(&self, input: &Image) -> Image {
        let output_width = input.width / self.pool_size;
        let output_height = input.height / self.pool_size;
        let mut output = Image::new(output_width, output_height, input.channels);
        
        for y in 0..output_height {
            for x in 0..output_width {
                for c in 0..input.channels {
                    let mut max_val = f64::NEG_INFINITY;
                    for py in 0..self.pool_size {
                        for px in 0..self.pool_size {
                            let pixel_val = input.get_pixel(
                                x * self.pool_size + px,
                                y * self.pool_size + py,
                                c
                            );
                            max_val = max_val.max(pixel_val);
                        }
                    }
                    output.set_pixel(x, y, c, max_val);
                }
            }
        }
        
        output
    }
}
```

### Lean实现

```lean
-- 图像数据结构
structure Image where
  width : Nat
  height : Nat
  channels : Nat
  data : List Float
  deriving Repr

-- 图像预处理
def normalizeImage (img : Image) : Image :=
  { img with data := img.data.map (λ x => x / 255.0) }

-- 卷积操作
def convolve (image : List (List Float)) (kernel : List (List Float)) : List (List Float) :=
  let kernelSize := kernel.length
  let imageHeight := image.length
  let imageWidth := image.head?.getD [] |>.length
  let outputHeight := imageHeight - kernelSize + 1
  let outputWidth := imageWidth - kernelSize + 1
  
  List.range outputHeight |>.map (λ i =>
    List.range outputWidth |>.map (λ j =>
      List.range kernelSize |>.bind (λ ki =>
        List.range kernelSize |>.map (λ kj =>
          (image.get? (i + ki) |>.getD [] |>.get? (j + kj) |>.getD 0.0) *
          (kernel.get? ki |>.getD [] |>.get? kj |>.getD 0.0)
        )
      ) |>.sum
    )
  )

-- 最大池化
def maxPooling (image : List (List Float)) (poolSize : Nat) : List (List Float) :=
  let height := image.length
  let width := image.head?.getD [] |>.length
  let outputHeight := height / poolSize
  let outputWidth := width / poolSize
  
  List.range outputHeight |>.map (λ i =>
    List.range outputWidth |>.map (λ j =>
      List.range poolSize |>.bind (λ di =>
        List.range poolSize |>.map (λ dj =>
          image.get? (i * poolSize + di) |>.getD [] |>.get? (j * poolSize + dj) |>.getD 0.0
        )
      ) |>.maximum?.getD 0.0
    )
  )
```

## 工程分析

### 技术选型考虑

1. **Haskell优势**：
   - 强类型系统保证代码正确性
   - 函数式编程简化算法实现
   - 惰性求值优化内存使用
   - 适合原型开发和算法验证

2. **Rust优势**：
   - 零成本抽象，性能接近C++
   - 内存安全，无数据竞争
   - 丰富的生态系统
   - 适合生产环境部署

3. **Lean优势**：
   - 依赖类型系统，最强形式化保证
   - 定理证明，可验证算法正确性
   - 适合关键系统和安全要求高的场景

### 性能对比

| 维度 | Haskell | Rust | Lean |
|------|---------|------|------|
| 执行速度 | 中等 | 高 | 中等 |
| 内存使用 | 中等 | 低 | 中等 |
| 开发效率 | 高 | 中等 | 低 |
| 形式化验证 | 中等 | 低 | 高 |

### 适用场景

- **Haskell**：算法原型、数据处理、函数式编程团队
- **Rust**：高性能应用、系统集成、生产环境
- **Lean**：关键系统、安全验证、学术研究

## 经验总结

1. **多语言协作**：根据项目不同阶段选择合适语言
2. **性能优化**：Rust用于性能关键部分，Haskell用于算法验证
3. **形式化验证**：Lean用于关键算法证明，提升系统可靠性
4. **工程实践**：结合领域知识，选择最适合的技术栈

## 总结

AI/ML案例分析展示了不同语言在机器学习项目中的应用特点。Haskell适合算法原型和函数式实现，Rust适合高性能生产环境，Lean适合形式化验证和关键系统。实际项目中应根据具体需求选择合适的技术栈，并考虑多语言协作的可能性。

## 参考文献

- [Haskell for ML](https://hackage.haskell.org/package/hmatrix)
- [Rust ML](https://github.com/rust-ml)
- [Lean Prover Community](https://leanprover-community.github.io/)
