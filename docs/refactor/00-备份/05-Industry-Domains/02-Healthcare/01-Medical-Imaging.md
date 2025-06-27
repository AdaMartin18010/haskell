# 医学影像

## 概述

医学影像技术用于获取、处理和分析人体内部结构的图像，辅助医疗诊断和治疗。本节将建立医学影像分析的形式化理论框架，并提供Haskell实现。

## 1. 图像基础

### 1.1 数字图像表示

**定义 1.1.1** (数字图像)
数字图像是二维函数 $f(x,y)$，其中 $(x,y)$ 是空间坐标，$f$ 是像素强度值。

**Haskell实现**：

```haskell
-- | 数字图像
data Image = Image
  { width :: Int
  , height :: Int
  , pixels :: [[Double]]
  } deriving (Show, Eq)

-- | 创建图像
createImage :: Int -> Int -> [[Double]] -> Image
createImage w h pixels = Image w h pixels

-- | 获取像素值
getPixel :: Image -> Int -> Int -> Double
getPixel image x y = 
  if x >= 0 && x < width image && y >= 0 && y < height image
  then pixels image !! y !! x
  else 0.0

-- | 设置像素值
setPixel :: Image -> Int -> Int -> Double -> Image
setPixel image x y value = 
  if x >= 0 && x < width image && y >= 0 && y < height image
  then let newPixels = updateMatrix (pixels image) y (updateRow (pixels image !! y) x value)
       in image { pixels = newPixels }
  else image

-- | 更新矩阵
updateMatrix :: [[a]] -> Int -> [a] -> [[a]]
updateMatrix matrix row newRow = 
  take row matrix ++ [newRow] ++ drop (row + 1) matrix

-- | 更新行
updateRow :: [a] -> Int -> a -> [a]
updateRow row col value = 
  take col row ++ [value] ++ drop (col + 1) row
```

### 1.2 图像滤波

**定义 1.2.1** (卷积滤波)
卷积滤波使用卷积核 $K$ 对图像进行滤波：

$$g(x,y) = \sum_{i=-k}^{k} \sum_{j=-k}^{k} K(i,j) f(x+i, y+j)$$

**Haskell实现**：

```haskell
-- | 卷积核
type Kernel = [[Double]]

-- | 高斯滤波
gaussianKernel :: Int -> Double -> Kernel
gaussianKernel size sigma = 
  let center = size `div` 2
      kernel = [[gaussian i j sigma | j <- [0..size-1]] | i <- [0..size-1]]
      sum = foldl (+) 0.0 (concat kernel)
  in [[kernel !! i !! j / sum | j <- [0..size-1]] | i <- [0..size-1]]

-- | 高斯函数
gaussian :: Int -> Int -> Double -> Double
gaussian x y sigma = 
  let r2 = fromIntegral ((x - 1)^2 + (y - 1)^2)
  in exp (-r2 / (2 * sigma^2))

-- | 卷积滤波
convolve :: Image -> Kernel -> Image
convolve image kernel = 
  let kSize = length kernel
      kCenter = kSize `div` 2
      newPixels = [[convolvePixel image kernel i j | j <- [0..width image-1]] 
                   | i <- [0..height image-1]]
  in image { pixels = newPixels }

-- | 卷积单个像素
convolvePixel :: Image -> Kernel -> Int -> Int -> Double
convolvePixel image kernel x y = 
  let kSize = length kernel
      kCenter = kSize `div` 2
      sum = foldl (+) 0.0 [kernel !! i !! j * getPixel image (x+i-kCenter) (y+j-kCenter)
                          | i <- [0..kSize-1], j <- [0..kSize-1]]
  in sum
```

## 2. 特征提取

### 2.1 边缘检测

**定义 2.1.1** (Canny边缘检测)
Canny边缘检测包括高斯滤波、梯度计算、非极大值抑制和双阈值处理。

**Haskell实现**：

```haskell
-- | Canny边缘检测
cannyEdgeDetection :: Image -> Double -> Double -> Image
cannyEdgeDetection image lowThreshold highThreshold = 
  let -- 1. 高斯滤波
      smoothed = convolve image (gaussianKernel 5 1.0)
      
      -- 2. 计算梯度
      (gradientMagnitude, gradientDirection) = computeGradient smoothed
      
      -- 3. 非极大值抑制
      suppressed = nonMaxSuppression gradientMagnitude gradientDirection
      
      -- 4. 双阈值处理
      edges = doubleThreshold suppressed lowThreshold highThreshold
  in edges

-- | 计算梯度
computeGradient :: Image -> (Image, Image)
computeGradient image = 
  let sobelX = [[-1, 0, 1], [-2, 0, 2], [-1, 0, 1]]
      sobelY = [[-1, -2, -1], [0, 0, 0], [1, 2, 1]]
      
      gradX = convolve image sobelX
      gradY = convolve image sobelY
      
      magnitude = computeMagnitude gradX gradY
      direction = computeDirection gradX gradY
  in (magnitude, direction)

-- | 计算梯度幅值
computeMagnitude :: Image -> Image -> Image
computeMagnitude gradX gradY = 
  let newPixels = [[sqrt ((getPixel gradX i j)^2 + (getPixel gradY i j)^2)
                    | j <- [0..width gradX-1]] | i <- [0..height gradX-1]]
  in gradX { pixels = newPixels }

-- | 计算梯度方向
computeDirection :: Image -> Image -> Image
computeDirection gradX gradY = 
  let newPixels = [[atan2 (getPixel gradY i j) (getPixel gradX i j)
                    | j <- [0..width gradX-1]] | i <- [0..height gradX-1]]
  in gradX { pixels = newPixels }
```

### 2.2 形态学操作

**定义 2.2.1** (形态学操作)
形态学操作使用结构元素对图像进行处理。

**Haskell实现**：

```haskell
-- | 结构元素
type StructuringElement = [[Bool]]

-- | 形态学膨胀
dilation :: Image -> StructuringElement -> Image
dilation image se = 
  let seSize = length se
      seCenter = seSize `div` 2
      newPixels = [[maximum [getPixel image (x+i-seCenter) (y+j-seCenter) 
                              | i <- [0..seSize-1], j <- [0..seSize-1],
                                se !! i !! j]
                    | y <- [0..height image-1]] | x <- [0..width image-1]]
  in image { pixels = newPixels }

-- | 形态学腐蚀
erosion :: Image -> StructuringElement -> Image
erosion image se = 
  let seSize = length se
      seCenter = seSize `div` 2
      newPixels = [[minimum [getPixel image (x+i-seCenter) (y+j-seCenter) 
                              | i <- [0..seSize-1], j <- [0..seSize-1],
                                se !! i !! j]
                    | y <- [0..height image-1]] | x <- [0..width image-1]]
  in image { pixels = newPixels }

-- | 开运算
opening :: Image -> StructuringElement -> Image
opening image se = dilation (erosion image se) se

-- | 闭运算
closing :: Image -> StructuringElement -> Image
closing image se = erosion (dilation image se) se
```

## 3. 图像分割

### 3.1 阈值分割

**定义 3.1.1** (Otsu阈值分割)
Otsu方法自动选择最优阈值，最大化类间方差。

**Haskell实现**：

```haskell
-- | Otsu阈值分割
otsuThreshold :: Image -> Double
otsuThreshold image = 
  let histogram = computeHistogram image
      totalPixels = width image * height image
      probabilities = map (\count -> fromIntegral count / fromIntegral totalPixels) histogram
      
      -- 计算类间方差
      variances = [computeBetweenClassVariance probabilities t | t <- [0..255]]
      maxVariance = maximum variances
      threshold = fromIntegral (head [t | (t, var) <- zip [0..255] variances, var == maxVariance])
  in threshold

-- | 计算直方图
computeHistogram :: Image -> [Int]
computeHistogram image = 
  let allPixels = concat (pixels image)
      pixelCounts = [length (filter (\p -> round p == i) allPixels) | i <- [0..255]]
  in pixelCounts

-- | 计算类间方差
computeBetweenClassVariance :: [Double] -> Int -> Double
computeBetweenClassVariance probabilities threshold = 
  let omega0 = sum (take threshold probabilities)
      omega1 = sum (drop threshold probabilities)
      
      mu0 = if omega0 > 0 
            then sum [fromIntegral i * probabilities !! i | i <- [0..threshold-1]] / omega0
            else 0
      mu1 = if omega1 > 0
            then sum [fromIntegral i * probabilities !! i | i <- [threshold..255]] / omega1
            else 0
      
      muT = sum [fromIntegral i * probabilities !! i | i <- [0..255]]
  in omega0 * omega1 * (mu0 - mu1)^2

-- | 应用阈值分割
applyThreshold :: Image -> Double -> Image
applyThreshold image threshold = 
  let newPixels = [[if getPixel image x y > threshold then 255.0 else 0.0
                    | y <- [0..height image-1]] | x <- [0..width image-1]]
  in image { pixels = newPixels }
```

### 3.2 区域生长

**定义 3.2.1** (区域生长)
区域生长从种子点开始，根据相似性准则扩展区域。

**Haskell实现**：

```haskell
-- | 区域生长
regionGrowing :: Image -> [(Int, Int)] -> Double -> Image
regionGrowing image seeds threshold = 
  let segmented = createImage (width image) (height image) 
                              (replicate (height image) (replicate (width image) 0.0))
      grown = foldl (\img seed -> growRegion img seed threshold) segmented seeds
  in grown

-- | 生长单个区域
growRegion :: Image -> (Int, Int) -> Double -> Image
growRegion image (x, y) threshold = 
  let seedValue = getPixel image x y
      visited = replicate (height image) (replicate (width image) False)
      queue = [(x, y)]
      result = growRegionHelper image seedValue threshold visited queue
  in result

-- | 区域生长辅助函数
growRegionHelper :: Image -> Double -> Double -> [[Bool]] -> [(Int, Int)] -> Image
growRegionHelper image seedValue threshold visited [] = 
  let newPixels = [[if visited !! i !! j then 255.0 else 0.0
                    | j <- [0..width image-1]] | i <- [0..height image-1]]
  in image { pixels = newPixels }
growRegionHelper image seedValue threshold visited ((x, y):queue) = 
  if x < 0 || x >= width image || y < 0 || y >= height image || visited !! y !! x
  then growRegionHelper image seedValue threshold visited queue
  else
    let currentValue = getPixel image x y
        similarity = abs (currentValue - seedValue)
        newVisited = updateMatrix visited y (updateRow (visited !! y) x True)
        newQueue = if similarity <= threshold
                   then queue ++ [(x+1, y), (x-1, y), (x, y+1), (x, y-1)]
                   else queue
    in growRegionHelper image seedValue threshold newVisited newQueue
```

## 4. 医学影像分析

### 4.1 CT图像分析

**定义 4.1.1** (CT图像)
CT图像是X射线断层扫描图像，显示人体内部结构。

**Haskell实现**：

```haskell
-- | CT图像
data CTImage = CTImage
  { image :: Image
  , hounsfieldUnits :: [[Int]]  -- HU值
  , sliceThickness :: Double
  } deriving (Show, Eq)

-- | 计算HU值
computeHounsfieldUnits :: Image -> CTImage
computeHounsfieldUnits image = 
  let -- 简化的HU值计算
      huValues = [[round (getPixel image x y * 1000 - 1000) | y <- [0..height image-1]]
                  | x <- [0..width image-1]]
  in CTImage image huValues 1.0

-- | 组织分割
tissueSegmentation :: CTImage -> TissueMap
tissueSegmentation ctImage = 
  let huValues = hounsfieldUnits ctImage
      tissueMap = [[classifyTissue (huValues !! x !! y) | y <- [0..length (head huValues)-1]]
                   | x <- [0..length huValues-1]]
  in TissueMap tissueMap

-- | 组织分类
data TissueType = Air | Fat | Water | Muscle | Bone
  deriving (Show, Eq)

-- | 组织映射
data TissueMap = TissueMap
  { tissues :: [[TissueType]]
  } deriving (Show, Eq)

-- | 分类组织
classifyTissue :: Int -> TissueType
classifyTissue hu = 
  if hu < -900
  then Air
  else if hu < -100
  then Fat
  else if hu < 100
  then Water
  else if hu < 300
  then Muscle
  else Bone
```

### 4.2 MRI图像分析

**定义 4.2.1** (MRI图像)
MRI图像使用磁场和射频脉冲生成人体内部图像。

**Haskell实现**：

```haskell
-- | MRI图像
data MRIImage = MRIImage
  { image :: Image
  , sequence :: MRISequence
  , contrast :: Double
  } deriving (Show, Eq)

data MRISequence = T1 | T2 | FLAIR | DWI
  deriving (Show, Eq)

-- | 脑部分割
brainSegmentation :: MRIImage -> BrainRegions
brainSegmentation mriImage = 
  let -- 简化的脑部分割
      regions = [[classifyBrainRegion (getPixel (image mriImage) x y) | y <- [0..height (image mriImage)-1]]
                 | x <- [0..width (image mriImage)-1]]
  in BrainRegions regions

-- | 脑部区域
data BrainRegion = WhiteMatter | GrayMatter | CSF | Lesion
  deriving (Show, Eq)

-- | 脑部区域映射
data BrainRegions = BrainRegions
  { regions :: [[BrainRegion]]
  } deriving (Show, Eq)

-- | 分类脑部区域
classifyBrainRegion :: Double -> BrainRegion
classifyBrainRegion intensity = 
  if intensity < 0.3
  then CSF
  else if intensity < 0.6
  then GrayMatter
  else if intensity < 0.9
  then WhiteMatter
  else Lesion
```

## 5. 诊断辅助

### 5.1 特征提取

**定义 5.1.1** (医学特征)
从医学影像中提取有诊断价值的特征。

**Haskell实现**：

```haskell
-- | 医学特征
data MedicalFeatures = MedicalFeatures
  { area :: Double
  , perimeter :: Double
  , circularity :: Double
  , texture :: [Double]
  } deriving (Show, Eq)

-- | 提取特征
extractFeatures :: Image -> MedicalFeatures
extractFeatures image = 
  let area = calculateArea image
      perimeter = calculatePerimeter image
      circularity = 4 * pi * area / (perimeter^2)
      texture = extractTextureFeatures image
  in MedicalFeatures area perimeter circularity texture

-- | 计算面积
calculateArea :: Image -> Double
calculateArea image = 
  let binaryPixels = [[if getPixel image x y > 128 then 1.0 else 0.0
                       | y <- [0..height image-1]] | x <- [0..width image-1]]
  in sum (concat binaryPixels)

-- | 计算周长
calculatePerimeter :: Image -> Double
calculatePerimeter image = 
  let edges = cannyEdgeDetection image 50 150
      edgePixels = [[if getPixel edges x y > 0 then 1.0 else 0.0
                     | y <- [0..height image-1]] | x <- [0..width image-1]]
  in sum (concat edgePixels)

-- | 提取纹理特征
extractTextureFeatures :: Image -> [Double]
extractTextureFeatures image = 
  let glcm = computeGLCM image
      contrast = computeContrast glcm
      homogeneity = computeHomogeneity glcm
      energy = computeEnergy glcm
      correlation = computeCorrelation glcm
  in [contrast, homogeneity, energy, correlation]

-- | 灰度共生矩阵
type GLCM = [[Int]]

-- | 计算GLCM
computeGLCM :: Image -> GLCM
computeGLCM image = 
  let levels = 256
      glcm = replicate levels (replicate levels 0)
      pixels = pixels image
  in foldl (\acc (i, j) -> 
    let val1 = round (pixels !! i !! j)
        val2 = if j + 1 < width image 
               then round (pixels !! i !! (j + 1))
               else val1
        newGLCM = updateMatrix acc val1 (updateRow (acc !! val1) val2 ((acc !! val1 !! val2) + 1))
    in newGLCM) glcm [(i, j) | i <- [0..height image-1], j <- [0..width image-1]]
```

### 5.2 机器学习诊断

**定义 5.2.1** (诊断模型)
使用机器学习模型辅助医学诊断。

**Haskell实现**：

```haskell
-- | 诊断结果
data Diagnosis = Diagnosis
  { condition :: String
  , confidence :: Double
  , features :: MedicalFeatures
  } deriving (Show, Eq)

-- | 诊断模型
data DiagnosticModel = DiagnosticModel
  { model :: MLModel
  , trainingData :: [(MedicalFeatures, String)]
  } deriving (Show, Eq)

-- | 诊断预测
predictDiagnosis :: DiagnosticModel -> MedicalFeatures -> Diagnosis
predictDiagnosis model features = 
  let prediction = predictModel (model model) (featuresToVector features)
      confidence = calculateConfidence prediction
      condition = classifyCondition prediction
  in Diagnosis condition confidence features

-- | 特征向量化
featuresToVector :: MedicalFeatures -> [Double]
featuresToVector features = 
  [area features, perimeter features, circularity features] ++ texture features

-- | 分类条件
classifyCondition :: [Double] -> String
classifyCondition prediction = 
  let maxIndex = head [i | (i, val) <- zip [0..] prediction, val == maximum prediction]
      conditions = ["Normal", "Benign", "Malignant"]
  in conditions !! maxIndex

-- | 计算置信度
calculateConfidence :: [Double] -> Double
calculateConfidence prediction = maximum prediction
```

## 6. 总结

医学影像分析提供了强大的工具来辅助医疗诊断。通过形式化建模和Haskell实现，我们可以：

1. **处理医学图像**：滤波、增强、分割
2. **提取诊断特征**：形态学、纹理、统计特征
3. **辅助诊断决策**：机器学习模型预测
4. **量化分析**：客观测量和评估

这些技术在现代医学中发挥着越来越重要的作用。

---

**参考文献**：

1. Gonzalez, R. C., & Woods, R. E. (2018). Digital Image Processing. Pearson.
2. Sonka, M., Hlavac, V., & Boyle, R. (2014). Image Processing, Analysis, and Machine Vision. Cengage Learning.
3. Otsu, N. (1979). A threshold selection method from gray-level histograms. IEEE Transactions on Systems, Man, and Cybernetics, 9(1), 62-66.
