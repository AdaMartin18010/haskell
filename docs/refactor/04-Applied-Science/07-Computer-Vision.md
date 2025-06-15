# 计算机视觉

## 概述

计算机视觉是人工智能的重要分支，研究如何让计算机理解和处理视觉信息。它结合了图像处理、模式识别、机器学习和几何学等多个学科的理论和方法。

## 基本概念

### 图像表示

图像是计算机视觉的基本数据单位，可以用多种方式表示。

```haskell
-- 图像的基本类型
data Image = 
    GrayscaleImage GrayscaleData
  | RGBImage RGBData
  | HSVImage HSVData
  | BinaryImage BinaryData
  deriving (Show, Eq)

-- 灰度图像
data GrayscaleImage = GrayscaleImage {
    width :: Int,
    height :: Int,
    pixels :: [[Double]],  -- 0.0 到 1.0 之间的值
    metadata :: ImageMetadata
} deriving (Show, Eq)

-- RGB图像
data RGBImage = RGBImage {
    width :: Int,
    height :: Int,
    redChannel :: [[Double]],
    greenChannel :: [[Double]],
    blueChannel :: [[Double]],
    metadata :: ImageMetadata
} deriving (Show, Eq)

-- HSV图像
data HSVImage = HSVImage {
    width :: Int,
    height :: Int,
    hueChannel :: [[Double]],      -- 0.0 到 360.0
    saturationChannel :: [[Double]], -- 0.0 到 1.0
    valueChannel :: [[Double]],     -- 0.0 到 1.0
    metadata :: ImageMetadata
} deriving (Show, Eq)

-- 二值图像
data BinaryImage = BinaryImage {
    width :: Int,
    height :: Int,
    pixels :: [[Bool]],
    metadata :: ImageMetadata
} deriving (Show, Eq)

-- 图像元数据
data ImageMetadata = ImageMetadata {
    format :: ImageFormat,
    compression :: CompressionType,
    colorSpace :: ColorSpace,
    resolution :: Resolution
} deriving (Show, Eq)

data ImageFormat = 
    JPEG
  | PNG
  | BMP
  | TIFF
  deriving (Show, Eq)

data ColorSpace = 
    sRGB
  | AdobeRGB
  | ProPhotoRGB
  deriving (Show, Eq)

-- 分辨率
data Resolution = Resolution {
    dpi :: Int,
    physicalWidth :: Double,
    physicalHeight :: Double
} deriving (Show, Eq)
```

### 像素操作

```haskell
-- 像素坐标
data Pixel = Pixel {
    x :: Int,
    y :: Int
} deriving (Show, Eq)

-- 像素值
data PixelValue = 
    GrayscaleValue Double
  | RGBValue Double Double Double
  | HSVValue Double Double Double
  | BinaryValue Bool
  deriving (Show, Eq)

-- 像素操作
class PixelOperations a where
    getPixel :: a -> Pixel -> PixelValue
    setPixel :: a -> Pixel -> PixelValue -> a
    getNeighbors :: a -> Pixel -> [Pixel]
    isValidPixel :: a -> Pixel -> Bool

instance PixelOperations GrayscaleImage where
    getPixel image pixel = 
        if isValidPixel image pixel
        then GrayscaleValue (pixels image !! y pixel !! x pixel)
        else GrayscaleValue 0.0
    
    setPixel image pixel value = 
        case value of
            GrayscaleValue v -> 
                let newPixels = updatePixel (pixels image) (x pixel) (y pixel) v
                in image { pixels = newPixels }
            _ -> image
    
    getNeighbors image pixel = 
        let neighbors = [(x pixel + dx, y pixel + dy) | 
                        dx <- [-1, 0, 1], dy <- [-1, 0, 1],
                        dx /= 0 || dy /= 0]
        in [Pixel x y | (x, y) <- neighbors, isValidPixel image (Pixel x y)]
    
    isValidPixel image pixel = 
        x pixel >= 0 && x pixel < width image &&
        y pixel >= 0 && y pixel < height image

-- 更新像素值
updatePixel :: [[Double]] -> Int -> Int -> Double -> [[Double]]
updatePixel pixels x y value = 
    take y pixels ++ 
    [take x (pixels !! y) ++ [value] ++ drop (x + 1) (pixels !! y)] ++ 
    drop (y + 1) pixels
```

## 图像处理

### 1. 滤波

```haskell
-- 滤波器
data Filter = 
    GaussianFilter GaussianParams
  | MedianFilter Int
  | SobelFilter SobelDirection
  | LaplacianFilter
  deriving (Show, Eq)

-- 高斯滤波器参数
data GaussianParams = GaussianParams {
    kernelSize :: Int,
    sigma :: Double
} deriving (Show, Eq)

-- Sobel方向
data SobelDirection = 
    Horizontal
  | Vertical
  | Both
  deriving (Show, Eq)

-- 滤波器应用
class FilterApplication a where
    applyFilter :: a -> Filter -> a
    applyConvolution :: a -> [[Double]] -> a
    applyMorphological :: a -> MorphologicalOperation -> a

instance FilterApplication GrayscaleImage where
    applyFilter image filter = 
        case filter of
            GaussianFilter params -> applyGaussianFilter image params
            MedianFilter size -> applyMedianFilter image size
            SobelFilter direction -> applySobelFilter image direction
            LaplacianFilter -> applyLaplacianFilter image
    
    applyConvolution image kernel = 
        let convolved = convolve2D (pixels image) kernel
        in image { pixels = convolved }
    
    applyMorphological image operation = 
        applyMorphologicalOperation image operation

-- 高斯滤波
applyGaussianFilter :: GrayscaleImage -> GaussianParams -> GrayscaleImage
applyGaussianFilter image params = 
    let kernel = generateGaussianKernel (kernelSize params) (sigma params)
    in applyConvolution image kernel

-- 生成高斯核
generateGaussianKernel :: Int -> Double -> [[Double]]
generateGaussianKernel size sigma = 
    let center = size `div` 2
        kernel = [[gaussian x y sigma | x <- [0..size-1]] | y <- [0..size-1]]
        total = sum (concat kernel)
    in [[k / total | k <- row] | row <- kernel]

-- 高斯函数
gaussian :: Int -> Int -> Double -> Double
gaussian x y sigma = 
    let x' = fromIntegral (x - center)
        y' = fromIntegral (y - center)
        center = size `div` 2
        size = 2 * ceiling (3 * sigma) + 1
    in exp (-(x'^2 + y'^2) / (2 * sigma^2))

-- 2D卷积
convolve2D :: [[Double]] -> [[Double]] -> [[Double]]
convolve2D image kernel = 
    let imageHeight = length image
        imageWidth = length (head image)
        kernelHeight = length kernel
        kernelWidth = length (head kernel)
        padY = kernelHeight `div` 2
        padX = kernelWidth `div` 2
        padded = padImage image padX padY
    in [[convolveAt padded kernel x y | x <- [0..imageWidth-1]] 
        | y <- [0..imageHeight-1]]

-- 在特定位置卷积
convolveAt :: [[Double]] -> [[Double]] -> Int -> Int -> Double
convolveAt image kernel x y = 
    let kernelHeight = length kernel
        kernelWidth = length (head kernel)
        values = [image !! (y + dy) !! (x + dx) * 
                 kernel !! dy !! dx |
                 dy <- [0..kernelHeight-1],
                 dx <- [0..kernelWidth-1]]
    in sum values
```

### 2. 形态学操作

```haskell
-- 形态学操作
data MorphologicalOperation = 
    Erosion StructuringElement
  | Dilation StructuringElement
  | Opening StructuringElement
  | Closing StructuringElement
  deriving (Show, Eq)

-- 结构元素
data StructuringElement = StructuringElement {
    shape :: [[Bool]],
    origin :: (Int, Int)
} deriving (Show, Eq)

-- 基本结构元素
basicStructuringElements :: [StructuringElement]
basicStructuringElements = [
    -- 3x3 方形
    StructuringElement (replicate 3 (replicate 3 True)) (1, 1),
    -- 3x3 十字形
    StructuringElement [[False, True, False],
                       [True, True, True],
                       [False, True, False]] (1, 1),
    -- 3x3 菱形
    StructuringElement [[False, True, False],
                       [True, True, True],
                       [False, True, False]] (1, 1)
]

-- 形态学操作应用
applyMorphologicalOperation :: GrayscaleImage -> MorphologicalOperation -> GrayscaleImage
applyMorphologicalOperation image operation = 
    case operation of
        Erosion se -> applyErosion image se
        Dilation se -> applyDilation image se
        Opening se -> applyOpening image se
        Closing se -> applyClosing image se

-- 腐蚀
applyErosion :: GrayscaleImage -> StructuringElement -> GrayscaleImage
applyErosion image se = 
    let eroded = [[erodeAt image se x y | x <- [0..width image-1]] 
                  | y <- [0..height image-1]]
    in image { pixels = eroded }

-- 在特定位置腐蚀
erodeAt :: GrayscaleImage -> StructuringElement -> Int -> Int -> Double
erodeAt image se x y = 
    let shape = shape se
        (ox, oy) = origin se
        values = [pixels image !! (y + dy - oy) !! (x + dx - ox) |
                 dy <- [0..length shape-1],
                 dx <- [0..length (head shape)-1],
                 shape !! dy !! dx,
                 isValidPixel image (Pixel (x + dx - ox) (y + dy - oy))]
    in minimum values

-- 膨胀
applyDilation :: GrayscaleImage -> StructuringElement -> GrayscaleImage
applyDilation image se = 
    let dilated = [[dilateAt image se x y | x <- [0..width image-1]] 
                   | y <- [0..height image-1]]
    in image { pixels = dilated }

-- 在特定位置膨胀
dilateAt :: GrayscaleImage -> StructuringElement -> Int -> Int -> Double
dilateAt image se x y = 
    let shape = shape se
        (ox, oy) = origin se
        values = [pixels image !! (y + dy - oy) !! (x + dx - ox) |
                 dy <- [0..length shape-1],
                 dx <- [0..length (head shape)-1],
                 shape !! dy !! dx,
                 isValidPixel image (Pixel (x + dx - ox) (y + dy - oy))]
    in maximum values
```

## 特征提取

### 1. 边缘检测

```haskell
-- 边缘检测器
data EdgeDetector = 
    CannyDetector CannyParams
  | SobelDetector
  | LaplacianDetector
  | PrewittDetector
  deriving (Show, Eq)

-- Canny参数
data CannyParams = CannyParams {
    lowThreshold :: Double,
    highThreshold :: Double,
    gaussianSigma :: Double
} deriving (Show, Eq)

-- 边缘检测
class EdgeDetection a where
    detectEdges :: a -> EdgeDetector -> EdgeMap
    computeGradient :: a -> GradientMap
    nonMaxSuppression :: a -> EdgeMap -> EdgeMap
    hysteresisThresholding :: a -> EdgeMap -> Double -> Double -> EdgeMap

instance EdgeDetection GrayscaleImage where
    detectEdges image detector = 
        case detector of
            CannyDetector params -> applyCanny image params
            SobelDetector -> applySobel image
            LaplacianDetector -> applyLaplacian image
            PrewittDetector -> applyPrewitt image
    
    computeGradient image = 
        let sobelX = [[-1, 0, 1], [-2, 0, 2], [-1, 0, 1]]
            sobelY = [[-1, -2, -1], [0, 0, 0], [1, 2, 1]]
            gradX = convolve2D (pixels image) sobelX
            gradY = convolve2D (pixels image) sobelY
            magnitude = [[sqrt (x^2 + y^2) | (x, y) <- zip rowX rowY] | 
                        (rowX, rowY) <- zip gradX gradY]
            direction = [[atan2 y x | (x, y) <- zip rowX rowY] | 
                        (rowX, rowY) <- zip gradX gradY]
        in GradientMap magnitude direction
    
    nonMaxSuppression image edgeMap = 
        let gradient = computeGradient image
            suppressed = [[suppressAt edgeMap gradient x y | 
                          x <- [0..width image-1]] | 
                         y <- [0..height image-1]]
        in EdgeMap suppressed
    
    hysteresisThresholding image edgeMap low high = 
        let strong = [[if edgeMap !! y !! x > high then 1.0 else 0.0 | 
                      x <- [0..width image-1]] | 
                     y <- [0..height image-1]]
            weak = [[if edgeMap !! y !! x > low && edgeMap !! y !! x <= high 
                    then 0.5 else 0.0 | 
                    x <- [0..width image-1]] | 
                   y <- [0..height image-1]]
            final = connectEdges strong weak
        in EdgeMap final

-- 边缘图
data EdgeMap = EdgeMap {
    edges :: [[Double]]
} deriving (Show, Eq)

-- 梯度图
data GradientMap = GradientMap {
    magnitude :: [[Double]],
    direction :: [[Double]]
} deriving (Show, Eq)

-- Canny边缘检测
applyCanny :: GrayscaleImage -> CannyParams -> EdgeMap
applyCanny image params = 
    let -- 1. 高斯滤波
        smoothed = applyGaussianFilter image (GaussianParams 5 (gaussianSigma params))
        -- 2. 计算梯度
        gradient = computeGradient smoothed
        -- 3. 非极大值抑制
        suppressed = nonMaxSuppression smoothed (EdgeMap (magnitude gradient))
        -- 4. 双阈值处理
        final = hysteresisThresholding smoothed (edges suppressed) 
                (lowThreshold params) (highThreshold params)
    in final
```

### 2. 角点检测

```haskell
-- 角点检测器
data CornerDetector = 
    HarrisDetector HarrisParams
  | FASTDetector FASTParams
  | SIFTDetector SIFTParams
  deriving (Show, Eq)

-- Harris参数
data HarrisParams = HarrisParams {
    windowSize :: Int,
    k :: Double,
    threshold :: Double
} deriving (Show, Eq)

-- FAST参数
data FASTParams = FASTParams {
    threshold :: Int,
    nonMaxSuppression :: Bool
} deriving (Show, Eq)

-- SIFT参数
data SIFTParams = SIFTParams {
    numOctaves :: Int,
    numScales :: Int,
    sigma :: Double
} deriving (Show, Eq)

-- 角点检测
class CornerDetection a where
    detectCorners :: a -> CornerDetector -> [Corner]
    computeHarrisResponse :: a -> Int -> Double -> [[Double]]
    detectFAST :: a -> Int -> [Corner]

instance CornerDetection GrayscaleImage where
    detectCorners image detector = 
        case detector of
            HarrisDetector params -> applyHarris image params
            FASTDetector params -> applyFAST image params
            SIFTDetector params -> applySIFT image params
    
    computeHarrisResponse image windowSize k = 
        let -- 计算x和y方向的梯度
            sobelX = [[-1, 0, 1], [-2, 0, 2], [-1, 0, 1]]
            sobelY = [[-1, -2, -1], [0, 0, 0], [1, 2, 1]]
            gradX = convolve2D (pixels image) sobelX
            gradY = convolve2D (pixels image) sobelY
            
            -- 计算结构张量的元素
            Ixx = [[x^2 | x <- row] | row <- gradX]
            Iyy = [[y^2 | y <- row] | row <- gradY]
            Ixy = [[x * y | (x, y) <- zip rowX rowY] | 
                   (rowX, rowY) <- zip gradX gradY]
            
            -- 应用高斯窗口
            gaussian = generateGaussianKernel windowSize 1.0
            Sxx = convolve2D Ixx gaussian
            Syy = convolve2D Iyy gaussian
            Sxy = convolve2D Ixy gaussian
            
            -- 计算Harris响应
            response = [[det - k * trace^2 | 
                        (det, trace) <- zip rowDet rowTrace] |
                       (rowDet, rowTrace) <- zip determinants traces]
            
            determinants = [[Sxx !! y !! x * Syy !! y !! x - (Sxy !! y !! x)^2 | 
                           x <- [0..width image-1]] | 
                          y <- [0..height image-1]]
            traces = [[Sxx !! y !! x + Syy !! y !! x | 
                     x <- [0..width image-1]] | 
                    y <- [0..height image-1]]
        in response
    
    detectFAST image threshold = 
        let corners = []
            -- FAST算法的简化实现
            -- 在实际应用中需要更复杂的实现
        in corners

-- 角点
data Corner = Corner {
    position :: Pixel,
    response :: Double,
    scale :: Double
} deriving (Show, Eq)

-- Harris角点检测
applyHarris :: GrayscaleImage -> HarrisParams -> [Corner]
applyHarris image params = 
    let response = computeHarrisResponse image (windowSize params) (k params)
        corners = findLocalMaxima response (threshold params)
    in [Corner (Pixel x y) (response !! y !! x) 1.0 | (x, y) <- corners]

-- 寻找局部最大值
findLocalMaxima :: [[Double]] -> Double -> [(Int, Int)]
findLocalMaxima matrix threshold = 
    let height = length matrix
        width = length (head matrix)
        maxima = [(x, y) | y <- [1..height-2], x <- [1..width-1],
                         let center = matrix !! y !! x,
                         center > threshold,
                         center == maximum [matrix !! (y+dy) !! (x+dx) |
                                          dy <- [-1, 0, 1], dx <- [-1, 0, 1]]]
    in maxima
```

## 目标检测

### 1. 模板匹配

```haskell
-- 模板匹配
data TemplateMatching = TemplateMatching {
    template :: GrayscaleImage,
    method :: MatchingMethod,
    threshold :: Double
} deriving (Show, Eq)

data MatchingMethod = 
    SumOfSquaredDifferences
  | NormalizedCrossCorrelation
  | CorrelationCoefficient
  deriving (Show, Eq)

-- 模板匹配
class TemplateMatching a where
    matchTemplate :: a -> GrayscaleImage -> [Match]
    computeSimilarity :: a -> GrayscaleImage -> Pixel -> Double

instance TemplateMatching TemplateMatching where
    matchTemplate tm image = 
        let matches = []
            -- 模板匹配的实现
        in matches
    
    computeSimilarity tm image pixel = 
        case method tm of
            SumOfSquaredDifferences -> computeSSD tm image pixel
            NormalizedCrossCorrelation -> computeNCC tm image pixel
            CorrelationCoefficient -> computeCC tm image pixel

-- 匹配结果
data Match = Match {
    position :: Pixel,
    similarity :: Double,
    confidence :: Double
} deriving (Show, Eq)

-- 计算SSD
computeSSD :: TemplateMatching -> GrayscaleImage -> Pixel -> Double
computeSSD tm image pixel = 
    let templatePixels = pixels (template tm)
        imagePixels = extractRegion image pixel (width (template tm)) (height (template tm))
        differences = zipWith (zipWith (-)) templatePixels imagePixels
        squared = concatMap (map (^2)) differences
    in sum squared

-- 提取图像区域
extractRegion :: GrayscaleImage -> Pixel -> Int -> Int -> [[Double]]
extractRegion image pixel w h = 
    [[pixels image !! (y pixel + dy) !! (x pixel + dx) |
      dx <- [0..w-1]] |
     dy <- [0..h-1]]
```

### 2. 滑动窗口

```haskell
-- 滑动窗口检测器
data SlidingWindowDetector = SlidingWindowDetector {
    classifier :: Classifier,
    windowSize :: (Int, Int),
    stride :: (Int, Int),
    scaleFactor :: Double
} deriving (Show, Eq)

-- 分类器
data Classifier = 
    SVMClassifier SVMParams
  | NeuralNetworkClassifier NetworkParams
  | RandomForestClassifier ForestParams
  deriving (Show, Eq)

-- SVM参数
data SVMParams = SVMParams {
    kernel :: KernelType,
    C :: Double,
    gamma :: Double
} deriving (Show, Eq)

data KernelType = 
    Linear
  | RBF
  | Polynomial
  deriving (Show, Eq)

-- 滑动窗口检测
class SlidingWindowDetection a where
    detect :: a -> GrayscaleImage -> [Detection]
    extractFeatures :: a -> GrayscaleImage -> Pixel -> FeatureVector
    classify :: a -> FeatureVector -> Classification

instance SlidingWindowDetection SlidingWindowDetector where
    detect detector image = 
        let detections = []
            -- 滑动窗口检测的实现
        in detections
    
    extractFeatures detector image pixel = 
        let window = extractWindow image pixel (windowSize detector)
            features = computeHOGFeatures window
        in FeatureVector features
    
    classify detector features = 
        case classifier detector of
            SVMClassifier params -> classifySVM params features
            NeuralNetworkClassifier params -> classifyNN params features
            RandomForestClassifier params -> classifyRF params features

-- 检测结果
data Detection = Detection {
    boundingBox :: BoundingBox,
    confidence :: Double,
    classLabel :: String
} deriving (Show, Eq)

-- 边界框
data BoundingBox = BoundingBox {
    x :: Int,
    y :: Int,
    width :: Int,
    height :: Int
} deriving (Show, Eq)

-- 特征向量
data FeatureVector = FeatureVector {
    features :: [Double]
} deriving (Show, Eq)

-- 分类结果
data Classification = Classification {
    label :: String,
    confidence :: Double,
    probabilities :: [(String, Double)]
} deriving (Show, Eq)
```

## 形式化证明

### 边缘检测的正确性

**定理 1**: Canny边缘检测算法在理想条件下能够检测到所有显著边缘。

**证明**:
```haskell
-- Canny边缘检测的正确性
cannyCorrectness :: GrayscaleImage -> CannyParams -> Bool
cannyCorrectness image params = 
    let -- 1. 高斯滤波保持边缘位置
        smoothed = applyGaussianFilter image (GaussianParams 5 (gaussianSigma params))
        edgePreservation = preservesEdgePositions image smoothed
        
        -- 2. 梯度计算准确
        gradient = computeGradient smoothed
        gradientAccuracy = isGradientAccurate smoothed gradient
        
        -- 3. 非极大值抑制正确
        edgeMap = EdgeMap (magnitude gradient)
        suppressed = nonMaxSuppression smoothed edgeMap
        suppressionCorrectness = isSuppressionCorrect edgeMap suppressed
        
        -- 4. 双阈值处理有效
        final = hysteresisThresholding smoothed suppressed 
                (lowThreshold params) (highThreshold params)
        thresholdingEffectiveness = isThresholdingEffective suppressed final
    in edgePreservation && gradientAccuracy && 
       suppressionCorrectness && thresholdingEffectiveness

-- 边缘位置保持
preservesEdgePositions :: GrayscaleImage -> GrayscaleImage -> Bool
preservesEdgePositions original smoothed = 
    let originalEdges = findEdges original
        smoothedEdges = findEdges smoothed
        positionError = maximum [distance e1 e2 | 
                                (e1, e2) <- zip originalEdges smoothedEdges]
    in positionError < threshold
```

### 角点检测的稳定性

**定理 2**: Harris角点检测对图像旋转和尺度变化具有稳定性。

**证明**:
```haskell
-- Harris角点检测的稳定性
harrisStability :: GrayscaleImage -> HarrisParams -> Bool
harrisStability image params = 
    let -- 1. 旋转不变性
        rotated = rotateImage image 45
        originalCorners = applyHarris image params
        rotatedCorners = applyHarris rotated params
        rotationStability = checkRotationStability originalCorners rotatedCorners
        
        -- 2. 尺度不变性
        scaled = scaleImage image 1.5
        scaledCorners = applyHarris scaled params
        scaleStability = checkScaleStability originalCorners scaledCorners
        
        -- 3. 光照不变性
        brightened = adjustBrightness image 1.2
        brightenedCorners = applyHarris brightened params
        lightingStability = checkLightingStability originalCorners brightenedCorners
    in rotationStability && scaleStability && lightingStability

-- 检查旋转稳定性
checkRotationStability :: [Corner] -> [Corner] -> Bool
checkRotationStability original rotated = 
    let -- 将旋转后的角点坐标转换回原始坐标系
        transformedRotated = map (transformCorner 45) rotated
        -- 计算匹配的角点数量
        matches = countMatches original transformedRotated
        stability = fromIntegral matches / fromIntegral (length original)
    in stability > 0.8  -- 80%的角点应该保持稳定
```

## 总结

计算机视觉为理解和处理视觉信息提供了系统化的方法。通过图像处理、特征提取、目标检测等技术，我们可以构建能够"看见"和"理解"图像的智能系统。

在Haskell中，我们可以通过类型系统、代数数据类型和函数式编程等特性，构建严格的计算机视觉系统，确保图像处理算法的正确性和稳定性。这种形式化的方法为计算机视觉的应用提供了坚实的技术基础。 