# 数据可视化 - 形式化理论与Haskell实现

## 📋 概述

数据可视化是将数据转换为图形表示的过程，通过视觉元素揭示数据中的模式、趋势和关系。本文档从形式化角度建立数据可视化的完整理论体系。

## 🎯 核心概念

### 1. 可视化基础

#### 形式化定义

**定义 1.1 (可视化映射)** 可视化映射是一个函数 $V: D \to G$，其中：
- $D$ 是数据空间
- $G$ 是图形空间
- $V$ 保持数据的某些结构性质

**定义 1.2 (视觉通道)** 视觉通道是图形元素的属性，如位置、颜色、大小、形状等。

**定义 1.3 (视觉编码)** 视觉编码是将数据属性映射到视觉通道的过程：
$$E: A \times C \to V$$
其中 $A$ 是数据属性，$C$ 是视觉通道，$V$ 是视觉值。

#### Haskell实现

```haskell
{-# LANGUAGE GADTs, TypeFamilies, DataKinds #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module DataVisualization.Core where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (zipWith)

-- 数据空间
type DataSpace a = [a]

-- 图形空间
type GraphicsSpace = [(Double, Double)]  -- 2D坐标

-- 可视化映射
type VisualizationMapping a = DataSpace a -> GraphicsSpace

-- 视觉通道
data VisualChannel = 
  PositionX | PositionY | 
  Color | Size | Shape | 
  Opacity | Texture
  deriving (Show, Eq)

-- 视觉值
data VisualValue = 
  PositionValue Double Double |
  ColorValue Int Int Int |  -- RGB
  SizeValue Double |
  ShapeValue String |
  OpacityValue Double
  deriving (Show)

-- 视觉编码
type VisualEncoding a = Map (String, VisualChannel) (a -> VisualValue)

-- 基础可视化映射
linearMapping :: (Num a) => 
  (a, a) ->  -- 数据范围
  (Double, Double) ->  -- 视觉范围
  a -> Double
linearMapping (dataMin, dataMax) (visMin, visMax) value =
  let dataRange = dataMax - dataMin
      visRange = visMax - visMin
      normalized = (value - dataMin) / dataRange
  in visMin + normalized * visRange

-- 对数映射
logMapping :: (Floating a) => 
  (a, a) -> 
  (Double, Double) -> 
  a -> Double
logMapping (dataMin, dataMax) (visMin, visMax) value =
  let logMin = log dataMin
      logMax = log dataMax
      logValue = log value
      normalized = (logValue - logMin) / (logMax - logMin)
  in visMin + normalized * (visMax - visMin)
```

### 2. 基础图表类型

#### 形式化定义

**定义 1.4 (散点图)** 散点图将二维数据映射到平面坐标：
$$S: \{(x_i, y_i)\}_{i=1}^n \to \{(X_i, Y_i)\}_{i=1}^n$$

**定义 1.5 (线图)** 线图连接有序数据点：
$$L: \{(t_i, v_i)\}_{i=1}^n \to \bigcup_{i=1}^{n-1} \overline{P_i P_{i+1}}$$

**定义 1.6 (柱状图)** 柱状图用矩形表示分类数据：
$$B: \{(c_i, v_i)\}_{i=1}^n \to \{R_i\}_{i=1}^n$$
其中 $R_i$ 是矩形，高度为 $v_i$。

#### Haskell实现

```haskell
module DataVisualization.BasicCharts where

import DataVisualization.Core
import Data.List (zipWith)

-- 图表类型
data ChartType = 
  ScatterPlot | LineChart | BarChart | 
  Histogram | BoxPlot | Heatmap
  deriving (Show)

-- 散点图
data ScatterPlot a = ScatterPlot
  { xData :: [a]
  , yData :: [a]
  , xRange :: (a, a)
  , yRange :: (a, a)
  , pointSize :: Double
  , pointColor :: (Int, Int, Int)
  } deriving (Show)

-- 创建散点图
createScatterPlot :: (Num a) => 
  [a] -> [a] -> 
  (a, a) -> (a, a) ->  -- 数据范围
  (Double, Double) -> (Double, Double) ->  -- 视觉范围
  ScatterPlot a
createScatterPlot xData yData xRange yRange visRange =
  ScatterPlot xData yData xRange yRange 5.0 (0, 0, 255)

-- 散点图映射
scatterPlotMapping :: (Num a) => 
  ScatterPlot a -> 
  (Double, Double) -> (Double, Double) -> 
  [(Double, Double)]
scatterPlotMapping plot (visXMin, visXMax) (visYMin, visYMax) =
  zipWith (\x y -> 
    (linearMapping plot.xRange (visXMin, visXMax) x,
     linearMapping plot.yRange (visYMin, visYMax) y))
    plot.xData plot.yData

-- 线图
data LineChart a = LineChart
  { timeData :: [a]
  , valueData :: [a]
  , timeRange :: (a, a)
  , valueRange :: (a, a)
  , lineWidth :: Double
  , lineColor :: (Int, Int, Int)
  } deriving (Show)

-- 创建线图
createLineChart :: (Num a) => 
  [a] -> [a] -> 
  (a, a) -> (a, a) -> 
  LineChart a
createLineChart timeData valueData timeRange valueRange =
  LineChart timeData valueData timeRange valueRange 2.0 (255, 0, 0)

-- 线图映射
lineChartMapping :: (Num a) => 
  LineChart a -> 
  (Double, Double) -> (Double, Double) -> 
  [(Double, Double)]
lineChartMapping chart (visXMin, visXMax) (visYMin, visYMax) =
  zipWith (\t v -> 
    (linearMapping chart.timeRange (visXMin, visXMax) t,
     linearMapping chart.valueRange (visYMin, visYMax) v))
    chart.timeData chart.valueData

-- 柱状图
data BarChart a = BarChart
  { categories :: [String]
  , values :: [a]
  , valueRange :: (a, a)
  , barWidth :: Double
  , barColor :: (Int, Int, Int)
  } deriving (Show)

-- 创建柱状图
createBarChart :: (Num a) => 
  [String] -> [a] -> 
  (a, a) -> 
  BarChart a
createBarChart categories values valueRange =
  BarChart categories values valueRange 30.0 (0, 255, 0)

-- 柱状图映射
barChartMapping :: (Num a) => 
  BarChart a -> 
  (Double, Double) -> (Double, Double) -> 
  [(Double, Double, Double)]  -- (x, y, height)
barChartMapping chart (visXMin, visXMax) (visYMin, visYMax) =
  let numBars = length chart.categories
      barSpacing = (visXMax - visXMin) / fromIntegral numBars
      barPositions = [visXMin + fromIntegral i * barSpacing | i <- [0..numBars-1]]
      barHeights = [linearMapping chart.valueRange (visYMin, visYMax) value | value <- chart.values]
  in zipWith (\x height -> (x, visYMin, height)) barPositions barHeights
```

### 3. 高级可视化技术

#### 形式化定义

**定义 1.7 (热力图)** 热力图将矩阵数据映射到颜色空间：
$$H: M_{m \times n} \to C_{m \times n}$$
其中 $C_{i,j}$ 是位置 $(i,j)$ 的颜色值。

**定义 1.8 (箱线图)** 箱线图显示数据的分布特征：
$$B: \{x_i\}_{i=1}^n \to (Q_1, Q_2, Q_3, IQR, \text{outliers})$$

**定义 1.9 (直方图)** 直方图显示数据分布：
$$H: \{x_i\}_{i=1}^n \to \{(b_i, f_i)\}_{i=1}^k$$
其中 $b_i$ 是区间，$f_i$ 是频率。

#### Haskell实现

```haskell
module DataVisualization.AdvancedCharts where

import DataVisualization.Core
import Data.List (sort, group, length)
import Data.Map (Map)
import qualified Data.Map as Map

-- 热力图
data Heatmap = Heatmap
  { matrix :: [[Double]]
  , colorMap :: ColorMap
  , minValue :: Double
  , maxValue :: Double
  } deriving (Show)

-- 颜色映射
data ColorMap = 
  RedBlue | GreenYellow | GrayScale | Rainbow
  deriving (Show)

-- 创建热力图
createHeatmap :: [[Double]] -> ColorMap -> Heatmap
createHeatmap matrix colorMap =
  let allValues = concat matrix
      minVal = minimum allValues
      maxVal = maximum allValues
  in Heatmap matrix colorMap minVal maxVal

-- 热力图映射
heatmapMapping :: Heatmap -> [[(Double, Double, (Int, Int, Int))]]
heatmapMapping heatmap =
  let rows = length heatmap.matrix
      cols = length (head heatmap.matrix)
      cellWidth = 1.0 / fromIntegral cols
      cellHeight = 1.0 / fromIntegral rows
  in [[(fromIntegral j * cellWidth, 
        fromIntegral i * cellHeight,
        valueToColor heatmap.colorMap heatmap.minValue heatmap.maxValue value) |
        (j, value) <- zip [0..] row] |
        (i, row) <- zip [0..] heatmap.matrix]

-- 值到颜色映射
valueToColor :: ColorMap -> Double -> Double -> Double -> (Int, Int, Int)
valueToColor RedBlue minVal maxVal value =
  let normalized = (value - minVal) / (maxVal - minVal)
      red = round (255 * normalized)
      blue = round (255 * (1 - normalized))
  in (red, 0, blue)

valueToColor GreenYellow minVal maxVal value =
  let normalized = (value - minVal) / (maxVal - minVal)
      green = round (255 * normalized)
      red = round (255 * (1 - normalized))
  in (red, green, 0)

valueToColor GrayScale minVal maxVal value =
  let normalized = (value - minVal) / (maxVal - minVal)
      gray = round (255 * normalized)
  in (gray, gray, gray)

valueToColor Rainbow minVal maxVal value =
  let normalized = (value - minVal) / (maxVal - minVal)
      hue = normalized * 360
  in hsvToRgb hue 1.0 1.0

-- HSV到RGB转换
hsvToRgb :: Double -> Double -> Double -> (Int, Int, Int)
hsvToRgb h s v =
  let c = v * s
      x = c * (1 - abs ((h / 60) `mod'` 2 - 1))
      m = v - c
      (r', g', b') = case floor (h / 60) `mod` 6 of
        0 -> (c, x, 0)
        1 -> (x, c, 0)
        2 -> (0, c, x)
        3 -> (0, x, c)
        4 -> (x, 0, c)
        5 -> (c, 0, x)
  in (round ((r' + m) * 255), round ((g' + m) * 255), round ((b' + m) * 255))

-- 箱线图
data BoxPlot = BoxPlot
  { data_ :: [Double]
  , q1 :: Double
  , q2 :: Double
  , q3 :: Double
  , iqr :: Double
  , outliers :: [Double]
  } deriving (Show)

-- 创建箱线图
createBoxPlot :: [Double] -> BoxPlot
createBoxPlot data_ =
  let sorted = sort data_
      n = length sorted
      q2 = median sorted
      q1 = median (take (n `div` 2) sorted)
      q3 = median (drop (n `div` 2) sorted)
      iqr = q3 - q1
      lowerBound = q1 - 1.5 * iqr
      upperBound = q3 + 1.5 * iqr
      outliers = [x | x <- data_, x < lowerBound || x > upperBound]
  in BoxPlot data_ q1 q2 q3 iqr outliers

-- 中位数
median :: [Double] -> Double
median xs =
  let sorted = sort xs
      n = length sorted
  in if odd n
     then sorted !! (n `div` 2)
     else (sorted !! (n `div` 2 - 1) + sorted !! (n `div` 2)) / 2

-- 直方图
data Histogram = Histogram
  { data_ :: [Double]
  , bins :: [(Double, Double)]  -- (binStart, binEnd)
  , frequencies :: [Int]
  , binWidth :: Double
  } deriving (Show)

-- 创建直方图
createHistogram :: [Double] -> Int -> Histogram
createHistogram data_ numBins =
  let minVal = minimum data_
      maxVal = maximum data_
      binWidth = (maxVal - minVal) / fromIntegral numBins
      bins = [(minVal + fromIntegral i * binWidth, 
               minVal + fromIntegral (i + 1) * binWidth) | i <- [0..numBins-1]]
      frequencies = [length [x | x <- data_, 
                               x >= binStart, 
                               x < binEnd || (i == numBins-1 && x == binEnd)] |
                    (i, (binStart, binEnd)) <- zip [0..] bins]
  in Histogram data_ bins frequencies binWidth

-- 直方图映射
histogramMapping :: Histogram -> (Double, Double) -> (Double, Double) -> [(Double, Double, Double)]
histogramMapping hist (visXMin, visXMax) (visYMin, visYMax) =
  let maxFreq = maximum hist.frequencies
      binPositions = [visXMin + fromIntegral i * (visXMax - visXMin) / fromIntegral (length hist.bins) |
                     i <- [0..length hist.bins-1]]
      barHeights = [linearMapping (0, fromIntegral maxFreq) (visYMin, visYMax) (fromIntegral freq) |
                   freq <- hist.frequencies]
  in zipWith (\x height -> (x, visYMin, height)) binPositions barHeights
```

### 4. 交互式可视化

#### 形式化定义

**定义 1.10 (交互事件)** 交互事件是用户与可视化系统的交互：
$$E: U \times S \to S'$$
其中 $U$ 是用户操作，$S$ 是系统状态，$S'$ 是新状态。

**定义 1.11 (视图变换)** 视图变换改变可视化的显示参数：
$$T: V \times P \to V'$$
其中 $V$ 是当前视图，$P$ 是变换参数，$V'$ 是新视图。

#### Haskell实现

```haskell
module DataVisualization.Interactive where

import DataVisualization.Core
import DataVisualization.BasicCharts
import Data.Map (Map)
import qualified Data.Map as Map

-- 交互事件类型
data InteractionEvent = 
  Zoom Double Double |  -- 缩放因子，中心点
  Pan Double Double |   -- 平移距离
  Select [Int] |        -- 选择的数据点索引
  Filter String |       -- 过滤条件
  Highlight Int         -- 高亮数据点
  deriving (Show)

-- 视图状态
data ViewState = ViewState
  { zoomLevel :: Double
  , panX :: Double
  , panY :: Double
  , selectedPoints :: [Int]
  , filterCondition :: String
  , highlightedPoint :: Maybe Int
  } deriving (Show)

-- 初始视图状态
initialViewState :: ViewState
initialViewState = ViewState 1.0 0.0 0.0 [] "" Nothing

-- 处理交互事件
handleInteraction :: ViewState -> InteractionEvent -> ViewState
handleInteraction state (Zoom factor center) =
  state { zoomLevel = state.zoomLevel * factor }
handleInteraction state (Pan dx dy) =
  state { panX = state.panX + dx, panY = state.panY + dy }
handleInteraction state (Select indices) =
  state { selectedPoints = indices }
handleInteraction state (Filter condition) =
  state { filterCondition = condition }
handleInteraction state (Highlight index) =
  state { highlightedPoint = Just index }

-- 应用视图变换
applyViewTransform :: ViewState -> [(Double, Double)] -> [(Double, Double)]
applyViewTransform state points =
  let transformed = [(x * state.zoomLevel + state.panX, 
                     y * state.zoomLevel + state.panY) | (x, y) <- points]
  in transformed

-- 交互式散点图
data InteractiveScatterPlot a = InteractiveScatterPlot
  { basePlot :: ScatterPlot a
  , viewState :: ViewState
  , eventHandlers :: Map String (InteractionEvent -> IO ())
  } deriving (Show)

-- 创建交互式散点图
createInteractiveScatterPlot :: (Num a) => 
  ScatterPlot a -> 
  InteractiveScatterPlot a
createInteractiveScatterPlot basePlot =
  InteractiveScatterPlot basePlot initialViewState Map.empty

-- 添加事件处理器
addEventHandler :: String -> (InteractionEvent -> IO ()) -> 
                  InteractiveScatterPlot a -> InteractiveScatterPlot a
addEventHandler name handler plot =
  plot { eventHandlers = Map.insert name handler plot.eventHandlers }

-- 处理事件
processEvent :: InteractiveScatterPlot a -> InteractionEvent -> IO (InteractiveScatterPlot a)
processEvent plot event =
  let newState = handleInteraction plot.viewState event
      newPlot = plot { viewState = newState }
  in do
    -- 执行所有事件处理器
    mapM_ (\handler -> handler event) (Map.elems plot.eventHandlers)
    return newPlot

-- 获取变换后的数据点
getTransformedPoints :: (Num a) => 
  InteractiveScatterPlot a -> 
  (Double, Double) -> (Double, Double) -> 
  [(Double, Double)]
getTransformedPoints plot visRange =
  let basePoints = scatterPlotMapping plot.basePlot visRange
  in applyViewTransform plot.viewState basePoints
```

## 📊 可视化设计原则

### 1. 视觉编码理论

```haskell
module DataVisualization.DesignPrinciples where

import DataVisualization.Core
import Data.List (zipWith)

-- 视觉通道有效性
data ChannelEffectiveness = 
  Position | Size | Color | Shape | 
  Orientation | Texture | Motion
  deriving (Show, Eq, Ord)

-- 通道有效性排序（从高到低）
channelEffectivenessOrder :: [ChannelEffectiveness]
channelEffectivenessOrder = 
  [Position, Size, Color, Shape, Orientation, Texture, Motion]

-- 数据类型
data DataType = 
  Nominal | Ordinal | Interval | Ratio
  deriving (Show, Eq)

-- 推荐的视觉通道映射
recommendedChannels :: DataType -> [ChannelEffectiveness]
recommendedChannels Nominal = [Position, Color, Shape, Texture]
recommendedChannels Ordinal = [Position, Size, Color, Orientation]
recommendedChannels Interval = [Position, Size, Color]
recommendedChannels Ratio = [Position, Size, Color]

-- 颜色理论
data ColorScheme = 
  Sequential | Diverging | Categorical
  deriving (Show)

-- 创建颜色方案
createColorScheme :: ColorScheme -> Int -> [(Int, Int, Int)]
createColorScheme Sequential n =
  let step = 255 `div` (n - 1)
  in [(i * step, i * step, i * step) | i <- [0..n-1]]

createColorScheme Diverging n =
  let half = n `div` 2
      reds = [(255, i * (255 `div` half), i * (255 `div` half)) | i <- [0..half-1]]
      blues = [(i * (255 `div` half), i * (255 `div` half), 255) | i <- [half..n-1]]
  in reds ++ blues

createColorScheme Categorical n =
  let colors = [(255, 0, 0), (0, 255, 0), (0, 0, 255), 
                (255, 255, 0), (255, 0, 255), (0, 255, 255),
                (128, 0, 0), (0, 128, 0), (0, 0, 128)]
  in take n colors

-- 视觉层次
data VisualHierarchy = VisualHierarchy
  { primaryElements :: [String]
  , secondaryElements :: [String]
  , tertiaryElements :: [String]
  } deriving (Show)

-- 创建视觉层次
createVisualHierarchy :: [String] -> VisualHierarchy
createVisualHierarchy elements =
  let n = length elements
      primary = take (n `div` 3) elements
      secondary = take (n `div` 3) (drop (n `div` 3) elements)
      tertiary = drop (2 * (n `div` 3)) elements
  in VisualHierarchy primary secondary tertiary
```

## 📚 形式化证明

### 定理 1.1: 线性映射的保序性

**定理** 线性映射 $f: [a,b] \to [c,d]$ 保持数据的顺序关系。

**证明**：
1. 设 $x_1 < x_2$，则 $f(x_1) = c + \frac{x_1-a}{b-a}(d-c)$
2. $f(x_2) = c + \frac{x_2-a}{b-a}(d-c)$
3. 由于 $x_1 < x_2$，有 $\frac{x_1-a}{b-a} < \frac{x_2-a}{b-a}$
4. 因此 $f(x_1) < f(x_2)$，证毕。

### 定理 1.2: 颜色映射的单调性

**定理** 对于单调的颜色映射，数据值的大小关系在颜色空间中保持。

**证明**：
1. 设颜色映射 $C: \mathbb{R} \to \mathbb{R}^3$ 是单调的
2. 对于 $v_1 < v_2$，有 $C(v_1) < C(v_2)$（按某种序关系）
3. 在RGB空间中，亮度 $L = 0.299R + 0.587G + 0.114B$ 是单调的
4. 因此亮度保持数据的大小关系

## 🔗 相关链接

- [统计分析](./01-Statistical-Analysis.md)
- [数据挖掘](./02-Data-Mining.md)
- [大数据技术](./04-Big-Data-Technology.md)
- [机器学习](../03-Artificial-Intelligence/01-Machine-Learning.md)

---

*本文档建立了数据可视化的完整形式化理论体系，包含严格的数学定义、Haskell实现和形式化证明。* 