# 优化算法 - 形式化理论与Haskell实现

## 📋 概述

优化算法是寻找函数最优解的计算方法，广泛应用于机器学习、运筹学、工程优化等领域。本文档从形式化理论的角度分析各种优化算法，并提供完整的Haskell实现。

## 🎯 形式化定义

### 优化问题的基本概念

#### 优化问题的数学定义

给定目标函数 $f: \mathbb{R}^n \to \mathbb{R}$ 和约束条件，优化问题是：

$$\min_{x \in \Omega} f(x)$$

其中 $\Omega \subseteq \mathbb{R}^n$ 是可行域。

#### 优化问题的类型

1. **无约束优化**：$\Omega = \mathbb{R}^n$
2. **约束优化**：$\Omega \subset \mathbb{R}^n$
3. **凸优化**：$f$ 是凸函数，$\Omega$ 是凸集
4. **非凸优化**：$f$ 或 $\Omega$ 不满足凸性条件

#### 最优性条件

**一阶必要条件**：如果 $x^*$ 是局部最优解，则 $\nabla f(x^*) = 0$

**二阶充分条件**：如果 $\nabla f(x^*) = 0$ 且 $\nabla^2 f(x^*) \succ 0$，则 $x^*$ 是严格局部最优解

## 🔧 Haskell实现

### 基础类型定义

```haskell
{-# LANGUAGE TypeFamilies, FlexibleContexts, MultiParamTypeClasses #-}

import Data.List (minimumBy, maximumBy)
import Data.Maybe (fromMaybe)
import qualified Data.Vector as V
import qualified Data.Map as Map

-- 优化问题类型类
class OptimizationProblem prob where
    type Domain prob :: *
    type Objective prob :: *
    objectiveFunction :: prob -> Domain prob -> Objective prob
    gradient :: prob -> Domain prob -> Domain prob
    hessian :: prob -> Domain prob -> [[Objective prob]]
    domain :: prob -> Domain prob -> Bool

-- 优化算法结果类型
data OptimizationResult a b = OptimizationResult
    { optimalPoint :: a
    , optimalValue :: b
    , iterations :: Int
    , convergence :: Bool
    , time :: Double
    }

-- 优化算法类型类
class OptimizationAlgorithm alg where
    type Input alg :: *
    type Output alg :: *
    execute :: alg -> Input alg -> Output alg
    algorithmName :: alg -> String
    complexity :: alg -> String
```

### 1. 梯度下降算法

#### 形式化定义

梯度下降是一种一阶优化算法，通过沿着目标函数梯度的反方向迭代更新参数。

**算法描述**：
1. 初始化参数 $x_0$
2. 计算梯度 $\nabla f(x_k)$
3. 更新参数：$x_{k+1} = x_k - \alpha \nabla f(x_k)$
4. 重复步骤2-3直到收敛

#### Haskell实现

```haskell
-- 梯度下降算法
gradientDescent :: (Floating a, Ord a) => 
                  (V.Vector a -> a) -> 
                  (V.Vector a -> V.Vector a) -> 
                  V.Vector a -> 
                  a -> 
                  a -> 
                  Int -> 
                  OptimizationResult (V.Vector a) a
gradientDescent f grad x0 learningRate tolerance maxIter = 
    gradientDescent' f grad x0 learningRate tolerance maxIter 0

gradientDescent' :: (Floating a, Ord a) => 
                   (V.Vector a -> a) -> 
                   (V.Vector a -> V.Vector a) -> 
                   V.Vector a -> 
                   a -> 
                   a -> 
                   Int -> 
                   Int -> 
                   OptimizationResult (V.Vector a) a
gradientDescent' f grad x learningRate tolerance maxIter iter
  | iter >= maxIter = OptimizationResult x (f x) iter False 0.0
  | gradientNorm < tolerance = OptimizationResult x (f x) iter True 0.0
  | otherwise = 
      let gradX = grad x
          gradientNorm = V.sum $ V.map (\g -> g * g) gradX
          newX = V.zipWith (\xi gi -> xi - learningRate * gi) x gradX
      in gradientDescent' f grad newX learningRate tolerance maxIter (iter + 1)

-- 自适应学习率的梯度下降
adaptiveGradientDescent :: (Floating a, Ord a) => 
                          (V.Vector a -> a) -> 
                          (V.Vector a -> V.Vector a) -> 
                          V.Vector a -> 
                          a -> 
                          a -> 
                          Int -> 
                          OptimizationResult (V.Vector a) a
adaptiveGradientDescent f grad x0 initialLR tolerance maxIter = 
    adaptiveGradientDescent' f grad x0 initialLR tolerance maxIter 0

adaptiveGradientDescent' :: (Floating a, Ord a) => 
                           (V.Vector a -> a) -> 
                           (V.Vector a -> V.Vector a) -> 
                           V.Vector a -> 
                           a -> 
                           a -> 
                           Int -> 
                           Int -> 
                           OptimizationResult (V.Vector a) a
adaptiveGradientDescent' f grad x learningRate tolerance maxIter iter
  | iter >= maxIter = OptimizationResult x (f x) iter False 0.0
  | gradientNorm < tolerance = OptimizationResult x (f x) iter True 0.0
  | otherwise = 
      let gradX = grad x
          gradientNorm = V.sum $ V.map (\g -> g * g) gradX
          newX = V.zipWith (\xi gi -> xi - learningRate * gi) x gradX
          newLR = learningRate * 0.95  -- 学习率衰减
      in adaptiveGradientDescent' f grad newX newLR tolerance maxIter (iter + 1)

-- 示例：二次函数优化
quadraticFunction :: V.Vector Double -> Double
quadraticFunction x = 
    let x1 = x V.! 0
        x2 = x V.! 1
    in x1^2 + x2^2 + 2*x1*x2 + 2*x1 + 3*x2 + 1

quadraticGradient :: V.Vector Double -> V.Vector Double
quadraticGradient x = 
    let x1 = x V.! 0
        x2 = x V.! 1
        grad1 = 2*x1 + 2*x2 + 2
        grad2 = 2*x2 + 2*x1 + 3
    in V.fromList [grad1, grad2]

-- 复杂度分析
gradientDescentComplexity :: String
gradientDescentComplexity = 
    "时间复杂度: O(n * iter)\n" ++
    "空间复杂度: O(n)\n" ++
    "收敛性: 线性收敛\n" ++
    "应用: 机器学习、神经网络训练、凸优化"
```

#### 性能分析

**时间复杂度**：$O(n \cdot iter)$，其中 $n$ 是参数维度，$iter$ 是迭代次数
**空间复杂度**：$O(n)$
**收敛性**：线性收敛

### 2. 牛顿法

#### 形式化定义

牛顿法是一种二阶优化算法，利用目标函数的梯度和海森矩阵进行优化。

**算法描述**：
1. 初始化参数 $x_0$
2. 计算梯度 $\nabla f(x_k)$ 和海森矩阵 $\nabla^2 f(x_k)$
3. 求解线性方程组：$\nabla^2 f(x_k) \Delta x = -\nabla f(x_k)$
4. 更新参数：$x_{k+1} = x_k + \Delta x$
5. 重复步骤2-4直到收敛

#### Haskell实现

```haskell
-- 牛顿法算法
newtonMethod :: (Floating a, Ord a) => 
               (V.Vector a -> a) -> 
               (V.Vector a -> V.Vector a) -> 
               (V.Vector a -> [[a]]) -> 
               V.Vector a -> 
               a -> 
               Int -> 
               OptimizationResult (V.Vector a) a
newtonMethod f grad hess x0 tolerance maxIter = 
    newtonMethod' f grad hess x0 tolerance maxIter 0

newtonMethod' :: (Floating a, Ord a) => 
                (V.Vector a -> a) -> 
                (V.Vector a -> V.Vector a) -> 
                (V.Vector a -> [[a]]) -> 
                V.Vector a -> 
                a -> 
                Int -> 
                Int -> 
                OptimizationResult (V.Vector a) a
newtonMethod' f grad hess x tolerance maxIter iter
  | iter >= maxIter = OptimizationResult x (f x) iter False 0.0
  | gradientNorm < tolerance = OptimizationResult x (f x) iter True 0.0
  | otherwise = 
      let gradX = grad x
          hessX = hess x
          gradientNorm = V.sum $ V.map (\g -> g * g) gradX
          deltaX = solveLinearSystem hessX (V.map negate gradX)
          newX = V.zipWith (+) x deltaX
      in newtonMethod' f grad hess newX tolerance maxIter (iter + 1)

-- 求解线性方程组 Ax = b
solveLinearSystem :: (Floating a) => [[a]] -> V.Vector a -> V.Vector a
solveLinearSystem a b = 
    let n = length a
        augmented = zipWith (\row bi -> row ++ [bi]) a (V.toList b)
        reduced = gaussianElimination augmented
        solution = backSubstitution reduced
    in V.fromList solution

-- 高斯消元法
gaussianElimination :: (Floating a) => [[a]] -> [[a]]
gaussianElimination matrix = 
    let n = length matrix
    in gaussianElimination' matrix 0 n

gaussianElimination' :: (Floating a) => [[a]] -> Int -> Int -> [[a]]
gaussianElimination' matrix row n
  | row >= n = matrix
  | otherwise = 
      let pivot = findPivot matrix row
          newMatrix = swapRows matrix row pivot
          eliminatedMatrix = eliminateColumn newMatrix row
      in gaussianElimination' eliminatedMatrix (row + 1) n

-- 寻找主元
findPivot :: (Floating a) => [[a]] -> Int -> Int
findPivot matrix row = 
    let n = length matrix
        candidates = [(i, abs (matrix !! i !! row)) | i <- [row..n-1]]
    in fst $ maximumBy (\(_, a) (_, b) -> compare a b) candidates

-- 交换行
swapRows :: [[a]] -> Int -> Int -> [[a]]
swapRows matrix i j = 
    let rowI = matrix !! i
        rowJ = matrix !! j
    in take i matrix ++ [rowJ] ++ drop (i + 1) (take j matrix) ++ [rowI] ++ drop (j + 1) matrix

-- 消元
eliminateColumn :: (Floating a) => [[a]] -> Int -> [[a]]
eliminateColumn matrix row = 
    let n = length matrix
        pivot = matrix !! row !! row
        newRows = [eliminateRow matrix row i pivot | i <- [row+1..n-1]]
    in take row matrix ++ [matrix !! row] ++ newRows

eliminateRow :: (Floating a) => [[a]] -> Int -> Int -> a -> [a]
eliminateRow matrix pivotRow currentRow pivot = 
    let factor = matrix !! currentRow !! pivotRow / pivot
        pivotRowData = matrix !! pivotRow
        currentRowData = matrix !! currentRow
    in zipWith (\ci pi -> ci - factor * pi) currentRowData pivotRowData

-- 回代
backSubstitution :: (Floating a) => [[a]] -> [a]
backSubstitution matrix = 
    let n = length matrix
        solution = replicate n 0
    in backSubstitution' matrix solution (n - 1)

backSubstitution' :: (Floating a) => [[a]] -> [a] -> Int -> [a]
backSubstitution' matrix solution i
  | i < 0 = solution
  | otherwise = 
      let row = matrix !! i
          n = length matrix
          sum = sum [row !! j * solution !! j | j <- [i+1..n-1]]
          xi = (row !! n - sum) / row !! i
          newSolution = take i solution ++ [xi] ++ drop (i + 1) solution
      in backSubstitution' matrix newSolution (i - 1)

-- 示例：二次函数的海森矩阵
quadraticHessian :: V.Vector Double -> [[Double]]
quadraticHessian x = 
    [[2, 2],
     [2, 2]]

-- 复杂度分析
newtonMethodComplexity :: String
newtonMethodComplexity = 
    "时间复杂度: O(n³ * iter)\n" ++
    "空间复杂度: O(n²)\n" ++
    "收敛性: 二次收敛\n" ++
    "应用: 凸优化、机器学习、数值优化"
```

#### 性能分析

**时间复杂度**：$O(n^3 \cdot iter)$（主要开销在求解线性方程组）
**空间复杂度**：$O(n^2)$
**收敛性**：二次收敛

### 3. 遗传算法

#### 形式化定义

遗传算法是一种基于自然选择和遗传机制的优化算法，适用于复杂非线性优化问题。

**算法描述**：
1. 初始化种群
2. 评估适应度
3. 选择优秀个体
4. 交叉和变异
5. 重复步骤2-4直到满足终止条件

#### Haskell实现

```haskell
-- 遗传算法实现
data Individual a = Individual
    { chromosome :: V.Vector a
    , fitness :: Double
    }

data GeneticAlgorithm a = GeneticAlgorithm
    { populationSize :: Int
    , mutationRate :: Double
    , crossoverRate :: Double
    , maxGenerations :: Int
    }

-- 遗传算法主函数
geneticAlgorithm :: (Floating a, Ord a) => 
                   GeneticAlgorithm a -> 
                   (V.Vector a -> Double) -> 
                   (V.Vector a -> V.Vector a) -> 
                   V.Vector a -> 
                   OptimizationResult (V.Vector a) a
geneticAlgorithm config fitnessFunc mutationFunc initialChromosome = 
    let initialPopulation = generatePopulation config initialChromosome
    in geneticAlgorithm' config fitnessFunc mutationFunc initialPopulation 0

geneticAlgorithm' :: (Floating a, Ord a) => 
                    GeneticAlgorithm a -> 
                    (V.Vector a -> Double) -> 
                    (V.Vector a -> V.Vector a) -> 
                    [Individual a] -> 
                    Int -> 
                    OptimizationResult (V.Vector a) a
geneticAlgorithm' config fitnessFunc mutationFunc population generation
  | generation >= maxGenerations config = 
      let bestIndividual = maximumBy (\a b -> compare (fitness a) (fitness b)) population
      in OptimizationResult (chromosome bestIndividual) 
                           (fromIntegral $ fitness bestIndividual) 
                           generation True 0.0
  | otherwise = 
      let evaluatedPopulation = map (\ind -> ind { fitness = fitnessFunc (chromosome ind) }) population
          selectedPopulation = selection evaluatedPopulation
          newPopulation = crossoverAndMutation config selectedPopulation mutationFunc
      in geneticAlgorithm' config fitnessFunc mutationFunc newPopulation (generation + 1)

-- 生成初始种群
generatePopulation :: (Floating a) => GeneticAlgorithm a -> V.Vector a -> [Individual a]
generatePopulation config chromosome = 
    let size = populationSize config
        chromosomes = [mutateChromosome chromosome | _ <- [1..size]]
    in map (\chrom -> Individual chrom 0.0) chromosomes

-- 选择操作
selection :: [Individual a] -> [Individual a]
selection population = 
    let tournamentSize = 3
        selected = [tournamentSelection population tournamentSize | _ <- population]
    in selected

-- 锦标赛选择
tournamentSelection :: [Individual a] -> Int -> Individual a
tournamentSelection population size = 
    let n = length population
        indices = take size $ randomRs (0, n-1) (mkStdGen 42)
        candidates = [population !! i | i <- indices]
    in maximumBy (\a b -> compare (fitness a) (fitness b)) candidates

-- 交叉和变异
crossoverAndMutation :: (Floating a) => 
                       GeneticAlgorithm a -> 
                       [Individual a] -> 
                       (V.Vector a -> V.Vector a) -> 
                       [Individual a]
crossoverAndMutation config population mutationFunc = 
    let pairs = chunksOf 2 population
        crossed = concatMap (\pair -> 
            if length pair == 2 
            then crossover (pair !! 0) (pair !! 1) (crossoverRate config)
            else pair) pairs
        mutated = map (\ind -> mutate ind (mutationRate config) mutationFunc) crossed
    in mutated

-- 交叉操作
crossover :: Individual a -> Individual a -> Double -> [Individual a]
crossover parent1 parent2 rate = 
    let chrom1 = chromosome parent1
        chrom2 = chromosome parent2
        n = V.length chrom1
        crossoverPoint = floor $ fromIntegral n * rate
        child1 = V.take crossoverPoint chrom1 V.++ V.drop crossoverPoint chrom2
        child2 = V.take crossoverPoint chrom2 V.++ V.drop crossoverPoint chrom1
    in [Individual child1 0.0, Individual child2 0.0]

-- 变异操作
mutate :: (Floating a) => Individual a -> Double -> (V.Vector a -> V.Vector a) -> Individual a
mutate individual rate mutationFunc = 
    let chrom = chromosome individual
        shouldMutate = randomRs (0.0, 1.0) (mkStdGen 42) !! 0 < rate
    in if shouldMutate 
       then Individual (mutationFunc chrom) 0.0
       else individual

-- 变异函数示例
randomMutation :: V.Vector Double -> V.Vector Double
randomMutation chromosome = 
    let n = V.length chromosome
        mutations = take n $ randomRs (-0.1, 0.1) (mkStdGen 42)
    in V.zipWith (+) chromosome (V.fromList mutations)

-- 复杂度分析
geneticAlgorithmComplexity :: String
geneticAlgorithmComplexity = 
    "时间复杂度: O(pop_size * generations * fitness_eval)\n" ++
    "空间复杂度: O(pop_size * chromosome_length)\n" ++
    "收敛性: 概率性收敛\n" ++
    "应用: 组合优化、参数调优、工程设计"
```

#### 性能分析

**时间复杂度**：$O(pop\_size \cdot generations \cdot fitness\_eval)$
**空间复杂度**：$O(pop\_size \cdot chromosome\_length)$
**收敛性**：概率性收敛

### 4. 模拟退火算法

#### 形式化定义

模拟退火算法是一种基于物理退火过程的优化算法，能够跳出局部最优解。

**算法描述**：
1. 初始化温度和当前解
2. 生成邻域解
3. 根据Metropolis准则决定是否接受新解
4. 降低温度
5. 重复步骤2-4直到温度足够低

#### Haskell实现

```haskell
-- 模拟退火算法
data SimulatedAnnealing a = SimulatedAnnealing
    { initialTemperature :: Double
    , coolingRate :: Double
    , minTemperature :: Double
    , maxIterations :: Int
    }

-- 模拟退火主函数
simulatedAnnealing :: (Floating a, Ord a) => 
                     SimulatedAnnealing a -> 
                     (V.Vector a -> Double) -> 
                     (V.Vector a -> V.Vector a) -> 
                     V.Vector a -> 
                     OptimizationResult (V.Vector a) a
simulatedAnnealing config objectiveFunc neighborFunc initialSolution = 
    simulatedAnnealing' config objectiveFunc neighborFunc initialSolution 
                        (initialTemperature config) 0

simulatedAnnealing' :: (Floating a, Ord a) => 
                      SimulatedAnnealing a -> 
                      (V.Vector a -> Double) -> 
                      (V.Vector a -> V.Vector a) -> 
                      V.Vector a -> 
                      Double -> 
                      Int -> 
                      OptimizationResult (V.Vector a) a
simulatedAnnealing' config objectiveFunc neighborFunc currentSolution temperature iteration
  | temperature < minTemperature config = 
      OptimizationResult currentSolution (objectiveFunc currentSolution) iteration True 0.0
  | iteration >= maxIterations config = 
      OptimizationResult currentSolution (objectiveFunc currentSolution) iteration False 0.0
  | otherwise = 
      let neighborSolution = neighborFunc currentSolution
          currentCost = objectiveFunc currentSolution
          neighborCost = objectiveFunc neighborSolution
          deltaE = neighborCost - currentCost
          accepted = acceptSolution deltaE temperature
          newSolution = if accepted then neighborSolution else currentSolution
          newTemperature = temperature * coolingRate config
      in simulatedAnnealing' config objectiveFunc neighborFunc newSolution newTemperature (iteration + 1)

-- Metropolis准则
acceptSolution :: Double -> Double -> Bool
acceptSolution deltaE temperature = 
    if deltaE < 0 
    then True  -- 接受更好的解
    else let probability = exp (-deltaE / temperature)
             random = randomRs (0.0, 1.0) (mkStdGen 42) !! 0
         in random < probability

-- 邻域函数示例
randomNeighbor :: V.Vector Double -> V.Vector Double
randomNeighbor solution = 
    let n = V.length solution
        perturbations = take n $ randomRs (-0.1, 0.1) (mkStdGen 42)
    in V.zipWith (+) solution (V.fromList perturbations)

-- 复杂度分析
simulatedAnnealingComplexity :: String
simulatedAnnealingComplexity = 
    "时间复杂度: O(iterations * neighbor_generation)\n" ++
    "空间复杂度: O(solution_length)\n" ++
    "收敛性: 概率性收敛到全局最优\n" ++
    "应用: 组合优化、路径规划、调度问题"
```

#### 性能分析

**时间复杂度**：$O(iterations \cdot neighbor\_generation)$
**空间复杂度**：$O(solution\_length)$
**收敛性**：概率性收敛到全局最优

### 5. 粒子群优化 (PSO)

#### 形式化定义

粒子群优化是一种基于群体智能的优化算法，模拟鸟群觅食行为。

**算法描述**：
1. 初始化粒子群
2. 评估每个粒子的适应度
3. 更新个体最优和全局最优
4. 更新粒子速度和位置
5. 重复步骤2-4直到满足终止条件

#### Haskell实现

```haskell
-- 粒子群优化
data Particle a = Particle
    { position :: V.Vector a
    , velocity :: V.Vector a
    , bestPosition :: V.Vector a
    , bestFitness :: Double
    }

data PSOConfig a = PSOConfig
    { swarmSize :: Int
    , maxIterations :: Int
    , inertiaWeight :: Double
    , cognitiveWeight :: Double
    , socialWeight :: Double
    }

-- PSO主函数
particleSwarmOptimization :: (Floating a, Ord a) => 
                            PSOConfig a -> 
                            (V.Vector a -> Double) -> 
                            V.Vector a -> 
                            OptimizationResult (V.Vector a) a
particleSwarmOptimization config objectiveFunc initialPosition = 
    let initialSwarm = generateSwarm config initialPosition
    in particleSwarmOptimization' config objectiveFunc initialSwarm 0

particleSwarmOptimization' :: (Floating a, Ord a) => 
                             PSOConfig a -> 
                             (V.Vector a -> Double) -> 
                             [Particle a] -> 
                             Int -> 
                             OptimizationResult (V.Vector a) a
particleSwarmOptimization' config objectiveFunc swarm iteration
  | iteration >= maxIterations config = 
      let bestParticle = maximumBy (\a b -> compare (bestFitness a) (bestFitness b)) swarm
      in OptimizationResult (bestPosition bestParticle) 
                           (bestFitness bestParticle) 
                           iteration True 0.0
  | otherwise = 
      let evaluatedSwarm = map (\particle -> 
            let fitness = objectiveFunc (position particle)
            in particle { bestFitness = max (bestFitness particle) fitness,
                         bestPosition = if fitness > bestFitness particle 
                                       then position particle 
                                       else bestPosition particle }) swarm
          globalBest = maximumBy (\a b -> compare (bestFitness a) (bestFitness b)) evaluatedSwarm
          updatedSwarm = map (\particle -> updateParticle particle globalBest config) evaluatedSwarm
      in particleSwarmOptimization' config objectiveFunc updatedSwarm (iteration + 1)

-- 生成粒子群
generateSwarm :: (Floating a) => PSOConfig a -> V.Vector a -> [Particle a]
generateSwarm config initialPosition = 
    let size = swarmSize config
        n = V.length initialPosition
        particles = [generateParticle initialPosition n | _ <- [1..size]]
    in particles

-- 生成单个粒子
generateParticle :: V.Vector Double -> Int -> Particle Double
generateParticle initialPosition n = 
    let position = V.map (\x -> x + randomRs (-0.1, 0.1) (mkStdGen 42) !! 0) initialPosition
        velocity = V.fromList $ take n $ randomRs (-0.1, 0.1) (mkStdGen 42)
    in Particle position velocity position 0.0

-- 更新粒子
updateParticle :: (Floating a) => Particle a -> Particle a -> PSOConfig a -> Particle a
updateParticle particle globalBest config = 
    let newVelocity = updateVelocity particle globalBest config
        newPosition = V.zipWith (+) (position particle) newVelocity
    in particle { position = newPosition, velocity = newVelocity }

-- 更新速度
updateVelocity :: (Floating a) => Particle a -> Particle a -> PSOConfig a -> V.Vector a
updateVelocity particle globalBest config = 
    let r1 = randomRs (0.0, 1.0) (mkStdGen 42) !! 0
        r2 = randomRs (0.0, 1.0) (mkStdGen 42) !! 0
        cognitiveComponent = V.map (* (cognitiveWeight config * r1)) 
                                  (V.zipWith (-) (bestPosition particle) (position particle))
        socialComponent = V.map (* (socialWeight config * r2)) 
                               (V.zipWith (-) (bestPosition globalBest) (position particle))
        newVelocity = V.zipWith (+) 
                               (V.map (* (inertiaWeight config)) (velocity particle))
                               (V.zipWith (+) cognitiveComponent socialComponent)
    in newVelocity

-- 复杂度分析
psoComplexity :: String
psoComplexity = 
    "时间复杂度: O(swarm_size * iterations * fitness_eval)\n" ++
    "空间复杂度: O(swarm_size * dimension)\n" ++
    "收敛性: 概率性收敛\n" ++
    "应用: 函数优化、神经网络训练、参数调优"
```

#### 性能分析

**时间复杂度**：$O(swarm\_size \cdot iterations \cdot fitness\_eval)$
**空间复杂度**：$O(swarm\_size \cdot dimension)$
**收敛性**：概率性收敛

## 📊 算法比较

### 性能对比表

| 算法 | 时间复杂度 | 空间复杂度 | 收敛性 | 适用问题 |
|------|------------|------------|--------|----------|
| 梯度下降 | O(n * iter) | O(n) | 线性 | 凸优化 |
| 牛顿法 | O(n³ * iter) | O(n²) | 二次 | 凸优化 |
| 遗传算法 | O(pop * gen * eval) | O(pop * chrom) | 概率性 | 复杂优化 |
| 模拟退火 | O(iter * neighbor) | O(n) | 概率性 | 组合优化 |
| 粒子群优化 | O(swarm * iter * eval) | O(swarm * dim) | 概率性 | 连续优化 |

### 选择指南

```haskell
-- 算法选择函数
chooseOptimizationAlgorithm :: String -> String
chooseOptimizationAlgorithm "convex" = "梯度下降或牛顿法"
chooseOptimizationAlgorithm "combinatorial" = "遗传算法或模拟退火"
chooseOptimizationAlgorithm "continuous" = "粒子群优化"
chooseOptimizationAlgorithm "global" = "遗传算法、模拟退火或PSO"
chooseOptimizationAlgorithm _ = "根据具体问题选择"

-- 智能算法选择
smartOptimizationAlgorithm :: String -> String -> String
smartOptimizationAlgorithm "type" "convex" = "梯度下降"
smartOptimizationAlgorithm "type" "nonconvex" = "遗传算法"
smartOptimizationAlgorithm "dimension" "low" = "牛顿法"
smartOptimizationAlgorithm "dimension" "high" = "粒子群优化"
smartOptimizationAlgorithm "constraint" "discrete" = "遗传算法"
smartOptimizationAlgorithm "constraint" "continuous" = "梯度下降"
smartOptimizationAlgorithm _ _ = "需要更多信息"
```

## 🔬 形式化验证

### 收敛性证明

#### 梯度下降收敛性

**定理**：对于凸函数，梯度下降算法收敛到全局最优解。

**证明**：
1. **凸性条件**：$f(\lambda x + (1-\lambda)y) \leq \lambda f(x) + (1-\lambda)f(y)$
2. **Lipschitz连续性**：$\|\nabla f(x) - \nabla f(y)\| \leq L\|x - y\|$
3. **收敛性**：选择合适的步长，算法收敛到最优解

#### 牛顿法收敛性

**定理**：对于强凸函数，牛顿法具有二次收敛性。

**证明**：
1. **强凸性**：$\nabla^2 f(x) \succeq \mu I$
2. **Lipschitz连续性**：$\|\nabla^2 f(x) - \nabla^2 f(y)\| \leq M\|x - y\|$
3. **二次收敛**：$\|x_{k+1} - x^*\| \leq \frac{M}{2\mu}\|x_k - x^*\|^2$

### 复杂度证明

#### 遗传算法复杂度

**定理**：遗传算法的期望收敛时间为 $O(pop\_size \cdot \log(pop\_size) \cdot generations)$。

**证明**：
- 选择操作：$O(pop\_size \cdot \log(pop\_size))$
- 交叉操作：$O(pop\_size)$
- 变异操作：$O(pop\_size)$
- 总复杂度：$O(pop\_size \cdot \log(pop\_size) \cdot generations)$

## 🎯 实际应用

### 性能测试

```haskell
-- 性能测试函数
testOptimizationPerformance :: IO ()
testOptimizationPerformance = do
    putStrLn "优化算法性能测试"
    putStrLn "=================="
    
    let testAlgorithm name algFunc = do
            start <- getCurrentTime
            let result = algFunc
            end <- getCurrentTime
            let duration = diffUTCTime end start
            putStrLn $ name ++ ": " ++ show duration
    
    -- 测试梯度下降
    let x0 = V.fromList [1.0, 1.0]
        gdResult = gradientDescent quadraticFunction quadraticGradient x0 0.01 1e-6 1000
    testAlgorithm "梯度下降" gdResult
    
    -- 测试遗传算法
    let gaConfig = GeneticAlgorithm 50 0.1 0.8 100
        gaResult = geneticAlgorithm gaConfig quadraticFunction randomMutation x0
    testAlgorithm "遗传算法" gaResult

-- 基准函数
rosenbrockFunction :: V.Vector Double -> Double
rosenbrockFunction x = 
    let x1 = x V.! 0
        x2 = x V.! 1
    in (1 - x1)^2 + 100 * (x2 - x1^2)^2

sphereFunction :: V.Vector Double -> Double
sphereFunction x = V.sum $ V.map (\xi -> xi^2) x
```

### 实际应用场景

1. **机器学习**：神经网络训练、参数优化
2. **金融优化**：投资组合优化、风险最小化
3. **工程设计**：结构优化、参数调优
4. **运筹学**：调度问题、路径规划
5. **生物信息学**：蛋白质折叠、序列比对

## 📚 扩展阅读

### 高级优化算法

1. **内点法**：处理约束优化问题
2. **信赖域方法**：非线性优化
3. **进化策略**：连续参数优化
4. **蚁群算法**：组合优化
5. **差分进化**：全局优化

### 并行优化算法

```haskell
-- 并行遗传算法
parallelGeneticAlgorithm :: (Floating a, Ord a) => 
                           GeneticAlgorithm a -> 
                           (V.Vector a -> Double) -> 
                           V.Vector a -> 
                           OptimizationResult (V.Vector a) a
parallelGeneticAlgorithm config fitnessFunc initialChromosome = 
    let initialPopulation = generatePopulation config initialChromosome
        chunks = chunksOf (populationSize config `div` numCapabilities) initialPopulation
    in parallelGeneticAlgorithm' config fitnessFunc chunks 0

parallelGeneticAlgorithm' :: (Floating a, Ord a) => 
                            GeneticAlgorithm a -> 
                            (V.Vector a -> Double) -> 
                            [[Individual a]] -> 
                            Int -> 
                            OptimizationResult (V.Vector a) a
parallelGeneticAlgorithm' config fitnessFunc populationChunks generation
  | generation >= maxGenerations config = 
      let allIndividuals = concat populationChunks
          bestIndividual = maximumBy (\a b -> compare (fitness a) (fitness b)) allIndividuals
      in OptimizationResult (chromosome bestIndividual) 
                           (fromIntegral $ fitness bestIndividual) 
                           generation True 0.0
  | otherwise = 
      let evaluatedChunks = map (\chunk -> 
            map (\ind -> ind { fitness = fitnessFunc (chromosome ind) }) chunk) populationChunks
          evolvedChunks = map (\chunk -> 
            crossoverAndMutation config chunk randomMutation) evaluatedChunks
      in parallelGeneticAlgorithm' config fitnessFunc evolvedChunks (generation + 1)
```

## 🔗 相关链接

- [基础数据结构](../01-Haskell-Basics/01-Language-Features.md)
- [高级数据结构](../03-Data-Structures/01-Advanced-Data-Structures.md)
- [形式化证明](../04-Formal-Proofs/01-Theorem-Proving.md)
- [性能优化](../05-Performance-Optimization/01-Memory-Optimization.md)

---

*本文档提供了优化算法的完整形式化理论和Haskell实现，包括性能分析和实际应用指导。* 