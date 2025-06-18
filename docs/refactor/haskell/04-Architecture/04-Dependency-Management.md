# 依赖管理 (Dependency Management)

## 概述

Haskell的依赖管理是确保项目正确构建和运行的核心机制，涉及版本解析、冲突解决、依赖图构建等复杂问题。本文档系统性介绍Haskell依赖管理的理论基础、数学模型和实际应用。

## 目录

1. [基本概念](#基本概念)
2. [依赖图](#依赖图)
3. [版本解析](#版本解析)
4. [冲突解决](#冲突解决)
5. [Haskell实现](#haskell实现)
6. [最佳实践](#最佳实践)

## 基本概念

### 定义 4.4.1: 依赖 (Dependency)

依赖是项目对其他包或模块的引用关系，包含版本约束和类型信息。

### 定义 4.4.2: 依赖管理 (Dependency Management)

依赖管理是解析、安装和更新项目依赖的过程，确保依赖关系的正确性和一致性。

### 依赖的数学定义

依赖可以表示为：
$$D = (S, T, V, C)$$

其中：

- $S$ 是源包
- $T$ 是目标包
- $V$ 是版本约束
- $C$ 是约束类型

## 依赖图

### 依赖图结构

```haskell
-- 依赖图
data DependencyGraph = DependencyGraph
  { nodes :: Map PackageName PackageNode
  , edges :: Map PackageName [DependencyEdge]
  , metadata :: GraphMetadata
  }

-- 包节点
data PackageNode = PackageNode
  { packageName :: PackageName
  , packageVersion :: Version
  , packageType :: PackageType
  , packageDependencies :: [DependencyEdge]
  , packageConflicts :: [PackageName]
  }

-- 依赖边
data DependencyEdge = DependencyEdge
  { sourcePackage :: PackageName
  , targetPackage :: PackageName
  , versionConstraint :: VersionConstraint
  , edgeType :: EdgeType
  , isOptional :: Bool
  }

-- 边类型
data EdgeType = 
    DirectDependency
  | TransitiveDependency
  | DevelopmentDependency
  | OptionalDependency

-- 图元数据
data GraphMetadata = GraphMetadata
  { totalPackages :: Int
  , totalDependencies :: Int
  , maxDepth :: Int
  , hasCycles :: Bool
  , hasConflicts :: Bool
  }

-- 构建依赖图
buildDependencyGraph :: [PackageInfo] -> DependencyGraph
buildDependencyGraph packages = DependencyGraph
  { nodes = Map.fromList [(packageName pkg, createNode pkg) | pkg <- packages]
  , edges = buildEdges packages
  , metadata = calculateMetadata packages
  }

-- 创建节点
createNode :: PackageInfo -> PackageNode
createNode pkg = PackageNode
  { packageName = packageName pkg
  , packageVersion = packageVersion pkg
  , packageType = Library
  , packageDependencies = []
  , packageConflicts = []
  }

-- 构建边
buildEdges :: [PackageInfo] -> Map PackageName [DependencyEdge]
buildEdges packages = Map.fromList
  [(packageName pkg, map (createEdge pkg) (dependencies pkg)) | pkg <- packages]

-- 创建边
createEdge :: PackageInfo -> Dependency -> DependencyEdge
createEdge pkg dep = DependencyEdge
  { sourcePackage = packageName pkg
  , targetPackage = depName dep
  , versionConstraint = versionConstraint dep
  , edgeType = DirectDependency
  , isOptional = False
  }
```

### 图分析

```haskell
-- 图分析器
data GraphAnalyzer = GraphAnalyzer
  { dependencyGraph :: DependencyGraph
  , analysisResults :: AnalysisResults
  }

-- 分析结果
data AnalysisResults = AnalysisResults
  { cycles :: [[PackageName]]
  , conflicts :: [DependencyConflict]
  , unusedDependencies :: [PackageName]
  , criticalPath :: [PackageName]
  }

-- 分析依赖图
analyzeDependencyGraph :: DependencyGraph -> AnalysisResults
analyzeDependencyGraph graph = AnalysisResults
  { cycles = findCycles graph
  , conflicts = findConflicts graph
  , unusedDependencies = findUnusedDependencies graph
  , criticalPath = findCriticalPath graph
  }

-- 查找循环依赖
findCycles :: DependencyGraph -> [[PackageName]]
findCycles graph = 
  let edges = Map.toList (edges graph)
  in detectCycles edges

-- 检测循环
detectCycles :: [(PackageName, [DependencyEdge])] -> [[PackageName]]
detectCycles edges = 
  -- 使用深度优先搜索检测循环
  let graph = buildAdjacencyList edges
  in findCyclesDFS graph

-- 构建邻接表
buildAdjacencyList :: [(PackageName, [DependencyEdge])] -> Map PackageName [PackageName]
buildAdjacencyList edges = Map.fromList
  [(pkg, map targetPackage deps) | (pkg, deps) <- edges]

-- 深度优先搜索查找循环
findCyclesDFS :: Map PackageName [PackageName] -> [[PackageName]]
findCyclesDFS graph = 
  let allNodes = Map.keys graph
  in concatMap (\node -> findCyclesFromNode graph node) allNodes

-- 从节点查找循环
findCyclesFromNode :: Map PackageName [PackageName] -> PackageName -> [[PackageName]]
findCyclesFromNode graph start = 
  dfs graph start start [] []

-- 深度优先搜索
dfs :: Map PackageName [PackageName] -> PackageName -> PackageName -> [PackageName] -> [[PackageName]] -> [[PackageName]]
dfs graph current start path cycles
  | current == start && not (null path) = cycles ++ [path]
  | current `elem` path = cycles
  | otherwise = 
      let neighbors = Map.findWithDefault [] current graph
          newPath = path ++ [current]
      in foldl (\acc neighbor -> dfs graph neighbor start newPath acc) cycles neighbors
```

## 版本解析

### 版本约束解析

```haskell
-- 版本解析器
data VersionResolver = VersionResolver
  { availableVersions :: Map PackageName [Version]
  , resolutionStrategy :: ResolutionStrategy
  , conflictResolution :: ConflictResolution
  }

-- 解析策略
data ResolutionStrategy = 
    LatestCompatible
  | EarliestCompatible
  | PinnedVersion
  | SemanticVersioning

-- 冲突解决策略
data ConflictResolution = 
    FailOnConflict
  | UseLatest
  | UseEarliest
  | ManualResolution

-- 解析依赖
resolveDependencies :: VersionResolver -> [Dependency] -> Either String [ResolvedDependency]
resolveDependencies resolver deps = do
  resolved <- mapM (resolveDependency resolver) deps
  validateResolution resolved
  return resolved

-- 解析单个依赖
resolveDependency :: VersionResolver -> Dependency -> Either String ResolvedDependency
resolveDependency resolver dep = do
  let candidates = Map.findWithDefault [] (depName dep) (availableVersions resolver)
  let compatible = filter (\v -> satisfiesConstraint v (versionConstraint dep)) candidates
  case compatible of
    [] -> Left $ "No compatible version found for " ++ depName dep
    versions -> do
      let selected = selectVersion (resolutionStrategy resolver) versions
      return ResolvedDependency
        { resolvedPackage = depName dep
        , resolvedVersion = selected
        , originalConstraint = versionConstraint dep
        }

-- 选择版本
selectVersion :: ResolutionStrategy -> [Version] -> Version
selectVersion strategy versions = case strategy of
  LatestCompatible -> maximum versions
  EarliestCompatible -> minimum versions
  PinnedVersion -> head versions
  SemanticVersioning -> selectSemanticVersion versions

-- 选择语义化版本
selectSemanticVersion :: [Version] -> Version
selectSemanticVersion versions = 
  let stableVersions = filter isStableVersion versions
  in if null stableVersions then maximum versions else maximum stableVersions

-- 检查稳定版本
isStableVersion :: Version -> Bool
isStableVersion version = 
  -- 简化实现，实际会检查预发布标识
  True

-- 验证解析结果
validateResolution :: [ResolvedDependency] -> Either String ()
validateResolution resolved = do
  -- 检查版本冲突
  let conflicts = findVersionConflicts resolved
  when (not (null conflicts)) $ Left $ "Version conflicts: " ++ show conflicts
  return ()

-- 查找版本冲突
findVersionConflicts :: [ResolvedDependency] -> [DependencyConflict]
findVersionConflicts resolved = 
  let grouped = groupBy resolvedPackage resolved
  in concatMap checkGroupConflicts grouped

-- 检查组冲突
checkGroupConflicts :: [ResolvedDependency] -> [DependencyConflict]
checkGroupConflicts group
  | length group <= 1 = []
  | otherwise = 
      let versions = map resolvedVersion group
          uniqueVersions = nub versions
      in if length uniqueVersions > 1
         then [DependencyConflict (resolvedPackage (head group)) uniqueVersions]
         else []
```

### 约束求解

```haskell
-- 约束求解器
data ConstraintSolver = ConstraintSolver
  { constraints :: [VersionConstraint]
  , variables :: Map PackageName Version
  , solution :: Maybe (Map PackageName Version)
  }

-- 求解约束
solveConstraints :: [VersionConstraint] -> Map PackageName [Version] -> Either String (Map PackageName Version)
solveConstraints constraints availableVersions = do
  let solver = ConstraintSolver constraints Map.empty Nothing
  solution <- solveConstraintsRecursive solver availableVersions
  return solution

-- 递归求解约束
solveConstraintsRecursive :: ConstraintSolver -> Map PackageName [Version] -> Either String (Map PackageName Version)
solveConstraintsRecursive solver availableVersions
  | allConstraintsSatisfied solver = return (variables solver)
  | otherwise = do
      let unsolved = findUnsolvedConstraints solver
      case unsolved of
        [] -> return (variables solver)
        (constraint:_) -> do
          let candidates = getCandidates constraint availableVersions
          tryCandidates solver constraint candidates availableVersions

-- 检查所有约束是否满足
allConstraintsSatisfied :: ConstraintSolver -> Bool
allConstraintsSatisfied solver = 
  all (\constraint -> isConstraintSatisfied constraint (variables solver)) (constraints solver)

-- 检查约束是否满足
isConstraintSatisfied :: VersionConstraint -> Map PackageName Version -> Bool
isConstraintSatisfied constraint vars = 
  -- 简化实现，实际会检查具体的约束逻辑
  True

-- 查找未解决的约束
findUnsolvedConstraints :: ConstraintSolver -> [VersionConstraint]
findUnsolvedConstraints solver = 
  filter (\constraint -> not (isConstraintSatisfied constraint (variables solver))) (constraints solver)

-- 获取候选版本
getCandidates :: VersionConstraint -> Map PackageName [Version] -> [Version]
getCandidates constraint availableVersions = 
  -- 简化实现，实际会根据约束类型获取候选版本
  []

-- 尝试候选版本
tryCandidates :: ConstraintSolver -> VersionConstraint -> [Version] -> Map PackageName [Version] -> Either String (Map PackageName Version)
tryCandidates solver constraint candidates availableVersions = 
  -- 简化实现，实际会尝试每个候选版本
  Left "No valid solution found"
```

## 冲突解决

### 冲突检测

```haskell
-- 依赖冲突
data DependencyConflict = DependencyConflict
  { conflictPackage :: PackageName
  , conflictVersions :: [Version]
  , conflictType :: ConflictType
  , conflictSeverity :: ConflictSeverity
  }

-- 冲突类型
data ConflictType = 
    VersionConflict
  | TransitiveConflict
  | CircularConflict
  | PlatformConflict

-- 冲突严重程度
data ConflictSeverity = 
    Low
  | Medium
  | High
  | Critical

-- 冲突检测器
data ConflictDetector = ConflictDetector
  { dependencyGraph :: DependencyGraph
  , detectionRules :: [DetectionRule]
  }

-- 检测规则
data DetectionRule = DetectionRule
  { ruleName :: String
  , ruleCondition :: ConflictCondition
  , ruleAction :: ConflictAction
  }

-- 冲突条件
data ConflictCondition = 
    VersionMismatch PackageName [Version]
  | CircularDependency [PackageName]
  | PlatformIncompatibility String

-- 冲突动作
data ConflictAction = 
    FailBuild
  | AutoResolve
  | WarnUser
  | IgnoreConflict

-- 检测冲突
detectConflicts :: ConflictDetector -> [DependencyConflict]
detectConflicts detector = 
  concatMap (applyDetectionRule detector) (detectionRules detector)

-- 应用检测规则
applyDetectionRule :: ConflictDetector -> DetectionRule -> [DependencyConflict]
applyDetectionRule detector rule = 
  case ruleCondition rule of
    VersionMismatch pkg versions -> 
      if hasVersionMismatch (dependencyGraph detector) pkg versions
      then [DependencyConflict pkg versions VersionConflict High]
      else []
    CircularDependency pkgs -> 
      if hasCircularDependency (dependencyGraph detector) pkgs
      then [DependencyConflict (head pkgs) [] CircularConflict Critical]
      else []
    PlatformIncompatibility platform -> 
      if hasPlatformConflict (dependencyGraph detector) platform
      then [DependencyConflict "" [] PlatformConflict Medium]
      else []

-- 检查版本不匹配
hasVersionMismatch :: DependencyGraph -> PackageName -> [Version] -> Bool
hasVersionMismatch graph pkg versions = 
  case Map.lookup pkg (nodes graph) of
    Nothing -> False
    Just node -> packageVersion node `notElem` versions

-- 检查循环依赖
hasCircularDependency :: DependencyGraph -> [PackageName] -> Bool
hasCircularDependency graph pkgs = 
  -- 简化实现，实际会检查是否存在循环依赖
  False

-- 检查平台冲突
hasPlatformConflict :: DependencyGraph -> String -> Bool
hasPlatformConflict graph platform = 
  -- 简化实现，实际会检查平台兼容性
  False
```

### 冲突解决策略

```haskell
-- 冲突解决器
data ConflictResolver = ConflictResolver
  { resolutionStrategy :: ResolutionStrategy
  , resolutionRules :: [ResolutionRule]
  , manualResolutions :: Map PackageName Version
  }

-- 解决规则
data ResolutionRule = ResolutionRule
  { ruleName :: String
  , rulePriority :: Int
  , ruleCondition :: ConflictCondition
  , ruleResolution :: ConflictResolution
  }

-- 解决冲突
resolveConflicts :: ConflictResolver -> [DependencyConflict] -> Either String [ResolvedDependency]
resolveConflicts resolver conflicts = do
  resolved <- mapM (resolveConflict resolver) conflicts
  return resolved

-- 解决单个冲突
resolveConflict :: ConflictResolver -> DependencyConflict -> Either String ResolvedDependency
resolveConflict resolver conflict = do
  let applicableRules = filter (\rule -> matchesCondition (ruleCondition rule) conflict) (resolutionRules resolver)
  let sortedRules = sortBy (\a b -> compare (rulePriority b) (rulePriority a)) applicableRules
  case sortedRules of
    [] -> applyDefaultResolution resolver conflict
    (rule:_) -> applyResolutionRule rule conflict

-- 检查条件匹配
matchesCondition :: ConflictCondition -> DependencyConflict -> Bool
matchesCondition condition conflict = case condition of
  VersionMismatch pkg _ -> conflictPackage conflict == pkg
  CircularDependency _ -> conflictType conflict == CircularConflict
  PlatformIncompatibility _ -> conflictType conflict == PlatformConflict

-- 应用默认解决
applyDefaultResolution :: ConflictResolver -> DependencyConflict -> Either String ResolvedDependency
applyDefaultResolution resolver conflict = 
  case resolutionStrategy resolver of
    UseLatest -> 
      let latestVersion = maximum (conflictVersions conflict)
      in return ResolvedDependency (conflictPackage conflict) latestVersion AnyVersion
    UseEarliest -> 
      let earliestVersion = minimum (conflictVersions conflict)
      in return ResolvedDependency (conflictPackage conflict) earliestVersion AnyVersion
    _ -> Left $ "Cannot resolve conflict for " ++ conflictPackage conflict

-- 应用解决规则
applyResolutionRule :: ResolutionRule -> DependencyConflict -> Either String ResolvedDependency
applyResolutionRule rule conflict = 
  case ruleResolution rule of
    FailBuild -> Left $ "Build failed due to conflict: " ++ conflictPackage conflict
    AutoResolve -> applyDefaultResolution (ConflictResolver UseLatest [] Map.empty) conflict
    WarnUser -> applyDefaultResolution (ConflictResolver UseLatest [] Map.empty) conflict
    IgnoreConflict -> Left $ "Conflict ignored: " ++ conflictPackage conflict
```

## Haskell实现

### 综合示例

```haskell
-- 依赖管理模块
module DependencyManagement where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub, sortBy, groupBy)
import Data.Maybe (fromMaybe)

-- 包名类型
type PackageName = String

-- 版本
data Version = Version
  { major :: Int
  , minor :: Int
  , patch :: Int
  } deriving (Show, Eq, Ord)

-- 版本约束
data VersionConstraint = 
    AnyVersion
  | ThisVersion Version
  | LaterVersion Version
  | EarlierVersion Version
  | UnionVersion VersionConstraint VersionConstraint
  | IntersectVersion VersionConstraint VersionConstraint
  deriving (Show, Eq)

-- 依赖
data Dependency = Dependency
  { depName :: PackageName
  , versionConstraint :: VersionConstraint
  } deriving (Show, Eq)

-- 已解析依赖
data ResolvedDependency = ResolvedDependency
  { resolvedPackage :: PackageName
  , resolvedVersion :: Version
  , originalConstraint :: VersionConstraint
  } deriving (Show, Eq)

-- 依赖冲突
data DependencyConflict = DependencyConflict
  { conflictPackage :: PackageName
  , conflictVersions :: [Version]
  , conflictType :: ConflictType
  , conflictSeverity :: ConflictSeverity
  } deriving (Show, Eq)

-- 冲突类型
data ConflictType = 
    VersionConflict
  | TransitiveConflict
  | CircularConflict
  | PlatformConflict
  deriving (Show, Eq)

-- 冲突严重程度
data ConflictSeverity = 
    Low
  | Medium
  | High
  | Critical
  deriving (Show, Eq)

-- 依赖管理器
data DependencyManager = DependencyManager
  { availablePackages :: Map PackageName [Version]
  , installedPackages :: Map PackageName Version
  , dependencyGraph :: DependencyGraph
  }

-- 依赖图
data DependencyGraph = DependencyGraph
  { nodes :: Map PackageName PackageNode
  , edges :: Map PackageName [DependencyEdge]
  } deriving (Show, Eq)

-- 包节点
data PackageNode = PackageNode
  { packageName :: PackageName
  , packageVersion :: Version
  , packageDependencies :: [DependencyEdge]
  } deriving (Show, Eq)

-- 依赖边
data DependencyEdge = DependencyEdge
  { sourcePackage :: PackageName
  , targetPackage :: PackageName
  , versionConstraint :: VersionConstraint
  } deriving (Show, Eq)

-- 创建依赖管理器
createDependencyManager :: DependencyManager
createDependencyManager = DependencyManager
  { availablePackages = Map.empty
  , installedPackages = Map.empty
  , dependencyGraph = DependencyGraph Map.empty Map.empty
  }

-- 添加可用包
addAvailablePackage :: DependencyManager -> PackageName -> [Version] -> DependencyManager
addAvailablePackage manager pkg versions = manager
  { availablePackages = Map.insert pkg versions (availablePackages manager)
  }

-- 解析依赖
resolveDependencies :: DependencyManager -> [Dependency] -> Either String [ResolvedDependency]
resolveDependencies manager deps = do
  resolved <- mapM (resolveDependency manager) deps
  validateResolution resolved
  return resolved

-- 解析单个依赖
resolveDependency :: DependencyManager -> Dependency -> Either String ResolvedDependency
resolveDependency manager dep = do
  let candidates = Map.findWithDefault [] (depName dep) (availablePackages manager)
  let compatible = filter (\v -> satisfiesConstraint v (versionConstraint dep)) candidates
  case compatible of
    [] -> Left $ "No compatible version found for " ++ depName dep
    versions -> do
      let selected = maximum versions  -- 使用最新版本
      return ResolvedDependency
        { resolvedPackage = depName dep
        , resolvedVersion = selected
        , originalConstraint = versionConstraint dep
        }

-- 检查版本约束
satisfiesConstraint :: Version -> VersionConstraint -> Bool
satisfiesConstraint version constraint = case constraint of
  AnyVersion -> True
  ThisVersion v -> version == v
  LaterVersion v -> version > v
  EarlierVersion v -> version < v
  UnionVersion c1 c2 -> satisfiesConstraint version c1 || satisfiesConstraint version c2
  IntersectVersion c1 c2 -> satisfiesConstraint version c1 && satisfiesConstraint version c2

-- 验证解析结果
validateResolution :: [ResolvedDependency] -> Either String ()
validateResolution resolved = do
  let conflicts = findVersionConflicts resolved
  when (not (null conflicts)) $ Left $ "Version conflicts: " ++ show conflicts
  return ()

-- 查找版本冲突
findVersionConflicts :: [ResolvedDependency] -> [DependencyConflict]
findVersionConflicts resolved = 
  let grouped = groupBy (\a b -> resolvedPackage a == resolvedPackage b) resolved
  in concatMap checkGroupConflicts grouped

-- 检查组冲突
checkGroupConflicts :: [ResolvedDependency] -> [DependencyConflict]
checkGroupConflicts group
  | length group <= 1 = []
  | otherwise = 
      let versions = map resolvedVersion group
          uniqueVersions = nub versions
      in if length uniqueVersions > 1
         then [DependencyConflict (resolvedPackage (head group)) uniqueVersions VersionConflict High]
         else []

-- 安装依赖
installDependencies :: DependencyManager -> [ResolvedDependency] -> DependencyManager
installDependencies manager deps = manager
  { installedPackages = foldl (\acc dep -> Map.insert (resolvedPackage dep) (resolvedVersion dep) acc) 
                              (installedPackages manager) deps
  }

-- 更新依赖图
updateDependencyGraph :: DependencyManager -> [ResolvedDependency] -> DependencyManager
updateDependencyGraph manager deps = manager
  { dependencyGraph = buildDependencyGraph deps
  }

-- 构建依赖图
buildDependencyGraph :: [ResolvedDependency] -> DependencyGraph
buildDependencyGraph deps = DependencyGraph
  { nodes = Map.fromList [(resolvedPackage dep, createNode dep) | dep <- deps]
  , edges = Map.empty  -- 简化实现
  }

-- 创建节点
createNode :: ResolvedDependency -> PackageNode
createNode dep = PackageNode
  { packageName = resolvedPackage dep
  , packageVersion = resolvedVersion dep
  , packageDependencies = []
  }

-- 检查依赖状态
checkDependencyStatus :: DependencyManager -> PackageName -> Maybe Version
checkDependencyStatus manager pkg = Map.lookup pkg (installedPackages manager)

-- 列出已安装依赖
listInstalledDependencies :: DependencyManager -> [ResolvedDependency]
listInstalledDependencies manager = 
  map (\(pkg, version) -> ResolvedDependency pkg version AnyVersion) 
      (Map.toList (installedPackages manager))
```

### 实际应用示例

```haskell
-- 示例依赖管理器
sampleDependencyManager :: DependencyManager
sampleDependencyManager = 
  let manager = createDependencyManager
  in foldl (\acc (pkg, versions) -> addAvailablePackage acc pkg versions) manager
       [ ("base", [Version 4 16 0, Version 4 17 0, Version 4 18 0])
       , ("containers", [Version 0 6 5, Version 0 6 6, Version 0 6 7])
       , ("text", [Version 1 2 4, Version 1 2 5, Version 2 0 0])
       , ("aeson", [Version 1 5 6, Version 2 0 0, Version 2 1 0])
       ]

-- 示例依赖
sampleDependencies :: [Dependency]
sampleDependencies = 
  [ Dependency "base" (LaterVersion (Version 4 16 0))
  , Dependency "containers" AnyVersion
  , Dependency "text" (LaterVersion (Version 1 2 0))
  , Dependency "aeson" (LaterVersion (Version 1 5 0))
  ]

-- 依赖管理示例
dependencyManagementExample :: IO ()
dependencyManagementExample = do
  putStrLn "Dependency Management Demo"
  
  -- 创建依赖管理器
  let manager = sampleDependencyManager
  
  -- 解析依赖
  case resolveDependencies manager sampleDependencies of
    Left err -> putStrLn $ "Dependency resolution failed: " ++ err
    Right resolved -> do
      putStrLn "Dependencies resolved successfully:"
      mapM_ (\dep -> putStrLn $ "  " ++ resolvedPackage dep ++ " v" ++ show (resolvedVersion dep)) resolved
      
      -- 安装依赖
      let manager' = installDependencies manager resolved
      
      -- 更新依赖图
      let manager'' = updateDependencyGraph manager' resolved
      
      -- 检查依赖状态
      putStrLn "\nInstalled dependencies:"
      let installed = listInstalledDependencies manager''
      mapM_ (\dep -> putStrLn $ "  " ++ resolvedPackage dep ++ " v" ++ show (resolvedVersion dep)) installed
      
      -- 检查特定依赖
      case checkDependencyStatus manager'' "base" of
        Nothing -> putStrLn "base package not found"
        Just version -> putStrLn $ "base package version: " ++ show version
```

### 冲突解决示例

```haskell
-- 冲突解决示例
conflictResolutionExample :: IO ()
conflictResolutionExample = do
  putStrLn "Conflict Resolution Demo"
  
  -- 创建有冲突的依赖
  let conflictingDeps = 
        [ ResolvedDependency "conflicting-package" (Version 1 0 0) AnyVersion
        , ResolvedDependency "conflicting-package" (Version 2 0 0) AnyVersion
        ]
  
  -- 检测冲突
  let conflicts = findVersionConflicts conflictingDeps
  putStrLn $ "Detected conflicts: " ++ show conflicts
  
  -- 解决冲突
  case conflicts of
    [] -> putStrLn "No conflicts found"
    (conflict:_) -> do
      putStrLn $ "Resolving conflict for " ++ conflictPackage conflict
      putStrLn $ "Available versions: " ++ show (conflictVersions conflict)
      
      -- 选择最新版本
      let latestVersion = maximum (conflictVersions conflict)
      putStrLn $ "Selected version: " ++ show latestVersion
      
      -- 创建解决后的依赖
      let resolved = ResolvedDependency (conflictPackage conflict) latestVersion AnyVersion
      putStrLn $ "Resolved dependency: " ++ show resolved
```

## 最佳实践

1. **版本约束**: 使用明确的版本约束，避免过于宽松的约束。
2. **依赖最小化**: 只包含必要的依赖，避免过度依赖。
3. **冲突检测**: 定期检查依赖冲突，及时解决。
4. **版本锁定**: 在生产环境中锁定依赖版本。
5. **依赖更新**: 定期更新依赖，保持安全性。

## 相关链接

- [模块系统](./01-Module-System.md)
- [包管理](./02-Package-Management.md)
- [项目结构](./03-Project-Structure.md)

---

**作者**: 形式化知识体系重构项目  
**最后更新**: 2024年12月  
**版本**: 1.0
