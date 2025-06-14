# 层次Petri网 (Hierarchical Petri Nets)

## 概述

层次Petri网是Petri网的重要扩展，通过引入层次化结构和模块化概念，使得Petri网能够建模复杂的系统，同时保持模型的清晰性和可维护性。

## 形式化定义

### 基本概念

```haskell
-- 层次结构
data Hierarchy = Hierarchy
  { level :: Int
  , parent :: Maybe Hierarchy
  , children :: [Hierarchy]
  , modules :: [PetriNetModule]
  }

-- Petri网模块
data PetriNetModule = PetriNetModule
  { moduleId :: String
  , places :: Set Place
  , transitions :: Set Transition
  , arcs :: Set Arc
  , interfaces :: [Interface]
  , subModules :: [PetriNetModule]
  }

-- 接口
data Interface = Interface
  { interfaceId :: String
  , inputPlaces :: Set Place
  , outputPlaces :: Set Place
  , inputTransitions :: Set Transition
  , outputTransitions :: Set Transition
  }

-- 层次Petri网
data HierarchicalPetriNet = HierarchicalPetriNet
  { hierarchy :: Hierarchy
  , modules :: Map String PetriNetModule
  , connections :: [Connection]
  , globalMarking :: Marking
  }
```

### 数学定义

层次Petri网是一个四元组 $HPN = (H, M, C, M_0)$，其中：

- $H$ 是层次结构
- $M$ 是模块集合，$M = \{M_1, M_2, \ldots, M_n\}$
- $C$ 是连接关系，$C \subseteq \bigcup_{i,j} I_i \times I_j$
- $M_0$ 是全局初始标记

### 执行语义

```haskell
-- 层次变迁使能条件
isHierarchicalEnabled :: HierarchicalPetriNet -> Transition -> Bool
isHierarchicalEnabled hpn transition = 
  let module = findModule hpn transition
      localEnabled = isEnabled module transition
      interfaceEnabled = checkInterfaceConstraints hpn transition
  in localEnabled && interfaceEnabled

-- 层次变迁执行
fireHierarchicalTransition :: HierarchicalPetriNet -> Transition -> HierarchicalPetriNet
fireHierarchicalTransition hpn transition = 
  let module = findModule hpn transition
      updatedModule = fireTransition module transition
      updatedModules = updateModule hpn module updatedModule
      newGlobalMarking = updateGlobalMarking hpn transition
  in hpn { modules = updatedModules, globalMarking = newGlobalMarking }
```

## 模块化语义

### 模块组合

```haskell
-- 模块组合
composeModules :: [PetriNetModule] -> [Connection] -> HierarchicalPetriNet
composeModules modules connections = 
  let hierarchy = buildHierarchy modules
      moduleMap = Map.fromList [(moduleId m, m) | m <- modules]
      globalMarking = combineMarkings modules
  in HierarchicalPetriNet hierarchy moduleMap connections globalMarking

-- 构建层次结构
buildHierarchy :: [PetriNetModule] -> Hierarchy
buildHierarchy modules = 
  let rootModules = filter (\m -> null (subModules m)) modules
      nonRootModules = filter (\m -> not (null (subModules m))) modules
  in Hierarchy 0 Nothing (map buildHierarchy nonRootModules) rootModules
```

### 接口语义

```haskell
-- 接口匹配
matchInterfaces :: Interface -> Interface -> Bool
matchInterfaces i1 i2 = 
  let inputMatch = inputPlaces i1 == outputPlaces i2
      outputMatch = outputPlaces i1 == inputPlaces i2
  in inputMatch && outputMatch

-- 接口连接
connectInterfaces :: Interface -> Interface -> Connection
connectInterfaces i1 i2 = 
  let inputConnections = zip (Set.toList (inputPlaces i1)) (Set.toList (outputPlaces i2))
      outputConnections = zip (Set.toList (outputPlaces i1)) (Set.toList (inputPlaces i1))
  in Connection inputConnections outputConnections
```

## 分析技术

### 层次可达性分析

```haskell
-- 层次可达性图
type HierarchicalReachabilityGraph = Graph HierarchicalMarking (Transition, ModuleId)

-- 构建层次可达性图
buildHierarchicalReachabilityGraph :: HierarchicalPetriNet -> HierarchicalReachabilityGraph
buildHierarchicalReachabilityGraph hpn = 
  let initial = HierarchicalMarking (globalMarking hpn) (getModuleMarkings hpn)
      states = exploreHierarchicalStates hpn [initial] Set.empty
      edges = buildHierarchicalEdges hpn states
  in Graph states edges

-- 层次状态探索
exploreHierarchicalStates :: HierarchicalPetriNet -> [HierarchicalMarking] -> Set HierarchicalMarking -> Set HierarchicalMarking
exploreHierarchicalStates hpn [] visited = visited
exploreHierarchicalStates hpn (current:rest) visited =
  if Set.member current visited
  then exploreHierarchicalStates hpn rest visited
  else 
    let enabledTransitions = getHierarchicalEnabledTransitions hpn current
        newStates = map (\t -> fireHierarchicalTransition hpn t current) enabledTransitions
        newVisited = Set.insert current visited
    in exploreHierarchicalStates hpn (rest ++ newStates) newVisited
```

### 模块化验证

```haskell
-- 模块化验证
modularVerification :: HierarchicalPetriNet -> [Property] -> Bool
modularVerification hpn properties = 
  let modules = Map.elems (modules hpn)
      moduleResults = map (\m -> verifyModule m properties) modules
      interfaceResults = verifyInterfaces hpn properties
  in all id moduleResults && all id interfaceResults

-- 模块验证
verifyModule :: PetriNetModule -> [Property] -> Bool
verifyModule module properties = 
  let reachabilityGraph = buildReachabilityGraph module
  in all (\prop -> checkProperty prop reachabilityGraph) properties
```

## 应用示例

### 分布式系统建模

```haskell
-- 分布式系统层次Petri网
distributedSystemHPN :: HierarchicalPetriNet
distributedSystemHPN = HierarchicalPetriNet
  { hierarchy = buildDistributedHierarchy
  , modules = Map.fromList
    [ ("client", clientModule)
    , ("server", serverModule)
    , ("network", networkModule)
    ]
  , connections = [clientServerConnection, serverNetworkConnection]
  , globalMarking = Map.fromList
    [ ("client_ready", 1)
    , ("server_ready", 1)
    , ("network_ready", 1)
    ]
  }

-- 客户端模块
clientModule :: PetriNetModule
clientModule = PetriNetModule
  { moduleId = "client"
  , places = Set.fromList ["ready", "requesting", "waiting", "processing"]
  , transitions = Set.fromList ["send_request", "receive_response", "process_data"]
  , arcs = Set.fromList [Arc "ready" "send_request", Arc "send_request" "requesting"]
  , interfaces = [clientInterface]
  , subModules = []
  }
```

### 制造系统建模

```haskell
-- 制造系统层次Petri网
manufacturingSystemHPN :: HierarchicalPetriNet
manufacturingSystemHPN = HierarchicalPetriNet
  { hierarchy = buildManufacturingHierarchy
  , modules = Map.fromList
    [ ("production", productionModule)
    , ("quality", qualityModule)
    , ("inventory", inventoryModule)
    ]
  , connections = [productionQualityConnection, qualityInventoryConnection]
  , globalMarking = Map.fromList
    [ ("raw_material", 10)
    , ("production_ready", 1)
    , ("quality_ready", 1)
    ]
  }
```

## 高级特性

### 动态重构

```haskell
-- 动态重构
dynamicReconfiguration :: HierarchicalPetriNet -> ReconfigurationRule -> HierarchicalPetriNet
dynamicReconfiguration hpn rule = 
  case rule of
    AddModule module -> addModule hpn module
    RemoveModule moduleId -> removeModule hpn moduleId
    ModifyConnection oldConn newConn -> modifyConnection hpn oldConn newConn
    ChangeHierarchy newHierarchy -> changeHierarchy hpn newHierarchy

-- 重构规则
data ReconfigurationRule = 
    AddModule PetriNetModule
  | RemoveModule String
  | ModifyConnection Connection Connection
  | ChangeHierarchy Hierarchy
```

### 自适应行为

```haskell
-- 自适应行为
adaptiveBehavior :: HierarchicalPetriNet -> AdaptationPolicy -> HierarchicalPetriNet
adaptiveBehavior hpn policy = 
  let currentState = getCurrentState hpn
      adaptation = evaluateAdaptation policy currentState
      adaptedHPN = applyAdaptation hpn adaptation
  in adaptedHPN

-- 适应策略
data AdaptationPolicy = AdaptationPolicy
  { conditions :: [Condition]
  , actions :: [AdaptationAction]
  , priorities :: Map AdaptationAction Int
  }
```

## 工具支持

### 建模工具

```haskell
-- 层次Petri网建模工具
class HierarchicalPetriNetTools where
  loadHierarchicalModel :: FilePath -> IO HierarchicalPetriNet
  saveHierarchicalModel :: HierarchicalPetriNet -> FilePath -> IO ()
  visualizeHierarchy :: HierarchicalPetriNet -> IO ()
  analyzeHierarchical :: HierarchicalPetriNet -> HierarchicalAnalysisResult

-- 层次分析结果
data HierarchicalAnalysisResult = HierarchicalAnalysisResult
  { moduleResults :: Map String ModuleAnalysisResult
  , interfaceResults :: [InterfaceAnalysisResult]
  , globalResults :: GlobalAnalysisResult
  , hierarchyMetrics :: HierarchyMetrics
  }
```

## 相关理论

- [基础Petri网](../01-基础Petri网/01-Basic-Concepts.md)
- [有色Petri网](./01-有色Petri网.md)
- [时间Petri网](./02-时间Petri网.md)
- [随机Petri网](./03-随机Petri网.md)

## 导航

- [返回高级Petri网主索引](./README.md)
- [返回Petri网理论主索引](../README.md)
- [返回理论层主索引](../../README.md)
