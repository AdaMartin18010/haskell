# 软件工程基础 (Software Engineering Foundation)

## 📋 目录

1. [软件开发过程](#1-软件开发过程)
2. [软件需求工程](#2-软件需求工程)
3. [软件设计](#3-软件设计)
4. [软件测试](#4-软件测试)
5. [软件质量保证](#5-软件质量保证)
6. [软件维护](#6-软件维护)
7. [软件项目管理](#7-软件项目管理)
8. [形式化方法](#8-形式化方法)

## 1. 软件开发过程

### 1.1 软件生命周期

**定义 1.1 (软件生命周期)**
软件生命周期是从软件概念到退役的完整过程。

**Haskell实现：**

```haskell
-- 软件生命周期阶段
data LifecyclePhase = 
    Requirements
  | Design
  | Implementation
  | Testing
  | Deployment
  | Maintenance
  | Retirement

-- 软件开发过程
data SoftwareProcess = SoftwareProcess
  { phases :: [LifecyclePhase]
  , artifacts :: Map LifecyclePhase [Artifact]
  , activities :: Map LifecyclePhase [Activity]
  }

-- 软件制品
data Artifact = Artifact
  { name :: String
  , type :: ArtifactType
  , content :: String
  , dependencies :: [String]
  }

-- 活动
data Activity = Activity
  { name :: String
  , input :: [Artifact]
  , output :: [Artifact]
  , duration :: Duration
  }
```

### 1.2 敏捷开发

**定义 1.2 (敏捷开发)**
敏捷开发是一种迭代、增量的软件开发方法。

**Haskell实现：**

```haskell
-- 敏捷团队
data AgileTeam = AgileTeam
  { members :: [TeamMember]
  , roles :: Map Role [TeamMember]
  , velocity :: Velocity
  }

-- 团队成员
data TeamMember = TeamMember
  { name :: String
  , role :: Role
  , skills :: [Skill]
  , availability :: Double
  }

-- 角色
data Role = 
    ProductOwner
  | ScrumMaster
  | Developer
  | Tester

-- 用户故事
data UserStory = UserStory
  { id :: String
  , title :: String
  , description :: String
  , acceptanceCriteria :: [String]
  , storyPoints :: Int
  , priority :: Priority
  }

-- 冲刺
data Sprint = Sprint
  { id :: Int
  , duration :: Duration
  , goal :: String
  , userStories :: [UserStory]
  , velocity :: Velocity
  }

-- 冲刺计划
sprintPlanning :: [UserStory] -> Velocity -> Sprint
sprintPlanning stories velocity = 
  let -- 按优先级排序
      sortedStories = sortBy (comparing priority) stories
      -- 选择适合的故事
      selectedStories = selectStoriesForVelocity sortedStories velocity
  in Sprint {
    id = generateSprintId,
    duration = Duration 14,  -- 2周
    goal = generateSprintGoal selectedStories,
    userStories = selectedStories,
    velocity = velocity
  }

-- 选择适合的故事
selectStoriesForVelocity :: [UserStory] -> Velocity -> [UserStory]
selectStoriesForVelocity stories velocity = 
  let maxPoints = velocityToPoints velocity
      selected = takeWhile (\story -> 
        sum (map storyPoints (story : selected)) <= maxPoints) stories
  in selected
```

## 2. 软件需求工程

### 2.1 需求分类

**定义 2.1 (软件需求)**
软件需求是对系统应该做什么的描述。

**Haskell实现：**

```haskell
-- 需求类型
data RequirementType = 
    FunctionalRequirement
  | NonFunctionalRequirement
  | UserRequirement
  | SystemRequirement

-- 需求
data Requirement = Requirement
  { id :: String
  , type :: RequirementType
  , description :: String
  , priority :: Priority
  , source :: String
  , stakeholders :: [String]
  }

-- 功能需求
data FunctionalRequirement = FunctionalRequirement
  { requirement :: Requirement
  , input :: [Parameter]
  , output :: [Parameter]
  , behavior :: Behavior
  }

-- 非功能需求
data NonFunctionalRequirement = NonFunctionalRequirement
  { requirement :: Requirement
  , qualityAttribute :: QualityAttribute
  , metric :: Metric
  , threshold :: Double
  }

-- 质量属性
data QualityAttribute = 
    Performance
  | Reliability
  | Usability
  | Security
  | Maintainability
  | Portability

-- 需求分析
requirementsAnalysis :: [Requirement] -> RequirementsSpecification
requirementsAnalysis requirements = 
  let -- 分类需求
      functionalReqs = filter (\r -> type r == FunctionalRequirement) requirements
      nonFunctionalReqs = filter (\r -> type r == NonFunctionalRequirement) requirements
      
      -- 分析依赖关系
      dependencies = analyzeDependencies requirements
      
      -- 验证一致性
      consistency = validateConsistency requirements
  in RequirementsSpecification {
    functionalRequirements = functionalReqs,
    nonFunctionalRequirements = nonFunctionalReqs,
    dependencies = dependencies,
    isConsistent = consistency
  }
```

### 2.2 需求建模

**定义 2.2 (需求模型)**
需求模型是需求的抽象表示。

**Haskell实现：**

```haskell
-- 用例模型
data UseCaseModel = UseCaseModel
  { actors :: [Actor]
  , useCases :: [UseCase]
  , relationships :: [UseCaseRelationship]
  }

-- 参与者
data Actor = Actor
  { name :: String
  , type :: ActorType
  , description :: String
  }

-- 用例
data UseCase = UseCase
  { name :: String
  , description :: String
  , actors :: [Actor]
  , preconditions :: [String]
  , postconditions :: [String]
  , mainFlow :: [Step]
  , alternativeFlows :: [[Step]]
  }

-- 用例关系
data UseCaseRelationship = 
    Include UseCase UseCase
  | Extend UseCase UseCase
  | Generalize UseCase UseCase

-- 用例建模
useCaseModeling :: [Requirement] -> UseCaseModel
useCaseModeling requirements = 
  let -- 识别参与者
      actors = identifyActors requirements
      
      -- 识别用例
      useCases = identifyUseCases requirements
      
      -- 建立关系
      relationships = establishRelationships useCases
  in UseCaseModel {
    actors = actors,
    useCases = useCases,
    relationships = relationships
  }
```

## 3. 软件设计

### 3.1 架构设计

**定义 3.1 (软件架构)**
软件架构是系统的高级结构。

**Haskell实现：**

```haskell
-- 软件架构
data SoftwareArchitecture = SoftwareArchitecture
  { components :: [Component]
  , connectors :: [Connector]
  , constraints :: [Constraint]
  , patterns :: [ArchitecturalPattern]
  }

-- 组件
data Component = Component
  { name :: String
  , type :: ComponentType
  , interfaces :: [Interface]
  , responsibilities :: [String]
  }

-- 连接器
data Connector = Connector
  { name :: String
  { type :: ConnectorType
  { source :: Component
  { target :: Component
  { protocol :: Protocol
  }

-- 架构模式
data ArchitecturalPattern = 
    LayeredArchitecture
  | ClientServer
  | Microservices
  | EventDriven
  | ModelViewController

-- 分层架构
layeredArchitecture :: [Layer] -> SoftwareArchitecture
layeredArchitecture layers = 
  let -- 建立层间依赖
      dependencies = establishLayerDependencies layers
      
      -- 定义接口
      interfaces = defineLayerInterfaces layers
      
      -- 约束
      constraints = [OnlyAdjacentLayersCanCommunicate]
  in SoftwareArchitecture {
    components = layers,
    connectors = dependencies,
    constraints = constraints,
    patterns = [LayeredArchitecture]
  }
```

### 3.2 详细设计

**定义 3.2 (详细设计)**
详细设计定义组件的内部结构和行为。

**Haskell实现：**

```haskell
-- 类图
data ClassDiagram = ClassDiagram
  { classes :: [Class]
  , relationships :: [ClassRelationship]
  }

-- 类
data Class = Class
  { name :: String
  { attributes :: [Attribute]
  { methods :: [Method]
  { visibility :: Visibility
  }

-- 属性
data Attribute = Attribute
  { name :: String
  { type :: Type
  { visibility :: Visibility
  { defaultValue :: Maybe Value
  }

-- 方法
data Method = Method
  { name :: String
  { parameters :: [Parameter]
  { returnType :: Type
  { visibility :: Visibility
  { implementation :: Maybe Implementation
  }

-- 类关系
data ClassRelationship = 
    Association Class Class
  | Inheritance Class Class
  | Composition Class Class
  | Aggregation Class Class

-- 设计模式
data DesignPattern = DesignPattern
  { name :: String
  { type :: PatternType
  { problem :: String
  { solution :: String
  { participants :: [Class]
  }

-- 模式类型
data PatternType = 
    Creational
  | Structural
  | Behavioral
```

## 4. 软件测试

### 4.1 测试策略

**定义 4.1 (测试策略)**
测试策略定义测试的目标、范围和方法。

**Haskell实现：**

```haskell
-- 测试策略
data TestStrategy = TestStrategy
  { objectives :: [TestObjective]
  { scope :: TestScope
  { approach :: TestApproach
  { resources :: [Resource]
  }

-- 测试目标
data TestObjective = 
    ValidateRequirements
  | VerifyDesign
  | EnsureQuality
  | ReduceRisk

-- 测试范围
data TestScope = TestScope
  { features :: [Feature]
  { components :: [Component]
  { interfaces :: [Interface]
  }

-- 测试方法
data TestApproach = 
    BlackBoxTesting
  | WhiteBoxTesting
  | GrayBoxTesting

-- 测试用例
data TestCase = TestCase
  { id :: String
  { name :: String
  { description :: String
  { input :: [TestInput]
  { expectedOutput :: [TestOutput]
  { preconditions :: [String]
  { postconditions :: [String]
  }

-- 测试执行
testExecution :: [TestCase] -> TestEnvironment -> TestResults
testExecution testCases environment = 
  let -- 执行测试用例
      results = map (\testCase -> executeTestCase testCase environment) testCases
      
      -- 分析结果
      analysis = analyzeTestResults results
  in TestResults {
    executedTests = length testCases,
    passedTests = length (filter isPassed results),
    failedTests = length (filter isFailed results),
    analysis = analysis
  }
```

### 4.2 单元测试

**定义 4.2 (单元测试)**
单元测试验证单个代码单元的正确性。

**Haskell实现：**

```haskell
-- 单元测试框架
class UnitTestable a where
  runTest :: a -> TestResult
  assert :: Bool -> String -> TestResult

-- 测试结果
data TestResult = 
    Passed
  | Failed String
  | Error String

-- 测试套件
data TestSuite = TestSuite
  { name :: String
  { tests :: [Test]
  { setup :: Maybe (IO ())
  { teardown :: Maybe (IO ())
  }

-- 测试
data Test = Test
  { name :: String
  { testFunction :: IO TestResult
  }

-- 属性测试
propertyTest :: (Arbitrary a, Show a) => (a -> Bool) -> String -> Test
propertyTest property name = 
  Test {
    name = name,
    testFunction = do
      testData <- generate (arbitrary :: Gen a)
      let result = property testData
      if result
        then return Passed
        else return $ Failed $ "Property failed for input: " ++ show testData
  }

-- 示例：测试排序函数
testSortFunction :: TestSuite
testSortFunction = TestSuite {
  name = "Sort Function Tests",
  tests = [
    Test "Empty list" $ do
      let result = sort []
      assert (result == []) "Empty list should remain empty",
    
    Test "Single element" $ do
      let result = sort [5]
      assert (result == [5]) "Single element should remain unchanged",
    
    Test "Multiple elements" $ do
      let result = sort [3, 1, 4, 1, 5]
      assert (result == [1, 1, 3, 4, 5]) "List should be sorted",
    
    propertyTest (\xs -> isSorted (sort xs)) "Sorted result should be sorted",
    propertyTest (\xs -> length (sort xs) == length xs) "Sort should preserve length"
  ],
  setup = Nothing,
  teardown = Nothing
}

-- 辅助函数
isSorted :: Ord a => [a] -> Bool
isSorted [] = True
isSorted [_] = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)
```

## 5. 软件质量保证

### 5.1 质量模型

**定义 5.1 (软件质量)**
软件质量是软件满足需求的程度。

**Haskell实现：**

```haskell
-- 质量模型
data QualityModel = QualityModel
  { characteristics :: [QualityCharacteristic]
  { subcharacteristics :: Map QualityCharacteristic [QualitySubcharacteristic]
  { metrics :: Map QualitySubcharacteristic Metric
  }

-- 质量特征
data QualityCharacteristic = 
    Functionality
  | Reliability
  | Usability
  | Efficiency
  | Maintainability
  | Portability

-- 质量子特征
data QualitySubcharacteristic = QualitySubcharacteristic
  { name :: String
  { characteristic :: QualityCharacteristic
  { description :: String
  }

-- 质量度量
data Metric = Metric
  { name :: String
  { formula :: String
  { unit :: String
  { threshold :: Maybe Double
  }

-- 质量评估
qualityAssessment :: SoftwareArtifact -> QualityModel -> QualityReport
qualityAssessment artifact model = 
  let -- 计算度量值
      measurements = map (\metric -> measureMetric artifact metric) (Map.elems (metrics model))
      
      -- 评估质量
      assessment = assessQuality measurements model
      
      -- 生成报告
      report = generateQualityReport assessment
  in report

-- 代码质量度量
codeQualityMetrics :: SourceCode -> [MetricValue]
codeQualityMetrics code = 
  let -- 圈复杂度
      cyclomaticComplexity = calculateCyclomaticComplexity code
      
      -- 代码行数
      linesOfCode = calculateLinesOfCode code
      
      -- 注释率
      commentRatio = calculateCommentRatio code
      
      -- 重复代码
      codeDuplication = calculateCodeDuplication code
  in [
    MetricValue "CyclomaticComplexity" cyclomaticComplexity,
    MetricValue "LinesOfCode" linesOfCode,
    MetricValue "CommentRatio" commentRatio,
    MetricValue "CodeDuplication" codeDuplication
  ]
```

### 5.2 代码审查

**定义 5.2 (代码审查)**
代码审查是检查代码质量和一致性的过程。

**Haskell实现：**

```haskell
-- 代码审查
data CodeReview = CodeReview
  { reviewer :: Reviewer
  { code :: SourceCode
  { comments :: [ReviewComment]
  { status :: ReviewStatus
  }

-- 审查者
data Reviewer = Reviewer
  { name :: String
  { expertise :: [Technology]
  { reviewHistory :: [CodeReview]
  }

-- 审查注释
data ReviewComment = ReviewComment
  { line :: Int
  { type :: CommentType
  { message :: String
  { severity :: Severity
  }

-- 注释类型
data CommentType = 
    Bug
  | Suggestion
  | Question
  | Praise

-- 严重程度
data Severity = 
    Critical
  | Major
  | Minor
  | Info

-- 自动代码审查
automatedCodeReview :: SourceCode -> [ReviewComment]
automatedCodeReview code = 
  let -- 静态分析
      staticAnalysisIssues = performStaticAnalysis code
      
      -- 代码风格检查
      styleIssues = checkCodeStyle code
      
      -- 安全漏洞检查
      securityIssues = checkSecurityVulnerabilities code
      
      -- 性能问题检查
      performanceIssues = checkPerformanceIssues code
  in staticAnalysisIssues ++ styleIssues ++ securityIssues ++ performanceIssues

-- 静态分析
performStaticAnalysis :: SourceCode -> [ReviewComment]
performStaticAnalysis code = 
  let -- 未使用的变量
      unusedVariables = findUnusedVariables code
      
      -- 死代码
      deadCode = findDeadCode code
      
      -- 类型错误
      typeErrors = findTypeErrors code
  in map (\issue -> ReviewComment {
    line = lineNumber issue,
    type = Bug,
    message = description issue,
    severity = Major
  }) (unusedVariables ++ deadCode ++ typeErrors)
```

## 6. 软件维护

### 6.1 维护类型

**定义 6.1 (软件维护)**
软件维护是软件交付后的修改活动。

**Haskell实现：**

```haskell
-- 维护类型
data MaintenanceType = 
    CorrectiveMaintenance
  | AdaptiveMaintenance
  | PerfectiveMaintenance
  | PreventiveMaintenance

-- 维护请求
data MaintenanceRequest = MaintenanceRequest
  { id :: String
  { type :: MaintenanceType
  { description :: String
  { priority :: Priority
  { affectedComponents :: [Component]
  }

-- 维护活动
data MaintenanceActivity = MaintenanceActivity
  { request :: MaintenanceRequest
  { changes :: [Change]
  { effort :: Effort
  { impact :: Impact
  }

-- 变更
data Change = Change
  { component :: Component
  { type :: ChangeType
  { description :: String
  { implementation :: Implementation
  }

-- 变更类型
data ChangeType = 
    BugFix
  | FeatureAddition
  | FeatureModification
  | FeatureRemoval
  | Refactoring

-- 维护计划
maintenancePlanning :: [MaintenanceRequest] -> MaintenancePlan
maintenancePlanning requests = 
  let -- 按优先级排序
      sortedRequests = sortBy (comparing priority) requests
      
      -- 估算工作量
      estimatedEffort = map estimateEffort sortedRequests
      
      -- 分配资源
      resourceAllocation = allocateResources sortedRequests
      
      -- 制定时间表
      schedule = createSchedule sortedRequests estimatedEffort
  in MaintenancePlan {
    requests = sortedRequests,
    effort = estimatedEffort,
    resources = resourceAllocation,
    schedule = schedule
  }
```

### 6.2 版本控制

**定义 6.2 (版本控制)**
版本控制管理软件的不同版本。

**Haskell实现：**

```haskell
-- 版本控制系统
data VersionControlSystem = VersionControlSystem
  { repository :: Repository
  { branches :: [Branch]
  { commits :: [Commit]
  }

-- 仓库
data Repository = Repository
  { name :: String
  { url :: String
  { history :: [Commit]
  }

-- 分支
data Branch = Branch
  { name :: String
  { head :: Commit
  { parent :: Maybe Branch
  }

-- 提交
data Commit = Commit
  { id :: String
  { message :: String
  { author :: String
  { timestamp :: Time
  { changes :: [Change]
  { parent :: Maybe Commit
  }

-- 变更
data Change = Change
  { file :: String
  { type :: ChangeType
  { content :: String
  }

-- 变更类型
data ChangeType = 
    Added
  | Modified
  | Deleted

-- 分支操作
createBranch :: VersionControlSystem -> String -> Commit -> VersionControlSystem
createBranch vcs name commit = 
  let newBranch = Branch {
    name = name,
    head = commit,
    parent = Nothing
  }
  in vcs { branches = branches vcs ++ [newBranch] }

-- 合并分支
mergeBranches :: VersionControlSystem -> Branch -> Branch -> VersionControlSystem
mergeBranches vcs source target = 
  let -- 查找共同祖先
      commonAncestor = findCommonAncestor (head source) (head target)
      
      -- 计算差异
      diff = calculateDiff (head source) (head target)
      
      -- 解决冲突
      resolvedChanges = resolveConflicts diff
      
      -- 创建合并提交
      mergeCommit = Commit {
        id = generateCommitId,
        message = "Merge " ++ name source ++ " into " ++ name target,
        author = "System",
        timestamp = getCurrentTime,
        changes = resolvedChanges,
        parent = Just (head target)
      }
  in vcs { commits = commits vcs ++ [mergeCommit] }
```

## 7. 软件项目管理

### 7.1 项目计划

**定义 7.1 (项目计划)**
项目计划定义项目的目标、范围、时间和资源。

**Haskell实现：**

```haskell
-- 项目计划
data ProjectPlan = ProjectPlan
  { objectives :: [Objective]
  { scope :: Scope
  { timeline :: Timeline
  { resources :: [Resource]
  { risks :: [Risk]
  }

-- 目标
data Objective = Objective
  { description :: String
  { measurable :: Bool
  { criteria :: [String]
  }

-- 范围
data Scope = Scope
  { features :: [Feature]
  { constraints :: [Constraint]
  { assumptions :: [Assumption]
  }

-- 时间线
data Timeline = Timeline
  { startDate :: Date
  { endDate :: Date
  { milestones :: [Milestone]
  { phases :: [Phase]
  }

-- 里程碑
data Milestone = Milestone
  { name :: String
  { date :: Date
  { deliverables :: [Deliverable]
  }

-- 项目跟踪
projectTracking :: ProjectPlan -> ProjectStatus -> ProjectStatus
projectTracking plan status = 
  let -- 计算进度
      progress = calculateProgress status
      
      -- 检查里程碑
      milestoneStatus = checkMilestones (timeline plan) status
      
      -- 评估风险
      riskAssessment = assessRisks (risks plan) status
      
      -- 更新状态
      updatedStatus = updateStatus status progress milestoneStatus riskAssessment
  in updatedStatus
```

### 7.2 风险管理

**定义 7.2 (风险管理)**
风险管理识别、分析和应对项目风险。

**Haskell实现：**

```haskell
-- 风险
data Risk = Risk
  { id :: String
  { description :: String
  { probability :: Probability
  { impact :: Impact
  { mitigation :: [MitigationStrategy]
  }

-- 概率
data Probability = 
    VeryLow
  | Low
  | Medium
  | High
  | VeryHigh

-- 影响
data Impact = 
    Negligible
  | Minor
  | Moderate
  | Major
  | Critical

-- 缓解策略
data MitigationStrategy = MitigationStrategy
  { description :: String
  { cost :: Cost
  { effectiveness :: Double
  }

-- 风险分析
riskAnalysis :: [Risk] -> RiskAnalysis
riskAnalysis risks = 
  let -- 计算风险值
      riskValues = map calculateRiskValue risks
      
      -- 风险矩阵
      riskMatrix = createRiskMatrix risks
      
      -- 优先级排序
      prioritizedRisks = sortBy (comparing riskValue) riskValues
  in RiskAnalysis {
    risks = risks,
    riskValues = riskValues,
    riskMatrix = riskMatrix,
    prioritizedRisks = prioritizedRisks
  }

-- 计算风险值
calculateRiskValue :: Risk -> Double
calculateRiskValue risk = 
  let prob = probabilityToNumber (probability risk)
      imp = impactToNumber (impact risk)
  in prob * imp

-- 概率转数字
probabilityToNumber :: Probability -> Double
probabilityToNumber VeryLow = 0.1
probabilityToNumber Low = 0.3
probabilityToNumber Medium = 0.5
probabilityToNumber High = 0.7
probabilityToNumber VeryHigh = 0.9
```

## 8. 形式化方法

### 8.1 形式化规约

**定义 8.1 (形式化规约)**
形式化规约使用数学符号精确描述软件行为。

**Haskell实现：**

```haskell
-- 形式化规约
data FormalSpecification = FormalSpecification
  { preconditions :: [Predicate]
  { postconditions :: [Predicate]
  { invariants :: [Predicate]
  }

-- 谓词
data Predicate = Predicate
  { expression :: String
  { variables :: [Variable]
  }

-- 变量
data Variable = Variable
  { name :: String
  { type :: Type
  }

-- Z规约语言
data ZSpecification = ZSpecification
  { schemas :: [Schema]
  { operations :: [Operation]
  }

-- Schema
data Schema = Schema
  { name :: String
  { declarations :: [Declaration]
  { predicates :: [Predicate]
  }

-- 操作
data Operation = Operation
  { name :: String
  { input :: [Variable]
  { output :: [Variable]
  { preconditions :: [Predicate]
  { postconditions :: [Predicate]
  }

-- 规约验证
specificationVerification :: FormalSpecification -> VerificationResult
specificationVerification spec = 
  let -- 一致性检查
      consistency = checkConsistency spec
      
      -- 完整性检查
      completeness = checkCompleteness spec
      
      -- 可满足性检查
      satisfiability = checkSatisfiability spec
  in VerificationResult {
    isConsistent = consistency,
    isComplete = completeness,
    isSatisfiable = satisfiability
  }
```

### 8.2 模型检测

**定义 8.2 (模型检测)**
模型检测验证系统是否满足给定的性质。

**Haskell实现：**

```haskell
-- 模型检测器
data ModelChecker = ModelChecker
  { model :: StateMachine
  { properties :: [Property]
  }

-- 状态机
data StateMachine = StateMachine
  { states :: [State]
  { transitions :: [Transition]
  { initialStates :: [State]
  }

-- 状态
data State = State
  { id :: String
  { variables :: Map String Value
  }

-- 转换
data Transition = Transition
  { source :: State
  { target :: State
  { guard :: Predicate
  { action :: Action
  }

-- 性质
data Property = 
    SafetyProperty String (State -> Bool)
  | LivenessProperty String (State -> Bool)

-- 模型检测
modelChecking :: ModelChecker -> [VerificationResult]
modelChecking checker = 
  let model = model checker
      properties = properties checker
      
      -- 计算可达状态
      reachableStates = computeReachableStates model
      
      -- 检查每个性质
      results = map (\property -> checkProperty property reachableStates) properties
  in results

-- 计算可达状态
computeReachableStates :: StateMachine -> Set State
computeReachableStates sm = 
  let initialStates = Set.fromList (initialStates sm)
      transitions = transitions sm
      
      -- 广度优先搜索
      bfs states visited = 
        let nextStates = Set.unions (map (\state -> 
              Set.fromList (map target (filter (\t -> source t == state) transitions))) states)
            unvisitedStates = Set.difference nextStates visited
        in if Set.null unvisitedStates
           then visited
           else bfs unvisitedStates (Set.union visited unvisitedStates)
  in bfs initialStates initialStates
```

## 📚 参考文献

1. Sommerville, I. (2015). Software Engineering. Pearson.
2. Pressman, R. S. (2014). Software Engineering: A Practitioner's Approach. McGraw-Hill.
3. Boehm, B. W. (1988). A spiral model of software development and enhancement. Computer.
4. Beck, K. (2000). Extreme Programming Explained. Addison-Wesley.

## 🔗 相关链接

- [计算机科学基础](../01-Computer-Science/计算机科学基础.md)
- [人工智能基础](../03-Artificial-Intelligence/人工智能基础.md)
- [数据科学基础](../04-Data-Science/数据科学基础.md)

---

*本文档提供了软件工程的完整理论基础，包含软件开发、测试、质量保证等核心概念，为后续的具体应用提供理论支撑。*
