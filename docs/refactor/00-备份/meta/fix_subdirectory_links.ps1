# 子目录链接修复脚本
# 用于修复各子目录中的链接引用问题

# 定义颜色函数
function Write-ColorOutput($ForegroundColor) {
    $fc = $host.UI.RawUI.ForegroundColor
    $host.UI.RawUI.ForegroundColor = $ForegroundColor
    if ($args) {
        Write-Output $args
    }
    else {
        $input | Write-Output
    }
    $host.UI.RawUI.ForegroundColor = $fc
}

function Write-Success($message) {
    Write-ColorOutput Green $message
}

function Write-Warning($message) {
    Write-ColorOutput Yellow $message
}

function Write-Error($message) {
    Write-ColorOutput Red $message
}

function Write-Info($message) {
    Write-ColorOutput Cyan $message
}

# 显示脚本信息
Write-Info "====================================================="
Write-Info "       子目录链接修复脚本"
Write-Info "====================================================="
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 定义要处理的子目录
$subDirs = @(
    "01-核心知识图谱",
    "02-深度分析",
    "03-设计模式",
    "04-类型系统",
    "05-执行流控制流",
    "06-形式化方法",
    "07-实践指南",
    "08-关联分析",
    "09-进度报告",
    "10-索引导航"
)

# 创建缺失的子目录文件
foreach ($dir in $subDirs) {
    $dirPath = Join-Path -Path $rootDir -ChildPath $dir
    
    # 如果目录不存在，创建它
    if (-not (Test-Path $dirPath)) {
        New-Item -Path $dirPath -ItemType Directory | Out-Null
        Write-Success "  已创建目录: $dir"
    }
    
    # 检查是否有README.md文件，如果没有则创建
    $readmePath = Join-Path -Path $dirPath -ChildPath "README.md"
    if (-not (Test-Path $readmePath)) {
        $readmeContent = @"
# $dir

> 本目录包含与$dir相关的文档和资源。

## 目录内容

- [返回上级](../README_统一版.md)
- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md)
- [快速导航](../快速导航_统一版.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $readmePath -Value $readmeContent
        Write-Success "  已创建README.md: $dir/README.md"
    }
}

# 修复01-核心知识图谱目录中的链接
Write-Info "1. 修复01-核心知识图谱目录中的链接..."
$dirPath = Join-Path -Path $rootDir -ChildPath "01-核心知识图谱"

# 创建01-知识图谱-核心.md文件
$filePath = Join-Path -Path $dirPath -ChildPath "01-知识图谱-核心.md"
if (-not (Test-Path $filePath)) {
    $fileContent = @"
# Lean与Haskell核心知识图谱

> 本文档提供Lean与Haskell的核心知识图谱，包括基础概念、类型系统和编程范式对比。

## 1. 基础概念

- 函数式编程基础
- 类型系统基础
- 语法对比
- 模块系统对比

## 2. 详细内容

请参考[统一知识图谱](../lean_haskell_unified_knowledge_graph.md)获取完整内容。

## 3. 相关链接

- [详细概念关系图](02-概念关系图.md)
- [深度分析整合](../02-深度分析/01-深度分析-整合.md)
- [函数式设计模式](../03-设计模式/01-设计模式-函数式.md)
- [类型系统对比](../04-类型系统/01-类型系统-对比.md)

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $filePath -Value $fileContent
    Write-Success "  已创建文件: 01-核心知识图谱/01-知识图谱-核心.md"
}

# 创建02-概念关系图.md文件
$filePath = Join-Path -Path $dirPath -ChildPath "02-概念关系图.md"
if (-not (Test-Path $filePath)) {
    $fileContent = @"
# Lean与Haskell概念关系图

> 本文档提供Lean与Haskell的概念关系图，展示各概念之间的关联性。

## 1. 核心概念关系

- **函数式编程范式** → [函数式编程范式](../lean_haskell_unified_knowledge_graph.md#函数式编程范式)
- **类型系统理论** → [类型系统理论](../lean_haskell_unified_knowledge_graph.md#类型系统理论)
- **范畴论基础** → [范畴论基础](../lean_haskell_unified_knowledge_graph.md#范畴论基础)

## 2. 设计模式关系

- **函数式设计模式** → [函数式设计模式](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)
- **架构设计模式** → [架构设计模式](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)
- **验证设计模式** → [验证设计模式](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)

## 3. 执行与控制流关系

- **求值策略** → [求值策略](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)
- **控制结构** → [控制结构](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)
- **数据流处理** → [数据流处理](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)

## 4. 形式化方法关系

- **形式化验证** → [形式化验证](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)
- **定理证明** → [定理证明](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)
- **程序推导** → [程序推导](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)

## 5. 应用领域关系

- **领域特定语言** → [领域特定语言](../lean_haskell_unified_knowledge_graph.md#61-应用领域)
- **领域建模** → [领域建模](../lean_haskell_unified_knowledge_graph.md#61-应用领域)
- **形式化模型** → [形式化模型](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $filePath -Value $fileContent
    Write-Success "  已创建文件: 01-核心知识图谱/02-概念关系图.md"
}

# 修复05-执行流控制流目录中的链接
Write-Info "2. 修复05-执行流控制流目录中的链接..."
$dirPath = Join-Path -Path $rootDir -ChildPath "05-执行流控制流"

# 创建01-执行流-控制流.md文件
$filePath = Join-Path -Path $dirPath -ChildPath "01-执行流-控制流.md"
if (-not (Test-Path $filePath)) {
    $fileContent = @"
# 执行流与控制流

> 本文档分析Lean与Haskell的执行流与控制流机制，包括求值策略、控制结构和单子控制流。

## 1. 求值策略

- 惰性求值 vs 严格求值
- 求值顺序
- 短路求值

## 2. 控制结构

- 条件控制
- 循环与递归
- 异常处理

## 3. 单子控制流

- 单子基础
- [单子控制流](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)
- IO单子
- State单子
- Reader单子
- Writer单子

## 4. 相关资源

- [数据流处理](02-数据流-处理.md)
- [并发模型](03-并发模型.md)
- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $filePath -Value $fileContent
    Write-Success "  已创建文件: 05-执行流控制流/01-执行流-控制流.md"
}

# 创建02-数据流-处理.md文件
$filePath = Join-Path -Path $dirPath -ChildPath "02-数据流-处理.md"
if (-not (Test-Path $filePath)) {
    $fileContent = @"
# 数据流处理

> 本文档分析Lean与Haskell的数据流处理机制，包括流处理、管道和函数组合。

## 1. 流处理模型

- 惰性流
- 严格流
- 流转换

## 2. 管道与组合

- 函数组合
- 管道操作符
- 数据转换链

## 3. 高阶函数

- map/filter/reduce
- fold操作
- 扫描操作

## 4. 相关资源

- [执行流控制流](01-执行流-控制流.md)
- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $filePath -Value $fileContent
    Write-Success "  已创建文件: 05-执行流控制流/02-数据流-处理.md"
}

# 创建03-并发模型.md文件
$filePath = Join-Path -Path $dirPath -ChildPath "03-并发模型.md"
if (-not (Test-Path $filePath)) {
    $fileContent = @"
# 并发模型

> 本文档分析Lean与Haskell的并发编程模型，包括并发原语、并行计算和异步处理。

## 1. 并发原语

- 线程与轻量级线程
- 通信机制
- 同步机制

## 2. 并行计算

- 数据并行
- 任务并行
- 并行策略

## 3. 异步处理

- Promise/Future
- 异步IO
- 事件驱动编程

## 4. 相关资源

- [执行流控制流](01-执行流-控制流.md)
- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#93-并发与并行)

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $filePath -Value $fileContent
    Write-Success "  已创建文件: 05-执行流控制流/03-并发模型.md"
}

# 完成
Write-Info ""
Write-Success "子目录链接修复完成！"
Write-Info "=====================================================" 