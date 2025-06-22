# 最终链接修复脚本
# 用于修复剩余的链接问题

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
Write-Info "       最终链接修复脚本"
Write-Info "====================================================="
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 1. 修复快速导航中的工具链接
Write-Info "1. 修复快速导航中的工具链接..."

# 定义工具脚本
$toolScripts = @(
    "check_links.ps1",
    "fix_links_unified.ps1",
    "check_structure.ps1",
    "check_all.bat",
    "clean_all.bat"
)

# 修复README.md中的工具链接
$readmePath = Join-Path -Path $rootDir -ChildPath "README.md"
if (Test-Path $readmePath) {
    $content = Get-Content -Path $readmePath -Raw
    $modified = $false
    
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]") {
            $content = $content -replace "\[([^]]+)\]\($script\)", "[$1](./$script)"
            $modified = $true
        }
    }
    
    if ($modified) {
        Set-Content -Path $readmePath -Value $content
        Write-Success "  已修复README.md中的工具链接"
    }
}

# 修复快速导航.md中的工具链接
$navPath = Join-Path -Path $rootDir -ChildPath "快速导航.md"
if (Test-Path $navPath) {
    $content = Get-Content -Path $navPath -Raw
    $modified = $false
    
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]") {
            $content = $content -replace "\[([^]]+)\]\(\./$script\)", "[$1](./$script)"
            $modified = $true
        }
    }
    
    if ($modified) {
        Set-Content -Path $navPath -Value $content
        Write-Success "  已修复快速导航.md中的工具链接"
    }
}

# 修复统一版文件列表.md中的工具链接
$listPath = Join-Path -Path $rootDir -ChildPath "统一版文件列表.md"
if (Test-Path $listPath) {
    $content = Get-Content -Path $listPath -Raw
    $modified = $false
    
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]") {
            $content = $content -replace "\[([^]]+)\]\($script\)", "[$1](./$script)"
            $modified = $true
        }
    }
    
    if ($modified) {
        Set-Content -Path $listPath -Value $content
        Write-Success "  已修复统一版文件列表.md中的工具链接"
    }
}

# 2. 修复01-核心知识图谱中的链接
Write-Info "2. 修复01-核心知识图谱中的链接..."

# 创建03-设计模式目录下的文件
$designPatternsDir = Join-Path -Path $rootDir -ChildPath "03-设计模式"
if (Test-Path $designPatternsDir) {
    # 创建01-设计模式-函数式.md
    $filePath = Join-Path -Path $designPatternsDir -ChildPath "01-设计模式-函数式.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 函数式设计模式

> 本文档介绍Lean与Haskell中的函数式设计模式，包括范畴论基础、单子模式和函数式抽象。

## 1. 范畴论基础

- 函子
- 应用函子
- 单子

## 2. 单子控制流

- IO单子
- State单子
- Reader单子
- Writer单子

## 3. 函数式抽象

- 高阶函数
- 柯里化
- 部分应用

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)
- [架构设计模式](02-设计模式-架构.md)
- [设计模式实践](03-设计模式-实践.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 03-设计模式/01-设计模式-函数式.md"
    }
    
    # 创建02-设计模式-架构.md
    $filePath = Join-Path -Path $designPatternsDir -ChildPath "02-设计模式-架构.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 架构设计模式

> 本文档介绍Lean与Haskell中的架构设计模式，包括分层架构、组件架构和函数式架构。

## 1. 分层架构

- 数据层
- 业务逻辑层
- 表示层

## 2. 组件架构

- 纯组件
- 副作用隔离
- 组件组合

## 3. 函数式架构

- 依赖注入
- 配置即代码
- 不可变基础设施

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)
- [函数式设计模式](01-设计模式-函数式.md)
- [设计模式实践](03-设计模式-实践.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 03-设计模式/02-设计模式-架构.md"
    }
    
    # 创建03-设计模式-实践.md
    $filePath = Join-Path -Path $designPatternsDir -ChildPath "03-设计模式-实践.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 设计模式实践

> 本文档介绍Lean与Haskell中的设计模式实践案例，包括领域特定语言、领域建模和实际应用。

## 1. 领域特定语言

- 内部DSL
- 外部DSL
- 嵌入式DSL

## 2. 领域建模

- 代数数据类型
- 类型驱动设计
- 依赖类型

## 3. 实际应用

- Web开发
- 数据处理
- 并发编程

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)
- [函数式设计模式](01-设计模式-函数式.md)
- [架构设计模式](02-设计模式-架构.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 03-设计模式/03-设计模式-实践.md"
    }
}

# 创建04-类型系统目录下的文件
$typeSystemDir = Join-Path -Path $rootDir -ChildPath "04-类型系统"
if (Test-Path $typeSystemDir) {
    # 创建01-类型系统-对比.md
    $filePath = Join-Path -Path $typeSystemDir -ChildPath "01-类型系统-对比.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 类型系统对比

> 本文档对比Lean与Haskell的类型系统，包括函数式编程范式、类型系统理论和类型特性。

## 1. 函数式编程范式

- 纯函数
- 不可变性
- 引用透明

## 2. 类型系统理论

- 静态类型
- 类型推导
- 多态

## 3. 类型特性

- 代数数据类型
- 类型类
- 依赖类型

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#2-类型系统深度对比)
- [类型系统高级特性](02-类型系统-高级特性.md)
- [类型系统应用](03-类型系统-应用.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 04-类型系统/01-类型系统-对比.md"
    }
    
    # 创建02-类型系统-高级特性.md
    $filePath = Join-Path -Path $typeSystemDir -ChildPath "02-类型系统-高级特性.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 类型系统高级特性

> 本文档介绍Lean与Haskell类型系统的高级特性，包括高级类型构造、类型级编程和证明辅助。

## 1. 高级类型构造

- GADT
- 类型族
- 高阶类型

## 2. 类型级编程

- 类型族
- 类型级函数
- 类型级算法

## 3. 证明辅助

- 定理证明
- 类型证明
- 依赖类型

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#2-类型系统深度对比)
- [类型系统对比](01-类型系统-对比.md)
- [类型系统应用](03-类型系统-应用.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 04-类型系统/02-类型系统-高级特性.md"
    }
    
    # 创建03-类型系统-应用.md
    $filePath = Join-Path -Path $typeSystemDir -ChildPath "03-类型系统-应用.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 类型系统应用

> 本文档介绍Lean与Haskell类型系统的实际应用，包括类型安全、领域建模和API设计。

## 1. 类型安全

- 编译时检查
- 类型驱动开发
- 错误预防

## 2. 领域建模

- 代数数据类型建模
- 状态机建模
- 业务规则建模

## 3. API设计

- 类型驱动API
- 组合式API
- 类型级约束

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#2-类型系统深度对比)
- [类型系统对比](01-类型系统-对比.md)
- [类型系统高级特性](02-类型系统-高级特性.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 04-类型系统/03-类型系统-应用.md"
    }
}

# 创建06-形式化方法目录下的文件
$formalMethodsDir = Join-Path -Path $rootDir -ChildPath "06-形式化方法"
if (Test-Path $formalMethodsDir) {
    # 创建01-形式化验证.md
    $filePath = Join-Path -Path $formalMethodsDir -ChildPath "01-形式化验证.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 形式化验证

> 本文档介绍Lean与Haskell中的形式化验证方法，包括形式化模型、验证设计模式和属性测试。

## 1. 形式化模型

- 状态机模型
- 行为模型
- 时序逻辑

## 2. 验证设计模式

- 不变量
- 前置条件与后置条件
- 类型驱动验证

## 3. 属性测试

- QuickCheck
- 基于属性的测试
- 随机测试

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)
- [定理证明](02-定理证明.md)
- [程序推导](03-程序推导.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 06-形式化方法/01-形式化验证.md"
    }
    
    # 创建02-定理证明.md
    $filePath = Join-Path -Path $formalMethodsDir -ChildPath "02-定理证明.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 定理证明

> 本文档介绍Lean与Haskell中的定理证明技术，包括定理证明系统、证明策略和自动化证明。

## 1. 定理证明系统

- Lean定理证明
- Coq集成
- Agda集成

## 2. 证明策略

- 归纳证明
- 反证法
- 构造性证明

## 3. 自动化证明

- 证明搜索
- 策略组合
- 证明重用

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)
- [形式化验证](01-形式化验证.md)
- [程序推导](03-程序推导.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 06-形式化方法/02-定理证明.md"
    }
    
    # 创建03-程序推导.md
    $filePath = Join-Path -Path $formalMethodsDir -ChildPath "03-程序推导.md"
    if (-not (Test-Path $filePath)) {
        $fileContent = @"
# 程序推导

> 本文档介绍Lean与Haskell中的程序推导方法，包括等式推理、程序变换和优化技术。

## 1. 等式推理

- 代数推理
- 程序等价性
- 重写系统

## 2. 程序变换

- 融合变换
- 去递归
- 并行化变换

## 3. 优化技术

- 记忆化
- 惰性评估优化
- 代数优化

## 4. 相关资源

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)
- [形式化验证](01-形式化验证.md)
- [定理证明](02-定理证明.md)

---

-*最后更新：2024年整理版本*
"@
        Set-Content -Path $filePath -Value $fileContent
        Write-Success "  已创建文件: 06-形式化方法/03-程序推导.md"
    }
}

# 3. 修复10-索引导航目录下的README.md
Write-Info "3. 修复10-索引导航目录下的README.md..."
$navDir = Join-Path -Path $rootDir -ChildPath "10-索引导航"
$readmePath = Join-Path -Path $navDir -ChildPath "README.md"

if (Test-Path $readmePath) {
    $content = @"
# 索引导航

> 本目录包含Lean与Haskell知识体系的索引和导航文件。

## 目录内容

- [返回上级](../README_统一版.md)
- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md)
- [快速导航](../快速导航_统一版.md)
- [整理总结报告](../整理工作报告.md)

## 索引文件

- [01-总索引](01-总索引.md)：完整的内容索引
- [02-快速导航](02-快速导航.md)：快速导航索引
- [03-知识图谱导航](03-知识图谱导航.md)：知识图谱导航

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $readmePath -Value $content
    Write-Success "  已修复10-索引导航/README.md"
}

# 4. 修复10-索引导航目录下的01-总索引.md
Write-Info "4. 修复10-索引导航目录下的01-总索引.md..."
$indexPath = Join-Path -Path $navDir -ChildPath "01-总索引.md"

if (Test-Path $indexPath) {
    $content = @"
# Lean与Haskell知识体系总索引

> 本文档提供Lean与Haskell知识体系的完整索引，方便快速查找和访问各部分内容。

## 1. 核心文档

- [Lean与Haskell知识图谱](../lean_haskell_unified_knowledge_graph.md)：统一知识图谱
- [快速导航](../快速导航_统一版.md)：快速导航入口
- [整理总结报告](../整理工作报告.md)：整理工作总结
- [文件整理计划](../清理计划.md)：文件整理计划

## 2. 知识体系分类

### 2.1 核心知识

- [01-核心知识图谱](../01-核心知识图谱/)：核心知识图谱目录
- [02-深度分析](../02-深度分析/)：深度分析目录
- [03-设计模式](../03-设计模式/)：设计模式目录
- [04-类型系统](../04-类型系统/)：类型系统目录

### 2.2 应用与实践

- [05-执行流控制流](../05-执行流控制流/)：执行流控制流目录
- [06-形式化方法](../06-形式化方法/)：形式化方法目录
- [07-实践指南](../07-实践指南/)：实践指南目录
- [08-关联分析](../08-关联分析/)：关联分析目录

### 2.3 导航与进度

- [09-进度报告](../09-进度报告/)：进度报告目录
- [10-索引导航](../10-索引导航/)：索引导航目录

## 3. 快速访问链接

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md#1-核心概念对比)：核心概念对比
- [类型系统深度对比](../lean_haskell_unified_knowledge_graph.md#2-类型系统深度对比)：类型系统深度对比
- [软件设计与设计模式](../lean_haskell_unified_knowledge_graph.md#3-软件设计与设计模式)：软件设计与设计模式
- [执行流与控制流](../lean_haskell_unified_knowledge_graph.md#4-执行流与控制流)：执行流与控制流
- [形式化方法](../lean_haskell_unified_knowledge_graph.md#5-形式化方法)：形式化方法
- [实践应用](../lean_haskell_unified_knowledge_graph.md#6-实践应用)：实践应用
- [学习路径与资源](../lean_haskell_unified_knowledge_graph.md#7-学习路径与资源)：学习路径与资源
- [整合视角](../lean_haskell_unified_knowledge_graph.md#8-整合视角)：整合视角
- [语言特性详细对比](../lean_haskell_unified_knowledge_graph.md#9-语言特性详细对比)：语言特性详细对比

---

-*最后更新：2024年整理版本*
"@
    Set-Content -Path $indexPath -Value $content
    Write-Success "  已修复10-索引导航/01-总索引.md"
}

# 完成
Write-Info ""
Write-Success "最终链接修复完成！"
Write-Info "=====================================================" 