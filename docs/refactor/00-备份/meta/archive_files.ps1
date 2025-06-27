# Lean与Haskell知识体系文件归档脚本
# 用于创建归档目录并移动旧版文件

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
Write-Info "       Lean与Haskell知识体系文件归档脚本"
Write-Info "====================================================="
Write-Info "此脚本将创建归档目录并移动旧版文件"
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 定义需要归档的文件
$filesToArchive = @(
    "lean_haskell_knowledge_graph.md",
    "快速导航.md",
    "快速导航_更新版.md",
    "整理总结报告.md",
    "整理总结报告_更新版.md",
    "link_fix_plan.md",
    "link_fix_plan_new.md",
    "comprehensive_fix_plan.md",
    "reorganization_summary.md"
)

# 定义需要保留的核心文件
$coreFiles = @(
    "lean_haskell_unified_knowledge_graph.md",
    "快速导航_统一版.md",
    "整理工作报告.md",
    "README_统一版.md",
    "README.md",
    "文件引用关系图.md",
    "统一版文件列表.md",
    "清理计划.md",
    "check_all.bat",
    "fix_links_unified.ps1",
    "format_unify.ps1",
    "archive_files.ps1",
    "check_structure.ps1",
    "check_links.ps1",
    "fix_links.ps1"
)

# 1. 创建归档目录
Write-Info "1. 创建归档目录..."
$archiveDir = Join-Path -Path $rootDir -ChildPath "archived"
if (-not (Test-Path $archiveDir)) {
    New-Item -Path $archiveDir -ItemType Directory | Out-Null
    Write-Success "  已创建归档目录: archived/"
} else {
    Write-Warning "  归档目录已存在: archived/"
}

# 2. 移动旧版文件到归档目录
Write-Info "2. 移动旧版文件到归档目录..."
foreach ($file in $filesToArchive) {
    $filePath = Join-Path -Path $rootDir -ChildPath $file
    $destPath = Join-Path -Path $archiveDir -ChildPath $file
    
    if (Test-Path $filePath) {
        # 检查目标文件是否已存在
        if (Test-Path $destPath) {
            $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
            $destPath = Join-Path -Path $archiveDir -ChildPath "$($file -replace '\.md$', '')_$timestamp.md"
        }
        
        # 移动文件
        Move-Item -Path $filePath -Destination $destPath
        Write-Success "  已归档文件: $file -> archived/$($destPath | Split-Path -Leaf)"
    } else {
        Write-Warning "  文件不存在，跳过: $file"
    }
}

# 3. 创建归档说明文件
Write-Info "3. 创建归档说明文件..."
$readmeContent = @"
# 归档文件

> 本目录包含Lean与Haskell知识体系整理过程中归档的旧版文件。

## 归档文件列表

以下文件已被新版文件替代，仅作为历史记录保留：

| 归档文件 | 对应的新文件 |
|---------|------------|
| lean_haskell_knowledge_graph.md | lean_haskell_unified_knowledge_graph.md |
| 快速导航.md | 快速导航_统一版.md |
| 快速导航_更新版.md | 快速导航_统一版.md |
| 整理总结报告.md | 整理工作报告.md |
| 整理总结报告_更新版.md | 整理工作报告.md |
| link_fix_plan.md | - |
| link_fix_plan_new.md | - |
| comprehensive_fix_plan.md | - |
| reorganization_summary.md | - |

## 归档原因

这些文件已经被整合到新的统一版文件中，或者其内容已过时。为了保持知识体系的清晰性和一致性，我们将这些文件归档。

## 访问新版文件

请使用以下核心文件：

- [统一知识图谱](../lean_haskell_unified_knowledge_graph.md)：Lean与Haskell整合统一知识图谱
- [统一快速导航](../快速导航_统一版.md)：知识体系快速导航
- [整理工作报告](../整理工作报告.md)：整理工作的总结报告
- [统一README](../README_统一版.md)：完整的知识体系说明

---

-*最后更新：2024年整理版本*
"@

$readmePath = Join-Path -Path $archiveDir -ChildPath "README.md"
Set-Content -Path $readmePath -Value $readmeContent
Write-Success "  已创建归档说明文件: archived/README.md"

# 4. 检查是否有其他非核心文件
Write-Info "4. 检查是否有其他非核心文件..."
$allFiles = Get-ChildItem -Path $rootDir -File | Where-Object { $_.Extension -eq ".md" }
$nonCoreFiles = $allFiles | Where-Object { $coreFiles -notcontains $_.Name -and $filesToArchive -notcontains $_.Name }

if ($nonCoreFiles.Count -gt 0) {
    Write-Warning "  发现其他非核心文件:"
    foreach ($file in $nonCoreFiles) {
        Write-Warning "    - $($file.Name)"
    }
    
    # 询问是否归档这些文件
    Write-Info "  是否要归档这些非核心文件? (Y/N)"
    $response = Read-Host
    if ($response -eq "Y" -or $response -eq "y") {
        foreach ($file in $nonCoreFiles) {
            $destPath = Join-Path -Path $archiveDir -ChildPath $file.Name
            
            # 检查目标文件是否已存在
            if (Test-Path $destPath) {
                $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
                $destPath = Join-Path -Path $archiveDir -ChildPath "$($file.BaseName)_$timestamp$($file.Extension)"
            }
            
            # 移动文件
            Move-Item -Path $file.FullName -Destination $destPath
            Write-Success "    已归档文件: $($file.Name) -> archived/$($destPath | Split-Path -Leaf)"
        }
    } else {
        Write-Info "  跳过归档非核心文件"
    }
} else {
    Write-Success "  未发现其他非核心文件"
}

# 完成
Write-Info ""
Write-Success "文件归档完成！"
Write-Info "=====================================================" 