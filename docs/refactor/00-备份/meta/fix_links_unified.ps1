# Lean与Haskell知识体系链接修复脚本
# 用于修复文件间的链接关系，确保一致性

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
Write-Info "       Lean与Haskell知识体系链接修复脚本"
Write-Info "====================================================="
Write-Info "此脚本将修复文件间的链接关系，确保一致性"
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 定义旧文件到新文件的映射
$fileMapping = @{
    "lean_haskell_knowledge_graph.md" = "lean_haskell_unified_knowledge_graph.md"
    "快速导航.md" = "快速导航_统一版.md"
    "快速导航_更新版.md" = "快速导航_统一版.md"
    "整理总结报告.md" = "整理工作报告.md"
    "整理总结报告_更新版.md" = "整理工作报告.md"
    "README.md" = "README_统一版.md"
    "link_fix_plan.md" = "link_fix_plan_new.md"
}

# 定义需要保留的核心文件
$coreFiles = @(
    "lean_haskell_unified_knowledge_graph.md",
    "快速导航_统一版.md",
    "整理工作报告.md",
    "README_统一版.md",
    "check_all.bat",
    "check_links.ps1",
    "fix_links.ps1",
    "fix_links_unified.ps1",
    "check_structure.ps1"
)

# 获取所有Markdown文件
$mdFiles = Get-ChildItem -Path $rootDir -Filter "*.md" -Recurse

# 1. 修复文件内的链接引用
Write-Info "1. 开始修复文件内的链接引用..."
foreach ($file in $mdFiles) {
    $content = Get-Content -Path $file.FullName -Raw
    $modified = $false
    
    # 检查并替换链接引用
    foreach ($oldFile in $fileMapping.Keys) {
        $newFile = $fileMapping[$oldFile]
        if ($content -match [regex]::Escape("($oldFile)") -or $content -match [regex]::Escape("[$oldFile]")) {
            $content = $content -replace [regex]::Escape("($oldFile)"), "($newFile)"
            $content = $content -replace [regex]::Escape("[$oldFile]"), "[$newFile]"
            $modified = $true
            Write-Warning "  在文件 $($file.Name) 中将 $oldFile 替换为 $newFile"
        }
    }
    
    # 保存修改后的内容
    if ($modified) {
        Set-Content -Path $file.FullName -Value $content
        Write-Success "  已更新文件: $($file.Name)"
    }
}

# 2. 更新README_统一版.md中的链接
Write-Info "2. 更新README_统一版.md中的链接..."
$readmePath = Join-Path -Path $rootDir -ChildPath "README_统一版.md"
if (Test-Path $readmePath) {
    $readmeContent = Get-Content -Path $readmePath -Raw
    
    # 确保链接正确
    foreach ($oldFile in $fileMapping.Keys) {
        $newFile = $fileMapping[$oldFile]
        $readmeContent = $readmeContent -replace [regex]::Escape("($oldFile)"), "($newFile)"
        $readmeContent = $readmeContent -replace [regex]::Escape("[$oldFile]"), "[$newFile]"
    }
    
    Set-Content -Path $readmePath -Value $readmeContent
    Write-Success "  已更新README_统一版.md"
}

# 3. 更新快速导航_统一版.md中的链接
Write-Info "3. 更新快速导航_统一版.md中的链接..."
$navPath = Join-Path -Path $rootDir -ChildPath "快速导航_统一版.md"
if (Test-Path $navPath) {
    $navContent = Get-Content -Path $navPath -Raw
    
    # 确保链接正确
    foreach ($oldFile in $fileMapping.Keys) {
        $newFile = $fileMapping[$oldFile]
        $navContent = $navContent -replace [regex]::Escape("($oldFile)"), "($newFile)"
        $navContent = $navContent -replace [regex]::Escape("[$oldFile]"), "[$newFile]"
    }
    
    Set-Content -Path $navPath -Value $navContent
    Write-Success "  已更新快速导航_统一版.md"
}

# 4. 创建文件引用关系图
Write-Info "4. 创建文件引用关系图..."
$relationshipMap = @{}

foreach ($file in $mdFiles) {
    $content = Get-Content -Path $file.FullName -Raw
    $relationshipMap[$file.Name] = @()
    
    # 查找所有Markdown链接
    $linkPattern = '\[([^\]]+)\]\(([^)]+\.md[^)]*)\)'
    $matches = [regex]::Matches($content, $linkPattern)
    
    foreach ($match in $matches) {
        $linkedFile = $match.Groups[2].Value
        # 去除可能的锚点
        $linkedFile = $linkedFile -replace '#.*$', ''
        
        if (-not $relationshipMap[$file.Name].Contains($linkedFile)) {
            $relationshipMap[$file.Name] += $linkedFile
        }
    }
}

# 输出引用关系
$relationshipOutput = "# 文件引用关系图\n\n"
foreach ($file in $relationshipMap.Keys | Sort-Object) {
    $relationshipOutput += "## $file\n\n"
    $relationshipOutput += "引用以下文件:\n\n"
    
    if ($relationshipMap[$file].Count -eq 0) {
        $relationshipOutput += "- 无引用其他文件\n"
    } else {
        foreach ($ref in $relationshipMap[$file] | Sort-Object) {
            $relationshipOutput += "- $ref\n"
        }
    }
    
    $relationshipOutput += "\n"
}

$relationshipPath = Join-Path -Path $rootDir -ChildPath "文件引用关系图.md"
Set-Content -Path $relationshipPath -Value $relationshipOutput
Write-Success "  已创建文件引用关系图: 文件引用关系图.md"

# 5. 检查无效链接
Write-Info "5. 检查无效链接..."
$invalidLinks = @{}

foreach ($file in $mdFiles) {
    $content = Get-Content -Path $file.FullName -Raw
    $invalidLinks[$file.Name] = @()
    
    # 查找所有Markdown链接
    $linkPattern = '\[([^\]]+)\]\(([^)]+\.md[^)]*)\)'
    $matches = [regex]::Matches($content, $linkPattern)
    
    foreach ($match in $matches) {
        $linkedFile = $match.Groups[2].Value
        # 去除可能的锚点
        $cleanLinkedFile = $linkedFile -replace '#.*$', ''
        
        # 检查链接是否有效
        $linkedFilePath = Join-Path -Path $rootDir -ChildPath $cleanLinkedFile
        if (-not (Test-Path $linkedFilePath)) {
            if (-not $invalidLinks[$file.Name].Contains($linkedFile)) {
                $invalidLinks[$file.Name] += $linkedFile
            }
        }
    }
}

# 输出无效链接
$invalidOutput = "# 无效链接报告\n\n"
$hasInvalidLinks = $false

foreach ($file in $invalidLinks.Keys | Sort-Object) {
    if ($invalidLinks[$file].Count -gt 0) {
        $hasInvalidLinks = $true
        $invalidOutput += "## $file\n\n"
        $invalidOutput += "包含以下无效链接:\n\n"
        
        foreach ($link in $invalidLinks[$file] | Sort-Object) {
            $invalidOutput += "- $link\n"
        }
        
        $invalidOutput += "\n"
    }
}

if ($hasInvalidLinks) {
    $invalidPath = Join-Path -Path $rootDir -ChildPath "无效链接报告.md"
    Set-Content -Path $invalidPath -Value $invalidOutput
    Write-Warning "  发现无效链接，详情请查看: 无效链接报告.md"
} else {
    Write-Success "  未发现无效链接"
}

# 6. 创建统一版文件列表
Write-Info "6. 创建统一版文件列表..."
$unifiedFiles = @"
# 统一版文件列表

以下是Lean与Haskell知识体系的核心文件：

## 核心文档

- [统一知识图谱](lean_haskell_unified_knowledge_graph.md)：Lean与Haskell整合统一知识图谱
- [统一快速导航](快速导航_统一版.md)：知识体系快速导航
- [整理工作报告](整理工作报告.md)：整理工作的总结报告
- [统一README](README_统一版.md)：完整的知识体系说明

## 工具脚本

- [链接检查脚本](check_links.ps1)：检查链接有效性
- [链接修复脚本](fix_links_unified.ps1)：修复文件间的链接关系
- [目录结构检查脚本](check_structure.ps1)：检查目录结构完整性
- [一键检查工具](check_all.bat)：自动检查链接和目录结构

## 辅助文档

- [文件引用关系图](文件引用关系图.md)：文件间的引用关系
- [统一版文件列表](统一版文件列表.md)：本文档

---

-*最后更新：2024年整理版本*
"@

$unifiedListPath = Join-Path -Path $rootDir -ChildPath "统一版文件列表.md"
Set-Content -Path $unifiedListPath -Value $unifiedFiles
Write-Success "  已创建统一版文件列表: 统一版文件列表.md"

# 完成
Write-Info ""
Write-Success "链接修复完成！"
Write-Info "=====================================================" 