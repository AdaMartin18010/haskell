# Lean与Haskell知识体系格式统一脚本
# 用于统一文件格式，特别是文件尾的更新日期格式

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
Write-Info "       Lean与Haskell知识体系格式统一脚本"
Write-Info "====================================================="
Write-Info "此脚本将统一文件格式，特别是文件尾的更新日期格式"
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 定义需要处理的核心文件
$coreFiles = @(
    "lean_haskell_unified_knowledge_graph.md",
    "快速导航_统一版.md",
    "整理工作报告.md",
    "README_统一版.md",
    "文件引用关系图.md",
    "统一版文件列表.md",
    "清理计划.md"
)

# 1. 统一文件尾的更新日期格式
Write-Info "1. 统一文件尾的更新日期格式..."

foreach ($file in $coreFiles) {
    $filePath = Join-Path -Path $rootDir -ChildPath $file
    if (Test-Path $filePath) {
        $content = Get-Content -Path $filePath -Raw
        
        # 检查文件是否以更新日期结尾
        if ($content -match '(?m)^[-*].*更新.*[-*][\r\n]*$') {
            # 替换为统一格式
            $content = $content -replace '(?m)^[-*].*更新.*[-*][\r\n]*$', "-*最后更新：2024年整理版本*`n"
            Set-Content -Path $filePath -Value $content
            Write-Success "  已统一文件 $file 的更新日期格式"
        }
        elseif ($content -match '(?m)^[*-].*更新.*[*-][\r\n]*$') {
            # 替换为统一格式
            $content = $content -replace '(?m)^[*-].*更新.*[*-][\r\n]*$', "-*最后更新：2024年整理版本*`n"
            Set-Content -Path $filePath -Value $content
            Write-Success "  已统一文件 $file 的更新日期格式"
        }
        else {
            # 添加更新日期
            if ($content -match '---[\r\n]*$') {
                # 如果文件以分隔线结尾，在分隔线后添加更新日期
                $content = $content -replace '---[\r\n]*$', "---`n`n-*最后更新：2024年整理版本*`n"
            } else {
                # 否则直接在文件末尾添加分隔线和更新日期
                $content = $content.TrimEnd() + "`n`n---`n`n-*最后更新：2024年整理版本*`n"
            }
            Set-Content -Path $filePath -Value $content
            Write-Success "  已添加更新日期到文件 $file"
        }
    } else {
        Write-Warning "  文件 $file 不存在，跳过"
    }
}

# 2. 统一文件头的格式
Write-Info "2. 统一文件头的格式..."

foreach ($file in $coreFiles) {
    $filePath = Join-Path -Path $rootDir -ChildPath $file
    if (Test-Path $filePath) {
        $content = Get-Content -Path $filePath -Raw
        $modified = $false
        
        # 确保文件以标题开头
        if (-not ($content -match '^# ')) {
            $title = $file -replace '\.md$', ''
            $title = $title -replace '_', ' '
            $content = "# $title`n`n$content"
            $modified = $true
        }
        
        # 确保标题后有简介
        if (-not ($content -match '^# .*?\n\n> ')) {
            $titleLine = ($content -split "`n")[0]
            $title = $titleLine -replace '^# ', ''
            
            # 根据文件名生成简介
            $intro = ""
            if ($file -match 'knowledge_graph') {
                $intro = "> 本文档整合了Lean与Haskell的核心知识体系，建立两种语言之间的联系和对比，形成完整的知识图谱。"
            }
            elseif ($file -match '快速导航') {
                $intro = "> 本文档为Haskell与Lean知识体系的快速导航入口，提供关键文档的直接访问链接。"
            }
            elseif ($file -match '整理工作报告') {
                $intro = "> 本报告总结了对Lean与Haskell知识体系文档的整理工作，包括文件整理、内容合并和结构优化。"
            }
            elseif ($file -match 'README') {
                $intro = "> 本知识体系整合了Lean与Haskell的核心概念、设计模式、应用模型、形式模型、执行流、控制流和数据流等方面的知识，构建了完整的函数式编程和形式化方法知识图谱。"
            }
            elseif ($file -match '清理计划') {
                $intro = "> 本文档提供了清理Lean与Haskell知识体系中无关文件和确保一致性的详细计划。"
            }
            else {
                $intro = "> 本文档是Lean与Haskell知识体系的组成部分，提供相关信息和内容。"
            }
            
            $content = $content -replace "^# $title", "# $title`n`n$intro"
            $modified = $true
        }
        
        if ($modified) {
            Set-Content -Path $filePath -Value $content
            Write-Success "  已统一文件 $file 的头部格式"
        }
    } else {
        Write-Warning "  文件 $file 不存在，跳过"
    }
}

# 3. 统一表格和列表格式
Write-Info "3. 统一表格和列表格式..."
# 这部分需要更复杂的处理，暂时跳过

# 4. 统一代码块格式
Write-Info "4. 统一代码块格式..."
foreach ($file in $coreFiles) {
    $filePath = Join-Path -Path $rootDir -ChildPath $file
    if (Test-Path $filePath) {
        $content = Get-Content -Path $filePath -Raw
        $modified = $false
        
        # 确保代码块使用```text而不是```
        if ($content -match '```(?!\w)') {
            $content = $content -replace '```(?!\w)', '```text'
            $modified = $true
        }
        
        if ($modified) {
            Set-Content -Path $filePath -Value $content
            Write-Success "  已统一文件 $file 的代码块格式"
        }
    } else {
        Write-Warning "  文件 $file 不存在，跳过"
    }
}

# 完成
Write-Info ""
Write-Success "格式统一完成！"
Write-Info "=====================================================" 