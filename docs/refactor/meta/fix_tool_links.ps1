# 修复指向工具脚本的链接

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
Write-Info "       修复指向工具脚本的链接"
Write-Info "====================================================="
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 定义链接映射
$linkMapping = @{
    "check_links.ps1" = "./check_links.ps1"
    "fix_links.ps1" = "./fix_links_unified.ps1"
    "fix_links_unified.ps1" = "./fix_links_unified.ps1"
    "check_structure.ps1" = "./check_structure.ps1"
    "check_all.bat" = "./check_all.bat"
    "clean_all.bat" = "./clean_all.bat"
}

# 获取所有Markdown文件
$mdFiles = Get-ChildItem -Path $rootDir -Filter "*.md" | Where-Object { $_.DirectoryName -eq $rootDir }

Write-Info "找到 $($mdFiles.Count) 个Markdown文件"

# 修复链接
foreach ($file in $mdFiles) {
    Write-Info "处理文件: $($file.FullName)"
    $content = Get-Content -Path $file.FullName -Raw
    $modified = $false
    
    # 检查并替换链接
    foreach ($oldLink in $linkMapping.Keys) {
        $newLink = $linkMapping[$oldLink]
        
        # 替换相对路径链接
        if ($content -match [regex]::Escape("($oldLink)") -or $content -match [regex]::Escape("[]($oldLink)")) {
            $content = $content -replace [regex]::Escape("($oldLink)"), "($newLink)"
            $content = $content -replace [regex]::Escape("[]($oldLink)"), "[]($newLink)"
            $modified = $true
            Write-Warning "  替换链接: $oldLink -> $newLink"
        }
    }
    
    # 保存修改后的内容
    if ($modified) {
        Set-Content -Path $file.FullName -Value $content
        Write-Success "  已更新文件: $($file.FullName)"
    } else {
        Write-Info "  文件无需修改: $($file.FullName)"
    }
}

# 完成
Write-Info ""
Write-Success "链接修复完成！"
Write-Info "=====================================================" 