# 工具链接修复脚本
# 用于修复工具链接引用问题

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
Write-Info "       工具链接修复脚本"
Write-Info "====================================================="
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 1. 复制工具脚本到各子目录
Write-Info "1. 创建工具脚本的符号链接..."

# 定义工具脚本
$toolScripts = @(
    "check_links.ps1",
    "fix_links_unified.ps1",
    "check_structure.ps1",
    "check_all.bat",
    "clean_all.bat"
)

# 确保工具脚本存在
foreach ($script in $toolScripts) {
    $scriptPath = Join-Path -Path $rootDir -ChildPath $script
    if (-not (Test-Path $scriptPath)) {
        Write-Error "  工具脚本不存在: $script"
    } else {
        Write-Success "  工具脚本已存在: $script"
    }
}

# 2. 修复快速导航_统一版.md中的工具链接
Write-Info "2. 修复快速导航_统一版.md中的工具链接..."
$navPath = Join-Path -Path $rootDir -ChildPath "快速导航_统一版.md"
if (Test-Path $navPath) {
    $content = Get-Content -Path $navPath -Raw
    
    # 检查是否需要修复
    $needsFix = $false
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]\(\.\/") {
            $needsFix = $true
            break
        }
    }
    
    if ($needsFix) {
        # 替换工具链接，去掉./前缀
        foreach ($script in $toolScripts) {
            $content = $content -replace "\[([^]]+)\]\(\./$script\)", "[$1]($script)"
        }
        
        Set-Content -Path $navPath -Value $content
        Write-Success "  已修复快速导航_统一版.md中的工具链接"
    } else {
        Write-Info "  快速导航_统一版.md中的工具链接已经正确"
    }
} else {
    Write-Error "  文件不存在: 快速导航_统一版.md"
}

# 3. 修复统一版文件列表.md中的工具链接
Write-Info "3. 修复统一版文件列表.md中的工具链接..."
$listPath = Join-Path -Path $rootDir -ChildPath "统一版文件列表.md"
if (Test-Path $listPath) {
    $content = Get-Content -Path $listPath -Raw
    
    # 检查是否需要修复
    $needsFix = $false
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]\(\.\/") {
            $needsFix = $true
            break
        }
    }
    
    if ($needsFix) {
        # 替换工具链接，去掉./前缀
        foreach ($script in $toolScripts) {
            $content = $content -replace "\[([^]]+)\]\(\./$script\)", "[$1]($script)"
        }
        
        Set-Content -Path $listPath -Value $content
        Write-Success "  已修复统一版文件列表.md中的工具链接"
    } else {
        Write-Info "  统一版文件列表.md中的工具链接已经正确"
    }
} else {
    Write-Error "  文件不存在: 统一版文件列表.md"
}

# 4. 修复README_统一版.md中的工具链接
Write-Info "4. 修复README_统一版.md中的工具链接..."
$readmePath = Join-Path -Path $rootDir -ChildPath "README_统一版.md"
if (Test-Path $readmePath) {
    $content = Get-Content -Path $readmePath -Raw
    
    # 检查是否需要修复
    $needsFix = $false
    foreach ($script in $toolScripts) {
        if ($content -match "\[$script\]\(\.\/") {
            $needsFix = $true
            break
        }
    }
    
    if ($needsFix) {
        # 替换工具链接，去掉./前缀
        foreach ($script in $toolScripts) {
            $content = $content -replace "\[([^]]+)\]\(\./$script\)", "[$1]($script)"
        }
        
        Set-Content -Path $readmePath -Value $content
        Write-Success "  已修复README_统一版.md中的工具链接"
    } else {
        Write-Info "  README_统一版.md中的工具链接已经正确"
    }
} else {
    Write-Error "  文件不存在: README_统一版.md"
}

# 完成
Write-Info ""
Write-Success "工具链接修复完成！"
Write-Info "=====================================================" 
Write-Info "=====================================================" 