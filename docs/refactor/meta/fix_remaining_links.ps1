# 修复剩余的链接问题
# 特别是脚本文件和工具链接

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
Write-Info "       修复剩余链接问题"
Write-Info "====================================================="
Write-Info ""

# 定义根目录
$rootDir = $PSScriptRoot
Write-Info "工作目录: $rootDir"

# 1. 创建缺失文件的符号链接
Write-Info "1. 创建缺失文件的符号链接..."

# 创建快速导航.md -> 快速导航_统一版.md 的符号链接
$sourceFile = Join-Path -Path $rootDir -ChildPath "快速导航_统一版.md"
$targetFile = Join-Path -Path $rootDir -ChildPath "快速导航.md"
if (Test-Path $sourceFile) {
    if (-not (Test-Path $targetFile)) {
        Copy-Item -Path $sourceFile -Destination $targetFile
        Write-Success "  已创建: 快速导航.md -> 快速导航_统一版.md"
    } else {
        Write-Warning "  文件已存在: 快速导航.md"
    }
} else {
    Write-Error "  源文件不存在: 快速导航_统一版.md"
}

# 创建整理总结报告.md -> 整理工作报告.md 的符号链接
$sourceFile = Join-Path -Path $rootDir -ChildPath "整理工作报告.md"
$targetFile = Join-Path -Path $rootDir -ChildPath "整理总结报告.md"
if (Test-Path $sourceFile) {
    if (-not (Test-Path $targetFile)) {
        Copy-Item -Path $sourceFile -Destination $targetFile
        Write-Success "  已创建: 整理总结报告.md -> 整理工作报告.md"
    } else {
        Write-Warning "  文件已存在: 整理总结报告.md"
    }
} else {
    Write-Error "  源文件不存在: 整理工作报告.md"
}

# 2. 修复README.md中的工具链接
Write-Info "2. 修复README.md中的工具链接..."
$readmePath = Join-Path -Path $rootDir -ChildPath "README.md"
if (Test-Path $readmePath) {
    $content = Get-Content -Path $readmePath -Raw
    
    # 替换工具链接，去掉./前缀
    $content = $content -replace '\[链接检查脚本\]\(\.\/check_links\.ps1\)', '[链接检查脚本](check_links.ps1)'
    $content = $content -replace '\[链接修复脚本\]\(\.\/fix_links_unified\.ps1\)', '[链接修复脚本](fix_links_unified.ps1)'
    $content = $content -replace '\[目录结构检查脚本\]\(\.\/check_structure\.ps1\)', '[目录结构检查脚本](check_structure.ps1)'
    $content = $content -replace '\[一键检查工具\]\(\.\/check_all\.bat\)', '[一键检查工具](check_all.bat)'
    $content = $content -replace '\[一键整理工具\]\(\.\/clean_all\.bat\)', '[一键整理工具](clean_all.bat)'
    
    Set-Content -Path $readmePath -Value $content
    Write-Success "  已修复README.md中的工具链接"
}

# 3. 修复快速导航_统一版.md中的工具链接
Write-Info "3. 修复快速导航_统一版.md中的工具链接..."
$navPath = Join-Path -Path $rootDir -ChildPath "快速导航_统一版.md"
if (Test-Path $navPath) {
    $content = Get-Content -Path $navPath -Raw
    
    # 替换工具链接，去掉./前缀
    $content = $content -replace '\[链接检查脚本\]\(\.\/check_links\.ps1\)', '[链接检查脚本](check_links.ps1)'
    $content = $content -replace '\[链接修复脚本\]\(\.\/fix_links_unified\.ps1\)', '[链接修复脚本](fix_links_unified.ps1)'
    $content = $content -replace '\[目录结构检查脚本\]\(\.\/check_structure\.ps1\)', '[目录结构检查脚本](check_structure.ps1)'
    
    # 替换使用指南和文件整理计划链接
    $content = $content -replace '\[使用指南\]\(使用指南\.md\)', '[使用指南](README_统一版.md)'
    $content = $content -replace '\[文件整理计划\]\(文件整理计划\.md\)', '[文件整理计划](清理计划.md)'
    
    Set-Content -Path $navPath -Value $content
    Write-Success "  已修复快速导航_统一版.md中的链接"
}

# 4. 修复统一版文件列表.md中的工具链接
Write-Info "4. 修复统一版文件列表.md中的工具链接..."
$listPath = Join-Path -Path $rootDir -ChildPath "统一版文件列表.md"
if (Test-Path $listPath) {
    $content = Get-Content -Path $listPath -Raw
    
    # 替换工具链接，去掉./前缀
    $content = $content -replace '\[链接检查脚本\]\(\.\/check_links\.ps1\)', '[链接检查脚本](check_links.ps1)'
    $content = $content -replace '\[链接修复脚本\]\(\.\/fix_links_unified\.ps1\)', '[链接修复脚本](fix_links_unified.ps1)'
    $content = $content -replace '\[目录结构检查脚本\]\(\.\/check_structure\.ps1\)', '[目录结构检查脚本](check_structure.ps1)'
    $content = $content -replace '\[一键检查工具\]\(\.\/check_all\.bat\)', '[一键检查工具](check_all.bat)'
    
    Set-Content -Path $listPath -Value $content
    Write-Success "  已修复统一版文件列表.md中的工具链接"
}

# 完成
Write-Info ""
Write-Success "链接修复完成！"
Write-Info "=====================================================" 