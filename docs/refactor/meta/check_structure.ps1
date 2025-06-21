# Meta目录结构检查脚本
# 用于检查目录结构完整性和文件状态

# 设置颜色
$colorGreen = "Green"
$colorRed = "Red"
$colorYellow = "Yellow"
$colorCyan = "Cyan"

Write-Host "===== Meta目录结构检查工具 =====" -ForegroundColor $colorCyan
Write-Host "检查开始时间: $(Get-Date)" -ForegroundColor $colorCyan
Write-Host ""

# 定义预期的目录结构
$expectedDirs = @(
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

# 定义必要的文件
$essentialFiles = @(
    "README.md",
    "快速导航.md",
    "整理总结报告.md",
    "10-索引导航/01-总索引.md",
    "10-索引导航/02-快速导航.md",
    "10-索引导航/03-知识图谱导航.md",
    "10-索引导航/quality_check.md",
    "10-索引导航/link_checker.md"
)

# 检查目录结构
Write-Host "1. 检查目录结构" -ForegroundColor $colorCyan
$missingDirs = @()
foreach ($dir in $expectedDirs) {
    if (Test-Path $dir) {
        Write-Host "  [✓] $dir" -ForegroundColor $colorGreen
    } else {
        Write-Host "  [✗] $dir (缺失)" -ForegroundColor $colorRed
        $missingDirs += $dir
    }
}

# 检查必要文件
Write-Host ""
Write-Host "2. 检查必要文件" -ForegroundColor $colorCyan
$missingFiles = @()
foreach ($file in $essentialFiles) {
    if (Test-Path $file) {
        Write-Host "  [✓] $file" -ForegroundColor $colorGreen
    } else {
        Write-Host "  [✗] $file (缺失)" -ForegroundColor $colorRed
        $missingFiles += $file
    }
}

# 检查README文件
Write-Host ""
Write-Host "3. 检查各目录README文件" -ForegroundColor $colorCyan
$missingReadmes = @()
foreach ($dir in $expectedDirs) {
    if (Test-Path $dir) {
        $readmePath = Join-Path $dir "README.md"
        if (Test-Path $readmePath) {
            Write-Host "  [✓] $dir/README.md" -ForegroundColor $colorGreen
        } else {
            Write-Host "  [✗] $dir/README.md (缺失)" -ForegroundColor $colorRed
            $missingReadmes += $readmePath
        }
    }
}

# 检查空目录
Write-Host ""
Write-Host "4. 检查空目录" -ForegroundColor $colorCyan
$emptyDirs = @()
foreach ($dir in $expectedDirs) {
    if (Test-Path $dir) {
        $files = Get-ChildItem $dir -File | Where-Object { $_.Name -ne "README.md" }
        if ($files.Count -eq 0) {
            Write-Host "  [!] $dir (空目录)" -ForegroundColor $colorYellow
            $emptyDirs += $dir
        } else {
            Write-Host "  [✓] $dir (包含 $($files.Count) 个文件)" -ForegroundColor $colorGreen
        }
    }
}

# 输出统计信息
Write-Host ""
Write-Host "===== 检查结果汇总 =====" -ForegroundColor $colorCyan
Write-Host "目录总数: $($expectedDirs.Count)" -ForegroundColor $colorCyan
Write-Host "缺失目录: $($missingDirs.Count)" -ForegroundColor $colorCyan
Write-Host "必要文件总数: $($essentialFiles.Count)" -ForegroundColor $colorCyan
Write-Host "缺失文件: $($missingFiles.Count)" -ForegroundColor $colorCyan
Write-Host "缺失README: $($missingReadmes.Count)" -ForegroundColor $colorCyan
Write-Host "空目录: $($emptyDirs.Count)" -ForegroundColor $colorCyan

# 输出建议
Write-Host ""
Write-Host "===== 建议操作 =====" -ForegroundColor $colorCyan
if ($missingDirs.Count -gt 0) {
    Write-Host "1. 创建缺失的目录:" -ForegroundColor $colorYellow
    foreach ($dir in $missingDirs) {
        Write-Host "   mkdir $dir" -ForegroundColor $colorYellow
    }
}

if ($missingFiles.Count -gt 0) {
    Write-Host "2. 创建缺失的必要文件:" -ForegroundColor $colorYellow
    foreach ($file in $missingFiles) {
        Write-Host "   New-Item -Path '$file' -ItemType File" -ForegroundColor $colorYellow
    }
}

if ($missingReadmes.Count -gt 0) {
    Write-Host "3. 为以下目录添加README.md:" -ForegroundColor $colorYellow
    foreach ($readme in $missingReadmes) {
        Write-Host "   New-Item -Path '$readme' -ItemType File" -ForegroundColor $colorYellow
    }
}

if ($emptyDirs.Count -gt 0) {
    Write-Host "4. 为以下空目录添加内容:" -ForegroundColor $colorYellow
    foreach ($dir in $emptyDirs) {
        Write-Host "   $dir" -ForegroundColor $colorYellow
    }
}

Write-Host ""
Write-Host "检查完成时间: $(Get-Date)" -ForegroundColor $colorCyan
Write-Host "===== 检查结束 =====" -ForegroundColor $colorCyan 