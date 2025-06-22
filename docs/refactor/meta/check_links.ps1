# Meta目录链接检查脚本
# 用于检查Markdown文件中的内部链接有效性

# 设置颜色
$colorGreen = "Green"
$colorRed = "Red"
$colorYellow = "Yellow"
$colorCyan = "Cyan"

Write-Host "===== Meta目录链接检查工具 =====" -ForegroundColor $colorCyan
Write-Host "检查开始时间: $(Get-Date)" -ForegroundColor $colorCyan
Write-Host ""

# 定义要检查的目录
$dirsToCheck = @(
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

# 获取所有Markdown文件
$mdFiles = @()
foreach ($dir in $dirsToCheck) {
    if (Test-Path $dir) {
        $mdFiles += Get-ChildItem -Path $dir -Filter "*.md" -Recurse
    }
}
$mdFiles += Get-ChildItem -Path "*.md" -File

Write-Host "找到 $($mdFiles.Count) 个Markdown文件" -ForegroundColor $colorCyan
Write-Host ""

# 创建文件路径映射，用于快速查找
$fileMap = @{}
foreach ($file in $mdFiles) {
    $relativePath = $file.FullName -replace [regex]::Escape((Get-Location).Path + "\"), ""
    $fileMap[$relativePath] = $true
    # 添加不带路径的文件名，用于同目录链接检查
    $fileMap[$file.Name] = $true
}

# 添加目录映射
foreach ($dir in $dirsToCheck) {
    if (Test-Path $dir) {
        $fileMap["$dir/"] = $true
    }
}

# 定义正则表达式来匹配Markdown链接
$linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
$brokenLinks = @()
$checkedLinks = 0

# 检查每个文件中的链接
foreach ($file in $mdFiles) {
    $fileContent = Get-Content -Path $file.FullName -Raw
    $fileDir = Split-Path -Parent $file.FullName
    $relativePath = $file.FullName -replace [regex]::Escape((Get-Location).Path + "\"), ""
    
    Write-Host "检查文件: $relativePath" -ForegroundColor $colorCyan
    
    # 使用正则表达式查找所有链接
    $matches = [regex]::Matches($fileContent, $linkPattern)
    
    foreach ($match in $matches) {
        $linkText = $match.Groups[1].Value
        $linkUrl = $match.Groups[2].Value
        $checkedLinks++
        
        # 只检查内部链接（不是以http开头的链接）
        if (-not ($linkUrl -match '^https?://')) {
            # 移除锚点部分
            $linkPath = $linkUrl -replace '#.*$', ''
            
            # 跳过空链接
            if ($linkPath -eq "") {
                continue
            }
            
            # 构建完整路径（相对于当前文件）
            $targetPath = ""
            if ($linkPath.StartsWith("../")) {
                # 相对于父目录的链接
                $parentDir = Split-Path -Parent (Split-Path -Parent $relativePath)
                if ($parentDir -eq "") {
                    $targetPath = $linkPath.Substring(3)
                } else {
                    $targetPath = "$parentDir/" + $linkPath.Substring(3)
                }
                $targetPath = $targetPath -replace "\\", "/"
            } elseif ($linkPath.StartsWith("./")) {
                # 相对于当前目录的链接
                $dirPath = Split-Path -Parent $relativePath
                if ($dirPath -eq "") {
                    $targetPath = $linkPath.Substring(2)
                } else {
                    $targetPath = "$dirPath/" + $linkPath.Substring(2)
                }
                $targetPath = $targetPath -replace "\\", "/"
            } elseif ($linkPath.StartsWith("/")) {
                # 绝对路径链接（相对于项目根目录）
                $targetPath = $linkPath.Substring(1)
                $targetPath = $targetPath -replace "\\", "/"
            } elseif ($linkPath.StartsWith("../../")) {
                # 相对于祖父目录的链接
                $grandParentDir = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $relativePath))
                if ($grandParentDir -eq "") {
                    $targetPath = $linkPath.Substring(6)
                } else {
                    $targetPath = "$grandParentDir/" + $linkPath.Substring(6)
                }
                $targetPath = $targetPath -replace "\\", "/"
            } else {
                # 同目录链接
                $dirPath = Split-Path -Parent $relativePath
                if ($dirPath -eq "") {
                    $targetPath = $linkPath
                } else {
                    $targetPath = "$dirPath/$linkPath"
                }
                $targetPath = $targetPath -replace "\\", "/"
            }
            
            # 检查链接是否存在
            if (-not $fileMap.ContainsKey($targetPath)) {
                Write-Host "  [✗] 失效链接: [$linkText]($linkUrl)" -ForegroundColor $colorRed
                $brokenLinks += @{
                    SourceFile = $relativePath
                    LinkText = $linkText
                    LinkUrl = $linkUrl
                    TargetPath = $targetPath
                }
            } else {
                Write-Host "  [✓] 有效链接: [$linkText]($linkUrl)" -ForegroundColor $colorGreen
            }
        }
    }
    
    Write-Host ""
}

# 输出统计信息
Write-Host "===== 检查结果汇总 =====" -ForegroundColor $colorCyan
Write-Host "检查的文件总数: $($mdFiles.Count)" -ForegroundColor $colorCyan
Write-Host "检查的链接总数: $checkedLinks" -ForegroundColor $colorCyan
Write-Host "失效链接总数: $($brokenLinks.Count)" -ForegroundColor $colorCyan

# 输出失效链接详情
if ($brokenLinks.Count -gt 0) {
    Write-Host ""
    Write-Host "===== 失效链接详情 =====" -ForegroundColor $colorRed
    foreach ($link in $brokenLinks) {
        Write-Host "文件: $($link.SourceFile)" -ForegroundColor $colorYellow
        Write-Host "链接文本: $($link.LinkText)" -ForegroundColor $colorYellow
        Write-Host "链接URL: $($link.LinkUrl)" -ForegroundColor $colorYellow
        Write-Host "目标路径: $($link.TargetPath)" -ForegroundColor $colorYellow
        Write-Host "---" -ForegroundColor $colorYellow
    }
}

Write-Host ""
Write-Host "检查完成时间: $(Get-Date)" -ForegroundColor $colorCyan
Write-Host "===== 检查结束 =====" -ForegroundColor $colorCyan 