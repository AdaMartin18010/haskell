# Meta目录链接修复脚本
# 用于修复Markdown文件中的常见链接问题

# 设置颜色
$colorGreen = "Green"
$colorRed = "Red"
$colorYellow = "Yellow"
$colorCyan = "Cyan"

Write-Host "===== Meta目录链接修复工具 =====" -ForegroundColor $colorCyan
Write-Host "修复开始时间: $(Get-Date)" -ForegroundColor $colorCyan
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
    
    # 添加目录映射
    $dirPath = Split-Path -Parent $relativePath
    if ($dirPath -ne "") {
        $fileMap["$dirPath/"] = $true
    }
}

# 定义链接修复规则
$linkFixRules = @(
    # 修复外部链接 - 将/docs/refactor/...改为相对路径
    @{
        Pattern = '/docs/refactor/(.+)'
        Replacement = '../$1'
    },
    # 修复根目录文件链接 - 确保使用正确的相对路径
    @{
        Pattern = '^([^/]+\.md)$'
        ReplacementFunc = {
            param($match, $filePath)
            $targetFile = $match.Groups[1].Value
            $fileDir = Split-Path -Parent $filePath
            if ($fileDir -eq "") {
                # 如果是根目录文件引用根目录文件，保持不变
                return $targetFile
            } else {
                # 如果是子目录文件引用根目录文件，添加../
                return "../$targetFile"
            }
        }
    },
    # 修复目录链接 - 确保目录链接以/结尾
    @{
        Pattern = '(\d+-[^/]+)(?!/)(\))'
        Replacement = '$1/$2'
    }
)

# 定义正则表达式来匹配Markdown链接
$linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
$fixedLinks = 0
$failedFixes = 0

# 修复每个文件中的链接
foreach ($file in $mdFiles) {
    $fileContent = Get-Content -Path $file.FullName -Raw
    $originalContent = $fileContent
    $relativePath = $file.FullName -replace [regex]::Escape((Get-Location).Path + "\"), ""
    
    Write-Host "处理文件: $relativePath" -ForegroundColor $colorCyan
    
    # 使用正则表达式查找所有链接
    $matches = [regex]::Matches($fileContent, $linkPattern)
    $fileModified = $false
    
    foreach ($match in $matches) {
        $linkText = $match.Groups[1].Value
        $linkUrl = $match.Groups[2].Value
        $originalLink = $linkUrl
        $fixed = $false
        
        # 只处理内部链接（不是以http开头的链接）
        if (-not ($linkUrl -match '^https?://')) {
            # 应用修复规则
            foreach ($rule in $linkFixRules) {
                if ($rule.ContainsKey("Pattern")) {
                    $pattern = $rule.Pattern
                    
                    if ($linkUrl -match $pattern) {
                        if ($rule.ContainsKey("Replacement")) {
                            # 使用静态替换
                            $newLinkUrl = $linkUrl -replace $pattern, $rule.Replacement
                        } elseif ($rule.ContainsKey("ReplacementFunc")) {
                            # 使用动态替换函数
                            $newLinkUrl = & $rule.ReplacementFunc $matches $relativePath
                        }
                        
                        # 替换链接
                        $oldLinkPattern = [regex]::Escape("[$linkText]($linkUrl)")
                        $newLink = "[$linkText]($newLinkUrl)"
                        $fileContent = $fileContent -replace $oldLinkPattern, $newLink
                        
                        Write-Host "  [✓] 修复链接: [$linkText]($linkUrl) -> [$linkText]($newLinkUrl)" -ForegroundColor $colorGreen
                        $fixedLinks++
                        $fixed = $true
                        break
                    }
                }
            }
            
            # 如果没有规则匹配，检查链接是否存在
            if (-not $fixed) {
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
                    $fileDir = Split-Path -Parent $relativePath
                    if ($fileDir -eq "") {
                        $targetPath = $linkPath.Substring(3)
                    } else {
                        $parentDir = Split-Path -Parent $fileDir
                        if ($parentDir -eq "") {
                            $targetPath = $linkPath.Substring(3)
                        } else {
                            $targetPath = Join-Path -Path $parentDir -ChildPath ($linkPath.Substring(3))
                        }
                    }
                    $targetPath = $targetPath -replace "\\", "/"
                } elseif ($linkPath.StartsWith("./")) {
                    # 相对于当前目录的链接
                    $fileDir = Split-Path -Parent $relativePath
                    if ($fileDir -eq "") {
                        $targetPath = $linkPath.Substring(2)
                    } else {
                        $targetPath = Join-Path -Path $fileDir -ChildPath ($linkPath.Substring(2))
                    }
                    $targetPath = $targetPath -replace "\\", "/"
                } elseif ($linkPath.StartsWith("/")) {
                    # 绝对路径链接（相对于项目根目录）
                    $targetPath = $linkPath.Substring(1)
                    $targetPath = $targetPath -replace "\\", "/"
                } else {
                    # 同目录链接
                    $fileDir = Split-Path -Parent $relativePath
                    if ($fileDir -eq "") {
                        $targetPath = $linkPath
                    } else {
                        $targetPath = Join-Path -Path $fileDir -ChildPath $linkPath
                    }
                    $targetPath = $targetPath -replace "\\", "/"
                }
                
                # 检查链接是否存在
                if (-not $fileMap.ContainsKey($targetPath)) {
                    Write-Host "  [✗] 无法修复链接: [$linkText]($linkUrl)" -ForegroundColor $colorRed
                    $failedFixes++
                }
            }
        }
    }
    
    # 如果文件内容被修改，则保存
    if ($fileContent -ne $originalContent) {
        Set-Content -Path $file.FullName -Value $fileContent -NoNewline
        $fileModified = $true
        Write-Host "  文件已更新" -ForegroundColor $colorGreen
    } else {
        Write-Host "  文件无需修改" -ForegroundColor $colorYellow
    }
    
    Write-Host ""
}

# 输出统计信息
Write-Host "===== 修复结果汇总 =====" -ForegroundColor $colorCyan
Write-Host "处理的文件总数: $($mdFiles.Count)" -ForegroundColor $colorCyan
Write-Host "修复的链接总数: $fixedLinks" -ForegroundColor $colorCyan
Write-Host "无法修复的链接: $failedFixes" -ForegroundColor $colorCyan

Write-Host ""
Write-Host "修复完成时间: $(Get-Date)" -ForegroundColor $colorCyan
Write-Host "===== 修复结束 =====" -ForegroundColor $colorCyan

# 建议运行链接检查工具验证修复结果
Write-Host ""
Write-Host "建议: 运行链接检查工具验证修复结果:" -ForegroundColor $colorYellow
Write-Host "powershell -ExecutionPolicy Bypass -File check_links.ps1" -ForegroundColor $colorYellow 