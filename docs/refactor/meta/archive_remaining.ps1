# 归档剩余的非核心文件

# 定义根目录
$rootDir = $PSScriptRoot
Write-Host "工作目录: $rootDir"

# 定义归档目录
$archiveDir = Join-Path -Path $rootDir -ChildPath "archived"
if (-not (Test-Path $archiveDir)) {
    New-Item -Path $archiveDir -ItemType Directory | Out-Null
    Write-Host "已创建归档目录: archived/"
} else {
    Write-Host "归档目录已存在: archived/"
}

# 定义需要归档的非核心文件
$filesToArchive = @(
    "使用指南.md",
    "文件整理计划.md",
    "无效链接报告.md",
    "start.bat",
    "quick_access.bat",
    "fix_links.ps1"
)

# 移动文件到归档目录
foreach ($file in $filesToArchive) {
    $filePath = Join-Path -Path $rootDir -ChildPath $file
    $destPath = Join-Path -Path $archiveDir -ChildPath $file
    
    if (Test-Path $filePath) {
        # 检查目标文件是否已存在
        if (Test-Path $destPath) {
            $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
            $extension = if ($file -match '\.md$') { ".md" } else { [System.IO.Path]::GetExtension($file) }
            $baseName = [System.IO.Path]::GetFileNameWithoutExtension($file)
            $destPath = Join-Path -Path $archiveDir -ChildPath "${baseName}_${timestamp}${extension}"
        }
        
        # 移动文件
        Move-Item -Path $filePath -Destination $destPath
        Write-Host "已归档文件: $file -> archived/$($destPath | Split-Path -Leaf)"
    } else {
        Write-Host "文件不存在，跳过: $file"
    }
}

Write-Host "归档完成！" 