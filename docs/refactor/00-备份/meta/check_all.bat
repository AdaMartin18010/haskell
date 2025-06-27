@echo off
echo ===================================
echo Lean与Haskell知识体系检查工具
echo ===================================
echo.

echo 1. 检查目录结构...
powershell -ExecutionPolicy Bypass -File check_structure.ps1
echo.

echo 2. 检查链接有效性...
powershell -ExecutionPolicy Bypass -File check_links.ps1
echo.

echo 3. 生成报告...
echo 检查完成，报告已生成 > check_report.txt
powershell -Command "Get-Date -Format 'yyyy-MM-dd HH:mm:ss'" >> check_report.txt
echo 目录结构检查结果: >> check_report.txt
powershell -ExecutionPolicy Bypass -Command "& {$result = & './check_structure.ps1'; $result | Out-File -Append -FilePath check_report.txt}"
echo. >> check_report.txt
echo 链接检查结果: >> check_report.txt
powershell -ExecutionPolicy Bypass -Command "& {$result = & './check_links.ps1'; $result | Out-File -Append -FilePath check_report.txt}"

echo 检查完成！结果已保存到 check_report.txt
echo.
echo 按任意键退出...
pause > nul 