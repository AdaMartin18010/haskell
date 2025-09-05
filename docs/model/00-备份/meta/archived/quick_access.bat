@echo off
echo ===== Haskell与Lean知识体系快速访问工具 =====
echo.

:menu
cls
echo 请选择要打开的文档:
echo.
echo 1. 快速导航 (推荐入口)
echo 2. 总索引
echo 3. 知识图谱导航
echo 4. 整理总结报告
echo 5. 质量检查清单
echo 6. 链接检查工具
echo 7. 运行目录结构检查脚本
echo 8. 退出
echo.
set /p choice=请输入选项 (1-8): 

if "%choice%"=="1" start notepad 快速导航.md
if "%choice%"=="2" start notepad 10-索引导航\01-总索引.md
if "%choice%"=="3" start notepad 10-索引导航\03-知识图谱导航.md
if "%choice%"=="4" start notepad 整理总结报告.md
if "%choice%"=="5" start notepad 10-索引导航\quality_check.md
if "%choice%"=="6" start notepad 10-索引导航\link_checker.md
if "%choice%"=="7" powershell -ExecutionPolicy Bypass -File check_structure.ps1 && pause
if "%choice%"=="8" goto :eof

echo.
pause
goto menu 