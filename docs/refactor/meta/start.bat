@echo off
echo Lean与Haskell知识体系导航启动器
echo ============================
echo.

echo 正在打开主要导航文件...
start "" "快速导航.md"

echo.
echo 可选操作:
echo 1. 打开核心知识图谱
echo 2. 打开深度分析
echo 3. 打开设计模式
echo 4. 打开类型系统
echo 5. 打开执行流控制流
echo 6. 打开形式化方法
echo 7. 打开实践指南
echo 8. 打开关联分析
echo 9. 打开进度报告
echo 0. 退出

set /p choice=请选择操作(0-9): 

if "%choice%"=="1" start "" "01-核心知识图谱\01-知识图谱-核心.md"
if "%choice%"=="2" start "" "02-深度分析\01-深度分析-整合.md"
if "%choice%"=="3" start "" "03-设计模式\01-设计模式-函数式.md"
if "%choice%"=="4" start "" "04-类型系统\01-类型系统-对比.md"
if "%choice%"=="5" start "" "05-执行流控制流\01-执行流-控制流.md"
if "%choice%"=="6" start "" "06-形式化方法\01-形式化验证.md"
if "%choice%"=="7" start "" "07-实践指南\01-technology-selection-guide.md"
if "%choice%"=="8" start "" "08-关联分析\01-design-patterns-correlation.md"
if "%choice%"=="9" start "" "09-进度报告\01-当前状态.md"
if "%choice%"=="0" exit

echo.
echo 操作完成!
pause 