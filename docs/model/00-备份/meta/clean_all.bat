@echo off
echo ===================================
echo Lean与Haskell知识体系一键整理工具
echo ===================================
echo.

echo 1. 修复文件间的链接关系...
powershell -ExecutionPolicy Bypass -File fix_links_unified.ps1
echo.

echo 2. 统一文件格式...
powershell -ExecutionPolicy Bypass -File format_unify.ps1
echo.

echo 3. 归档旧版文件...
powershell -ExecutionPolicy Bypass -File archive_files.ps1
echo.

echo 4. 检查链接和目录结构...
call check_all.bat
echo.

echo 整理完成！
echo.
echo 核心文件：
echo  - lean_haskell_unified_knowledge_graph.md：统一知识图谱
echo  - 快速导航_统一版.md：统一快速导航
echo  - 整理工作报告.md：整理工作总结
echo  - README_统一版.md：统一README
echo.
echo 按任意键退出...
pause > nul 