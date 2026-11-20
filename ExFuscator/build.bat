@echo off
setlocal enabledelayedexpansion

set SOURCES=src\Main.cpp src\astra\Config.cpp src\astra\cff\CfgFlow.cpp src\astra\core\Obfuscator.cpp src\astra\emitter\Emitter.cpp src\astra\lexer\Lexer.cpp src\astra\parser\Parser.cpp
for %%f in (src\astra\passes\*.cpp) do set SOURCES=!SOURCES! %%f
for %%f in (src\astra\vm\*.cpp) do set SOURCES=!SOURCES! %%f

if exist exfuscator.exe del exfuscator.exe

where cl >nul 2>nul
if not errorlevel 1 goto msvc

where g++ >nul 2>nul
if errorlevel 1 goto nocompiler
goto mingw

:msvc
cl /nologo /O2 /EHsc /std:c++17 /Isrc %SOURCES% /Fe:exfuscator.exe
if errorlevel 1 goto fail
goto done

:mingw
g++ -std=c++17 -O2 -Isrc %SOURCES% -o exfuscator.exe
if errorlevel 1 goto fail
goto done

:nocompiler
echo error: no C++ compiler found in PATH.
echo.
echo   option 1: install Visual Studio Build Tools with the
echo             "Desktop development with C++" workload, then run this
echo             from the "x64 Native Tools Command Prompt for VS".
echo   option 2: install MinGW-w64 (w64devkit) and add its bin folder to PATH.
echo   option 3: just use the prebuilt exfuscator.exe - no compiler needed.
echo.
exit /b 1

:fail
echo build failed
exit /b 1

:done
if not exist exfuscator.exe goto fail
echo build done -^> exfuscator.exe
exit /b 0
