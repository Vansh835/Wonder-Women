@echo off
setlocal
cd /d "%~dp0"

where py >nul 2>&1
if not errorlevel 1 (
  set "PYRUN=py -3"
) else (
  where python >nul 2>&1
  if errorlevel 1 (
    echo Python 3.10 or newer was not found. Install Python, then try again.
    pause
    exit /b 1
  )
  set "PYRUN=python"
)

%PYRUN% --version >nul 2>&1
if errorlevel 1 (
  echo Could not start Python. Install Python 3.10 or newer, then try again.
  pause
  exit /b 1
)
%PYRUN% -c "import sys; raise SystemExit(0 if sys.version_info >= (3, 10) else 1)"
if errorlevel 1 (
  echo Python 3.10 or newer is required.
  pause
  exit /b 1
)
%PYRUN% -c "import flask, ollama, requests" >nul 2>&1
if errorlevel 1 (
  echo Required Python packages are missing from the regular Python installation.
  choice /M "Install them for this Windows user now"
  if errorlevel 2 exit /b 1
  %PYRUN% -m pip install --user -r requirements.txt
  if errorlevel 1 (
    echo Package installation failed. Check the Python and pip messages above.
    pause
    exit /b 1
  )
)

where ollama >nul 2>&1
if errorlevel 1 (
  echo Ollama was not found. Install Ollama and start it before running this app.
  pause
  exit /b 1
)

ollama list 2>nul | findstr /i "qwen3:latest" >nul
if errorlevel 1 (
  echo Downloading the configured chat model qwen3:latest...
  ollama pull qwen3:latest
  if errorlevel 1 (
    echo Model download failed. Check that Ollama is running and internet is available.
    pause
    exit /b 1
  )
)

set "OLLAMA_NUM_GPU=99"
echo Requesting maximum Ollama GPU layer offload. Ollama may use CPU if GPU support is unavailable or memory is insufficient.
echo Starting the phone-first Safety Shield app...
%PYRUN% safety_shield_gpu.py --mobile
pause