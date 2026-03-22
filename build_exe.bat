@echo off
cd /d %~dp0

if not exist venv (
    py -m venv venv
)

call venv\Scripts\activate
python -m pip install --upgrade pip
pip install -r requirements.txt
pip install pyinstaller

pyinstaller --noconfirm --onefile --windowed --name LitPilot litpilot.py

echo.
echo Build finished. EXE is in dist\LitPilot.exe
pause