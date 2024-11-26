@echo off
call C:\Xilinx\Vivado\2022.2\settings64.bat

if "%1"=="run" (goto run) 
if "%1"=="cov" (goto cov)
if "%1"=="waves" (goto waves) 
if "%1"=="help" (goto help)
if "%1"=="clean" (goto clean)
if "%1"=="" (goto help)
goto EOF

:run
	echo Making run...
	call xvlog -sv -f alu_tb.f
	call xelab -debug typical -relax alu_tb
	call xsim work.alu_tb -log alu_tb.log -tclbatch "wave.tcl"
	if "%1"=="run" (exit /B 0)

:cov
	echo Making cov...
	call xcrg -report_format html -dir xsim.covdb -report_dir xcrg_report
	if "%1"=="cov" (exit /B 0)

:waves 
	echo Loading waves...
	call vivado -mode batch -source alu_tb.tcl
	if "%1"=="waves" (exit /B 0)

:help
	echo "+-+-+-+-+-+-+ +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ +-+-+-+-+-+-+-+-+"
	echo "|V|i|v|a|d|o| |C|o|m|p|i|l|e|/|S|i|m|u|l|a|t|o|r| |M|a|k|e|.|b|a|t|"
	echo "+-+-+-+-+-+-+ +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+ +-+-+-+-+-+-+-+-+"																																											
	echo " Targets:"

	echo "	run    --> Simulates the design"
	echo "	clean  --> Clean support files"
	echo "	help   --> This help menu!"
	echo "" 
	exit /B 0

:clean
	echo Cleaning...
	call taskkill /IM xvlog.exe /F
	call taskkill /IM xelab.exe /F
	call taskkill /IM xsim.exe /F
	call taskkill /IM xsimk.exe /F
	call taskkill /IM vivado.exe /F
	del /Q xvlog* xelab* xsim* webtalk* tr_db* ana elab sim .Xil vivado* work* xcrg* xsc* *.log

	rmdir /S /Q xsim.dir
	rmdir /S /Q xsim.covdb
	rmdir /S /Q .Xil
	exit /B 0

:EOF
