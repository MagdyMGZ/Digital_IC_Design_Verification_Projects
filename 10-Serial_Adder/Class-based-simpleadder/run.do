# Create Library
vlib work

# Compile All files 
vlog -f src_files.list +cover -covercells
vencrypt simpleadder_encrypted.v

# Simulate the testbench
vsim -voptargs=+acc work.simpleadder_oop_tb -sv_seed random -cover -classdebug

# Add all interface signals and assertions on the wave
add wave /adderif/*
add wave /simpleadder_oop_tb/DUT/sva_inst/Adder_Out_Assertion /simpleadder_oop_tb/DUT/sva_inst/Adder_En_O_Assertion

# Save Coverage for Design only for Code and Assertion Coverage
# coverage save adder.ucdb -onexit -du work.simpleadder

# Save Coverage for Code, Assertion, and Functional Coverage
coverage save adder.ucdb -onexit

run -all

# exclude some unused statements to complete 100% Code and Assertion Coverage in Design
coverage exclude -du simpleadder -togglenode counter
coverage exclude -du simpleadder -togglenode state
coverage exclude -du simpleadder -ftrans state st1->st0

# exclude some unused statements to complete 100% Code, Assertion, and Functional Coverage in TB
coverage exclude -src simpleadder_oop_tb.sv -line 67 -code s
coverage exclude -src simpleadder_oop_tb.sv -line 68 -code s
coverage exclude -src simpleadder_oop_tb.sv -line 69 -code s
coverage exclude -src simpleadder_oop_tb.sv -line 70 -code s
coverage exclude -src simpleadder_oop_tb.sv -line 71 -code s
coverage exclude -src adder_checker.svh -line 15 -code s
coverage exclude -src adder_checker.svh -line 19 -code s
coverage exclude -src adder_checker.svh -line 16 -code s
coverage exclude -src adder_checker.svh -line 14 -code b
coverage exclude -src adder_checker.svh -line 14 -code c

# Quit to Save Coverage database and Execute the Reports
# quit -sim
# vcover report adder.ucdb -details -annotate -all -output code_assert_cov_report.txt
# vcover report adder.ucdb -details -annotate -all -output func_cov_report.txt