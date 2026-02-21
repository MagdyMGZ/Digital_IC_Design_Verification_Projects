vlib work

# Compile C Code
if {![file exists "DPI_C_GM.dll"]} {
    puts "DPI_C_GM.dll not found. so, compiling Golden_model_caller.c"
    exec gcc -m64 -shared -fPIC -o DPI_C_GM.dll Golden_model_caller.c
} else {
    puts "DPI_C_GM.dll already exists. so, skipping compilation"
}

# Compile UVM 1.2
vlog -sv +incdir+C:/questasim64_2021.1/verilog_src/uvm-1.2/src C:/questasim64_2021.1/verilog_src/uvm-1.2/src/uvm_pkg.sv

# Put top level module and small modules in one file 
vlog ../RTL/AES_Encrypt_Only/*.v -Epretty AES_Encrypt_Files.v

# Encrypt this file using auto 3 protect to self Encrypt without envelope except for io signals / parameters
vencrypt -auto3protect AES_Encrypt_Files.v

# Take Copy From AES_Encrypt_Files.v but add Encryption Envelope
vencrypt AES_Encrypt_Envelope.v

# Encrypt All Design Files and add Envelope in Toplevel module only except for ios and parameters using -auto3protect
vencrypt ../RTL/AES_Encrypt_Only/*.v -d Encrypted_Design_Files
vencrypt -auto3protect ../RTL/AES_Encrypt_Only/AES_Encrypt.v -d Encrypted_Design_Files

vlog ./Encrypted_Design_Files/*.vp
vlog AES_Encrypt_Envelope.vp

# vlog -sv Golden_model_caller.c
vlog -sv +incdir+C:/questasim64_2021.1/verilog_src/uvm-1.2/src ../UVM/*.sv +cover -covercells +define+AES_ASSERT

vsim -voptargs=+acc -sv_lib DPI_C_GM work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME=AES_test -sv_lib C:/questasim64_2021.1/uvm-1.2/win64/uvm_dpi
run 0
add wave /top/DUT/*
coverage save AES_top.ucdb -onexit -du work.AES_Encrypt_Encrypted
run -all

coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
coverage report -output functional_coverage_rpt.txt -srcfile=* -detail -all -dump -annotate -directive -cvg
coverage report -output assertion_coverage.txt -detail -assert
# quit -sim
# vcover report AES_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report AES_top.ucdb -du=AES_Encrypt_Encrypted -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt
