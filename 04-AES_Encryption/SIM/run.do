vlib work

# Put top level module and small modules in one file 
vlog ../RTL/AES_Encrypt_Only/*.v -Epretty AES_Encrypt_Files.v

# Encrypt this file using auto 3 protect to self Encrypt without envelope except for io signals / parameters
vencrypt -auto3protect AES_Encrypt_Files.v

# Take Copy From AES_Encrypt_Files.v but add Encryption Envelope
vencrypt AES_Encrypt_Envelope.v

# Encrypt All Design Files and add Envelope in Toplevel module only 
vencrypt ../RTL/AES_Encrypt_Only/*.v -d Encrypted_Design_Files
vencrypt -auto3protect ../RTL/AES_Encrypt_Only/AES_Encrypt.v -d Encrypted_Design_Files

vlog AES_Encrypt_Envelope.vp
vlog ./Encrypted_Design_Files/*.vp

vlog ../UVM/*.sv +cover -covercells
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all +UVM_VERBOSITY=UVM_HIGH +UVM_TESTNAME=AES_test
run 0
add wave /top/DUT/*
coverage save AES_top.ucdb -onexit -du work.AES_Encrypt
run -all

coverage report -detail -cvg -comments -output SFC_cov_rprt.txt {}
# quit -sim
# vcover report AES_top.ucdb -details -annotate -all -output CC_SVA_cov_rprt.txt
# vcover report AES_top.ucdb -du=AES_Encrypt -recursive -assert -directive -cvg -codeAll -output cov_rprt_summary.txt

