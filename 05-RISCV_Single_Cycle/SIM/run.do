vlib work
vlog -f src_files.list +define+SIM +cover -covercells
vsim -voptargs=+acc work.RISCV_TB -cover -classdebug
do wave.do
coverage save RISCV_TB.ucdb -onexit
run -all
# quit -sim
# vcover report RISCV_TB.ucdb -output RISCV_COV_RPRT.txt -du=RISCV -recursive -assert -directive -cvg -codeAll 
# vcover report RISCV_TB.ucdb -details -annotate -all -output RISCV_COV_RPRT_DETAILS.txt -du=RISCV