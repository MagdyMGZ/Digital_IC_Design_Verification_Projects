vlib work
vlog -f src_files.list +cover -covercells
vsim -voptargs=+acc work.top -cover -classdebug -uvmcontrol=all
add wave /top/shift_regif/*
run 0
coverage save top.ucdb -onexit
run -all
# quit -sim
# vcover report top.ucdb -details -annotate -all -output cov_report.txt

