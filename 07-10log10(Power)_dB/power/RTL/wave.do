onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group TB -radix unsigned /power_tb/clk
add wave -noupdate -group TB -radix unsigned /power_tb/rstn
add wave -noupdate -group TB -radix unsigned /power_tb/enable_in
add wave -noupdate -group TB -radix decimal /power_tb/real_in
add wave -noupdate -group TB -radix decimal /power_tb/imag_in
add wave -noupdate -group TB -radix unsigned /power_tb/power_out
add wave -noupdate -group TB -radix unsigned /power_tb/power_out_exp
add wave -noupdate -group TB -radix unsigned /power_tb/valid_out
add wave -noupdate -group TB -radix unsigned /power_tb/valid_out_exp
add wave -noupdate -group TB -radix decimal /power_tb/error_count
add wave -noupdate -group TB -radix decimal /power_tb/correct_count
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/clk
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/rstn
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/sel
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/enable_in
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/enable_in_reg
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/real_in
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/real_in_reg
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/imag_in
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/imag_in_reg
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/counter
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/power_out
add wave -noupdate -group DUT -radix unsigned /power_tb/DUT/valid_out
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/mult_in1
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/mult_in2
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/mult_out
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/adder_in1
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/adder_in2
add wave -noupdate -group DUT -radix decimal /power_tb/DUT/adder_out
add wave -noupdate -group SVA -childformat {{/power_tb/valid_out -radix unsigned} {/power_tb/power_out -radix unsigned}} -subitemconfig {/power_tb/valid_out {-radix unsigned} /power_tb/power_out {-radix unsigned}} /power_tb/rstn_assertion
add wave -noupdate -group SVA -childformat {{/power_tb/enable_in -radix unsigned} {/power_tb/imag_in -radix decimal} {/power_tb/real_in -radix decimal} {/power_tb/power_out -radix unsigned} {/power_tb/rstn -radix unsigned}} -subitemconfig {/power_tb/enable_in {-radix unsigned} /power_tb/imag_in {-radix decimal} /power_tb/real_in {-radix decimal} /power_tb/power_out {-radix unsigned} /power_tb/rstn {-radix unsigned}} /power_tb/power_assertion
add wave -noupdate -group SVA -childformat {{/power_tb/enable_in -radix unsigned} {/power_tb/valid_out -radix unsigned} {/power_tb/rstn -radix unsigned}} -subitemconfig {/power_tb/enable_in {-radix unsigned} /power_tb/valid_out {-radix unsigned} /power_tb/rstn {-radix unsigned}} /power_tb/valid_assertion
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {971 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 233
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {966 ns} {1004 ns}
