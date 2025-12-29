onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {AHB5 Signals}
add wave -noupdate -radix unsigned /top/AHB5_vif/HCLK
add wave -noupdate -radix unsigned /top/AHB5_vif/HRESETn
add wave -noupdate -radix unsigned /top/AHB5_vif/HREADY
add wave -noupdate -radix unsigned /top/AHB5_vif/HSEL1
add wave -noupdate /top/AHB5_vif/HTRANS
add wave -noupdate -radix unsigned /top/AHB5_vif/HADDR
add wave -noupdate /top/AHB5_vif/HWRITE
add wave -noupdate /top/AHB5_vif/HBURST
add wave -noupdate /top/AHB5_vif/HSIZE
add wave -noupdate -radix unsigned /top/AHB5_vif/HREADYOUT
add wave -noupdate -radix unsigned /top/AHB5_vif/HWDATA
add wave -noupdate -radix unsigned /top/AHB5_vif/HRDATA
add wave -noupdate -radix unsigned /top/AHB5_vif/HWSTRB
add wave -noupdate -radix unsigned /top/AHB5_vif/HRESP
add wave -noupdate -divider {DUT Internals}
add wave -noupdate -radix unsigned /top/DUT/MEM
add wave -noupdate -radix unsigned /top/DUT/address
add wave -noupdate -radix unsigned /top/DUT/error_first_cycle
add wave -noupdate -radix unsigned /top/DUT/error_second_cycle
add wave -noupdate -radix unsigned /top/DUT/mask
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
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
configure wave -timelineunits ps
update
WaveRestoreZoom {99002538 ps} {100068288 ps}
