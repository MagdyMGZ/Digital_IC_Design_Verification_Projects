onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HCLK
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HRESETn
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HREADY
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HSELx
add wave -noupdate -expand -group {AHB5 Signals} /top/AHB5_vif/HTRANS
add wave -noupdate -expand -group {AHB5 Signals} /top/AHB5_vif/HBURST
add wave -noupdate -expand -group {AHB5 Signals} /top/AHB5_vif/HWRITE
add wave -noupdate -expand -group {AHB5 Signals} /top/AHB5_vif/HSIZE
add wave -noupdate -expand -group {AHB5 Signals} -radix binary /top/AHB5_vif/HWSTRB
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HADDR
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HWDATA
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HREADYOUT
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HRESP
add wave -noupdate -expand -group {AHB5 Signals} -radix unsigned /top/AHB5_vif/HRDATA
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/invalid_trans
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HREADY_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HSELx_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HTRANS_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HBURST_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HWRITE_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HSIZE_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix binary /top/DUT/HWSTRB_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HADDR_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HWDATA_FF
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/HWDATA_mask
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/mask
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/offset
add wave -noupdate -expand -group {AHB5 Internals} -radix unsigned /top/DUT/data_memory
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {22185 ps} 0}
quietly wave cursor active 1
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
WaveRestoreZoom {0 ps} {190524 ps}
