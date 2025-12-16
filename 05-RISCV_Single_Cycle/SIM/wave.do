onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/clk
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/areset
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/DUT/pc/PC
add wave -noupdate -expand -group FIBONACCI -radix unsigned -childformat {{{/RISCV_TB/DUT/data_mem/data_memory[63]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[62]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[61]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[60]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[59]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[58]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[57]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[56]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[55]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[54]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[53]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[52]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[51]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[50]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[49]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[48]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[47]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[46]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[45]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[44]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[43]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[42]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[41]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[40]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[39]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[38]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[37]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[36]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[35]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[34]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[33]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[32]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[31]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[30]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[29]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[28]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[27]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[26]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[25]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[24]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[23]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[22]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[21]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[20]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[19]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[18]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[17]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[16]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[15]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[14]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[13]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[12]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[11]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[10]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[9]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[8]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[7]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[6]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[5]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[4]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[3]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[2]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[1]} -radix unsigned} {{/RISCV_TB/DUT/data_mem/data_memory[0]} -radix unsigned}} -subitemconfig {{/RISCV_TB/DUT/data_mem/data_memory[63]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[62]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[61]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[60]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[59]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[58]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[57]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[56]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[55]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[54]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[53]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[52]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[51]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[50]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[49]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[48]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[47]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[46]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[45]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[44]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[43]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[42]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[41]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[40]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[39]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[38]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[37]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[36]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[35]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[34]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[33]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[32]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[31]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[30]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[29]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[28]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[27]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[26]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[25]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[24]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[23]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[22]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[21]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[20]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[19]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[18]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[17]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[16]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[15]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[14]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[13]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[12]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[11]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[10]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[9]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[8]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[7]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[6]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[5]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[4]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[3]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[2]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[1]} {-height 15 -radix unsigned} {/RISCV_TB/DUT/data_mem/data_memory[0]} {-height 15 -radix unsigned}} /RISCV_TB/DUT/data_mem/data_memory
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/FIBONACCI
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/error_counter
add wave -noupdate -expand -group FIBONACCI -radix unsigned /RISCV_TB/correct_counter
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/RST_assertion
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ImmExt_assertion_00
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ImmExt_assertion_01
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ImmExt_assertion_10
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ImmExt_assertion_11
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/SrcB_assertion_1
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/SrcB_assertion_0
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/PCNext_assertion_1
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/PCNext_assertion_0
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_0
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_1
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_2
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_4
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_5
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_6
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_7
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/ALU_assertion_3
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/Result_assertion_1
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/Result_assertion_0
add wave -noupdate -group RISCV_SVA -radix unsigned /RISCV_TB/DUT/PC_assertion
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/clk
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/areset
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ALUSrc
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ALUResult
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ALUControl
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ImmExt
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ImmSrc
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/Instr
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/MemWrite
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/PC
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/PCNext
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/PCPlus4
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/PCSrc
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/PCTarget
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/RD2
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ReadData
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/RegWrite
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/Result
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/ResultSrc
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/sign_flag
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/SrcA
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/SrcB
add wave -noupdate -group RISCV_DUT -radix unsigned /RISCV_TB/DUT/Zero
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {25 ns} 0}
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
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {179 ns}
