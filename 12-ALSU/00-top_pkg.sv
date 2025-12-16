package top_pkg;

parameter MAXPOS =3;
parameter MAXNEG =-4;
parameter ZERO   =0;

typedef enum  {or_op,xor_op,add_op,mul_op,shift_op,rot_op,INVALID_6,INVALID_7} opcode_e;
typedef enum  {OR,XOR,ADD,MULT,SHIFT,ROTATE} opcode_valid_e;
import uvm_pkg::*;
`include "uvm_macros.svh"
`include "02-ALSU_seq_item.svh"
`include "02-shift_seq_item.svh"
`include "03-ALSU_sequence.svh"
`include "03-shift_reg_sequence.svh"
`include "04-ALSU_sequencer.svh"
`include "04-shift_reg_sequencer.svh"
`include "05-ALSU_driver.svh"
`include "05-shift_reg_driver.svh"
`include "06-ALSU_monitor.svh"
`include "06-shift_reg_monitor.svh"
`include "07-ALSU_config_obj.svh"
`include "07-shift_reg_config_obj.svh"
`include "08-ALSU_agent.svh"
`include "08-shift_reg_agent.svh"
`include "09-ALSU_coverage_collector.svh"
`include "09-shift_reg_coverage_collector.svh"
`include "10-ALSU_scoreboard.svh"
`include "10-shift_reg_scoreboard.svh"
`include "11-ALSU_env.svh"
`include "11-shift_reg_env.svh"
`include "12-ALSU_test.svh"
endpackage