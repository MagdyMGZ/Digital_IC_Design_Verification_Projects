module top ();
    import top_pkg::*;
    import uvm_pkg::*;
    `include "uvm_macros.svh"    

    bit clk;

    initial begin
        clk = 0;
        forever begin
            #1 clk = ~clk;
        end
    end

    ALSU_if alsu_IF (clk);
    shift_reg_if shift_reg_IF();
    ALSU alsu_dut (alsu_IF);
    shift_reg shift_reg_dut (shift_reg_IF);
    ALSU_Gold alsu_gold (alsu_IF);
    bind ALSU SVA assertions (alsu_IF);

    assign shift_reg_IF.datain = alsu_IF.out;
    assign alsu_IF.out_shift_reg = shift_reg_IF.dataout;
    assign shift_reg_IF.direction = alsu_dut.direction_reg;
    assign shift_reg_IF.serial_in = alsu_dut.serial_in_reg;
    assign shift_reg_IF.mode = alsu_dut.opcode_reg[0];

    initial begin
        uvm_config_db#(virtual ALSU_if)::set(null,"uvm_test_top","ALSU_if",alsu_IF);
        uvm_config_db#(virtual shift_reg_if)::set(null,"uvm_test_top","shift_reg_if",shift_reg_IF);
        run_test("ALSU_test");
    end

endmodule