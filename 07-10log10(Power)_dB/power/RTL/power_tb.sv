////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: Power Calculation Testbench
////////////////////////////////////////////////////////////////////////////////
class rand_in;
    parameter   IN_WIDTH  = 16;
    localparam  OUT_WIDTH = 2 * IN_WIDTH;

    randc    logic    signed      [IN_WIDTH-1:0]      real_in;
    randc    logic    signed      [IN_WIDTH-1:0]      imag_in;
    rand     logic                                    rstn;
             logic                [OUT_WIDTH-1:0]     power_out;
             logic                                    valid_out;
    
    constraint rstn_c { rstn dist {0:/2, 1:/98}; }

    covergroup cvr_grp;
        coverpoint real_in;
        coverpoint imag_in;
        coverpoint rstn;
        coverpoint valid_out;
        coverpoint power_out {bins power_values = {[0:2147483647]};}
    endgroup
    
    function new ();
        cvr_grp = new();
    endfunction
endclass

module power_tb ();

parameter   IN_WIDTH  = 16;
localparam  OUT_WIDTH = 2 * IN_WIDTH;

logic    signed      [IN_WIDTH-1:0]      real_in;
logic    signed      [IN_WIDTH-1:0]      imag_in;
logic                                    clk;
logic                                    rstn;
logic                                    enable_in;

logic                [OUT_WIDTH-1:0]     power_out;
logic                                    valid_out;

logic                [OUT_WIDTH-1:0]     power_out_exp;
logic                                    valid_out_exp;

int error_count, correct_count;

power #(.IN_WIDTH(IN_WIDTH)) DUT (.*);

initial begin
    clk = 0;
    forever 
        #1 clk = ~clk;
end

rand_in randin = new();

initial begin
    rstn = 0;
    @(negedge clk);
    rstn = 1;

    repeat (10000) begin
        assert(randin.randomize());
        real_in = randin.real_in;
        imag_in = randin.imag_in;
        rstn = randin.rstn;
        enable_in = 1;
        @(negedge clk);
        golden_model ();
        enable_in = 0;
        power_check ();
        randin.power_out = power_out;
        randin.valid_out = valid_out;
        randin.cvr_grp.sample();
    end

    $display("Error Count = %0d, Correct Count = %0d",error_count,correct_count);
    $stop;
end

task power_check ();
    repeat(4) @(negedge clk);
    if ((power_out !== power_out_exp) || (valid_out !== valid_out_exp))
        error_count++;
    else
        correct_count++;
endtask

task golden_model ();
    if (!rstn) begin
        power_out_exp = 0;
        valid_out_exp = 0;
    end
    else begin
        if (enable_in) begin
            power_out_exp = ((real_in**2) + (imag_in**2));
            valid_out_exp = 1;
        end
        else begin
            power_out_exp = 0;
            valid_out_exp = 0;
        end
    end
endtask

always_comb begin
    if (!rstn) begin
        rstn_assertion : assert final (~power_out && !valid_out);
        rstn_cover     : cover final (~power_out && !valid_out);
    end
end

property power_property;
    @(posedge clk) disable iff (!rstn) $rose(enable_in) |-> ##5 (power_out == (($past(real_in,5) ** 2) + ($past(imag_in,5) ** 2)) [->1]);
endproperty

power_assertion : assert property (power_property);
power_cover     : cover property (power_property);

property valid_property;
    @(posedge clk) disable iff (!rstn) $rose(enable_in) |-> ##5 $rose(valid_out) ##1 $fell(valid_out); 
endproperty

valid_assertion : assert property (valid_property);
valid_cover     : cover property (valid_property);

endmodule