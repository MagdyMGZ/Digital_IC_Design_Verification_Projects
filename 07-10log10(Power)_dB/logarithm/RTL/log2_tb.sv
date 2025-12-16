////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: Log2 Testbench
////////////////////////////////////////////////////////////////////////////////
module log2_tb ();

parameter WIDTH  = 32;

logic      [WIDTH-1:0]     log2_in;
logic                      clk;
logic                      rstn;
logic                      enable_in;
logic                      valid_out;
logic      [WIDTH-1:0]     log2_out;     // log2_out[31:24] = Integer Part, log2_out[23:0] = Fraction Part

int error_count, correct_count;

log2 #(.WIDTH(WIDTH)) DUT (.*);

initial begin
    clk = 0;
    forever
        #1 clk = ~clk;
end

initial begin
    rstn = 0;
    @(negedge clk);
    rstn = 1;

    for (int i = 0 ; i <= 1000; i++) begin
        enable_in = 1;
        log2_in = i;
        @(negedge clk);
        enable_in = 0;
        @(negedge clk);
        
        $display("log2_out[%0d] = %0d.%0d", log2_in , log2_out[31:24] , log2_out[23:0]);

        if (valid_out != 1)
            error_count++;
        else
            correct_count++;
    end

    enable_in = 1;
    log2_in = 2**32 - 1;
    @(negedge clk);
    enable_in = 0;
    @(negedge clk);
    
    $display("log2_out[%0d] = %0d.%0d", log2_in , log2_out[31:24] , log2_out[23:0]);

    if (valid_out != 1)
        error_count++;
    else
        correct_count++;

    $display("Error Counter = %0d, Correct Counter = %0d",error_count,correct_count);
    $stop;
end

endmodule