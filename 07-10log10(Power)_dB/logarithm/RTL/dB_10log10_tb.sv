////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: dB Calculation 10.Log10 Testbench
////////////////////////////////////////////////////////////////////////////////
module dB_10log10_tb ();

parameter WIDTH  = 32;

logic     [WIDTH-1:0]     log10_in;
logic                     clk;
logic                     rstn;
logic                     enable_in;
logic                     valid_out;
logic     [WIDTH-1:0]     log10_out;

dB_10log10 #(.WIDTH(WIDTH)) DUT (.*);
int error_count, correct_count;

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
        log10_in = i;
        @(negedge clk);
        enable_in = 0;
        @(negedge clk);
        
        $display("10.log10_out[%0d] = %f", log10_in , fixed8_24_to_real(log10_out));
        
        if (valid_out != 1)
            error_count++;
        else
            correct_count++;
    end

    enable_in = 1;
    log10_in = 2**32 - 1;
    @(negedge clk);
    enable_in = 0;
    @(negedge clk);
    
    $display("10.log10_out[%0d] = %f", log10_in , fixed8_24_to_real(log10_out));

    if (valid_out != 1)
        error_count++;
    else
        correct_count++;

    $display("Error Counter = %0d, Correct Counter = %0d",error_count,correct_count);
    $stop;
end

// Function to convert 8.24 fixed point to real
function real fixed8_24_to_real(bit [31:0] fixed);
    return $itor(fixed) / (2**24);
endfunction

// Function to convert real to 8.24 fixed point
function bit [31:0] real_to_fixed8_24(real val);
    automatic bit [31:0] result;
    result = ($rtoi(val * (2**24)));
    return result;
endfunction

endmodule