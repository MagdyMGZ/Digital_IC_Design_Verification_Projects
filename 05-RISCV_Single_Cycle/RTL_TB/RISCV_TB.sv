module RISCV_TB ();

reg clk, areset;

RISCV DUT (.*);

localparam bit[31:0] FIBONACCI_RESULT[0:9] = '{1, 2, 3, 5, 8, 13, 21, 34, 55, 89};

int error_counter, correct_counter;
bit [31:0] FIBONACCI [0:9];

initial begin
    $readmemh("../FIBONACCI/FIBONACCI_INSTR.txt",DUT.instr_mem.RAM);
end

initial begin
    clk = 0;
    forever begin
        #1 clk = ~clk;
    end
end

initial begin
    assert_reset();
    
    repeat(167/2) @(negedge clk);

    FIBONACCI_Checker();

    assert_reset();

    $display("Error Counter = %0d, Correct Counter = %0d",error_counter,correct_counter);
    $stop;
end

task FIBONACCI_Checker ();
    for (int i = 0 ; i <= 9 ; i++) begin
        FIBONACCI[i] = DUT.data_mem.data_memory[i*4];
        if (FIBONACCI[i] !== FIBONACCI_RESULT[i]) begin
            $display("Error in FIBONACCI Result");
            error_counter++;
        end
        else begin
            correct_counter++;
        end
    end
endtask

task assert_reset ();
    areset = 0;
    @(negedge clk);
    areset = 1;
endtask

endmodule