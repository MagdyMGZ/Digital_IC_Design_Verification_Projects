////////////////////////////////////////////////////////////////////////////////
// Author: Magdy Ahmed Abbas
// Company: Consultix 
// Description: Power Calculation Verilog Design using 1 Multiplier & 1 Adder
////////////////////////////////////////////////////////////////////////////////
module power #(
    parameter   IN_WIDTH  = 16
) (
    input       wire    signed      [IN_WIDTH-1:0]      real_in,
    input       wire    signed      [IN_WIDTH-1:0]      imag_in,
    input       wire                                    clk,
    input       wire                                    rstn,
    input       wire                                    enable_in,
    output      reg                 [2*IN_WIDTH-1:0]    power_out,
    output      reg                                     valid_out
);

// Power = (real + imag * i) x conjugate (real + imag * i)
// Power = (real + imag * i) x (real - imag * i)
// Power = real^2 + imag^2 = real x real + imag x imag

reg       sel;
reg [1:0] counter;

reg  signed [IN_WIDTH-1:0]   real_in_reg, imag_in_reg;
reg                          enable_in_reg;

reg  signed [IN_WIDTH-1:0]   mult_in1, mult_in2;
wire        [2*IN_WIDTH-1:0] mult_out;

reg         [2*IN_WIDTH-1:0] adder_in1, adder_in2;
wire        [2*IN_WIDTH-1:0] adder_out;

multiplier #(.IN_WIDTH(IN_WIDTH)) mult_instance (
    .mult_in1(mult_in1),
    .mult_in2(mult_in2),
    .mult_out(mult_out)
);

adder #(.IN_WIDTH(IN_WIDTH)) adder_instance (
    .adder_in1(adder_in1),
    .adder_in2(adder_in2),
    .adder_out(adder_out)
);

// Register the Inputs 
always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        real_in_reg <= 0;
        imag_in_reg <= 0;
        enable_in_reg <= 0;
    end
    else if (enable_in) begin
        real_in_reg <= real_in;
        imag_in_reg <= imag_in;
        enable_in_reg <= enable_in;
    end
    else begin
        if (counter == 3) begin
            real_in_reg <= 0;
            imag_in_reg <= 0;
            enable_in_reg <= 0;
        end
    end
end

// Generation the logic of Selection signal
always @(posedge clk or negedge rstn) begin
    if (!rstn)
        sel <= 0;
    else if (enable_in_reg)
        sel <= !sel;
    else
        sel <= 0;
end

// Multiplier Block
always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        mult_in1 <= 0;
        mult_in2 <= 0;
    end
    else if (enable_in_reg) begin
        if (!sel) begin
            mult_in1 <= real_in;
            mult_in2 <= real_in;
        end
        else begin
            mult_in1 <= imag_in;
            mult_in2 <= imag_in;
        end
    end
    else begin
        mult_in1 <= 0;
        mult_in2 <= 0;
    end
end

// Adder Block
always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        adder_in1 <= 0;
        adder_in2 <= 0;
    end
    else if (enable_in_reg) begin
        if (sel) 
            adder_in1 <= mult_out; // real^2
        else 
            adder_in2 <= mult_out; // imag^2
    end
    else begin
        adder_in1 <= 0;
        adder_in2 <= 0;
    end
end

// output block
always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        power_out <= 0;
        valid_out <= 0;
    end
    else if (enable_in_reg) begin
        if (counter == 3) begin
            power_out <= adder_out;
            valid_out <= 1;
        end
        else begin
            power_out <= 0;
            valid_out <= 0;
        end
    end
    else begin
        power_out <= 0;
        valid_out <= 0;
    end
end

always @(posedge clk or negedge rstn) begin
    if (!rstn)
        counter <= 0;
    else if (enable_in_reg) begin
        if (counter == 3)
            counter <= 0;
        else
            counter <= counter + 1'b1; 
    end
    else 
        counter <= 0;
end
    
endmodule