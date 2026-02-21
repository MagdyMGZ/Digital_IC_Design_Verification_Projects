module ALSU(ALSU_if.DUT alsu_IF);
parameter INPUT_PRIORITY = "A";
parameter FULL_ADDER = "ON";

reg red_op_A_reg, red_op_B_reg, bypass_A_reg, bypass_B_reg, direction_reg, serial_in_reg;
reg signed [1:0] cin_reg;
reg [2:0] opcode_reg;
reg signed [2:0] A_reg, B_reg;

wire invalid_red_op, invalid_opcode, invalid;

assign invalid_red_op = (red_op_A_reg | red_op_B_reg) & (opcode_reg[1] | opcode_reg[2]);
assign invalid_opcode = opcode_reg[1] & opcode_reg[2];
assign invalid = invalid_red_op | invalid_opcode;

always @(posedge alsu_IF.clk or posedge alsu_IF.reset) begin
  if(alsu_IF.reset) begin
     cin_reg <= 0;
     red_op_B_reg <= 0;
     red_op_A_reg <= 0;
     bypass_B_reg <= 0;
     bypass_A_reg <= 0;
     direction_reg <= 0;
     serial_in_reg <= 0;
     opcode_reg <= 0;
     A_reg <= 0;
     B_reg <= 0;
  end else begin
     cin_reg <= alsu_IF.cin;
     red_op_B_reg <= alsu_IF.red_op_B;
     red_op_A_reg <= alsu_IF.red_op_A;
     bypass_B_reg <= alsu_IF.bypass_B;
     bypass_A_reg <= alsu_IF.bypass_A;
     direction_reg <= alsu_IF.direction;
     serial_in_reg <= alsu_IF.serial_in;
     opcode_reg <= alsu_IF.opcode;
     A_reg <= alsu_IF.A;
     B_reg <= alsu_IF.B;
  end
end

always @(posedge alsu_IF.clk or posedge alsu_IF.reset) begin
  if(alsu_IF.reset) begin
     alsu_IF.leds <= 0;
  end else begin
      if (invalid)
        alsu_IF.leds <= ~alsu_IF.leds;
      else
        alsu_IF.leds <= 0;
  end
end

always @(posedge alsu_IF.clk or posedge alsu_IF.reset) begin
  if(alsu_IF.reset) begin
    alsu_IF.out <= 0;
  end
  else begin
    if (invalid) 
        alsu_IF.out <= 0;
    else if (bypass_A_reg && bypass_B_reg)
      alsu_IF.out <= (INPUT_PRIORITY == "A")? A_reg: B_reg;
    else if (bypass_A_reg)
      alsu_IF.out <= A_reg;
    else if (bypass_B_reg)
      alsu_IF.out <= B_reg;
    else begin
        case (opcode_reg)
          3'h0: begin 
            if (red_op_A_reg && red_op_B_reg)
              alsu_IF.out = (INPUT_PRIORITY == "A")? |A_reg: |B_reg;
            else if (red_op_A_reg) 
              alsu_IF.out <= |A_reg;
            else if (red_op_B_reg)
              alsu_IF.out <= |B_reg;
            else 
              alsu_IF.out <= A_reg | B_reg;
          end
          3'h1: begin
            if (red_op_A_reg && red_op_B_reg)
              alsu_IF.out <= (INPUT_PRIORITY == "A")? ^A_reg: ^B_reg;
            else if (red_op_A_reg) 
              alsu_IF.out <= ^A_reg;
            else if (red_op_B_reg)
              alsu_IF.out <= ^B_reg;
            else 
              alsu_IF.out <= A_reg ^ B_reg;
          end
          3'h2:begin
            if (FULL_ADDER=="ON") begin
              alsu_IF.out <= A_reg + B_reg + cin_reg;
            end
            else
            alsu_IF.out <= A_reg + B_reg;
          end 
          3'h3: alsu_IF.out <= A_reg * B_reg;
          3'h4: begin
            if (direction_reg)
              alsu_IF.out <= alsu_IF.out_shift_reg;
            else
              alsu_IF.out <= alsu_IF.out_shift_reg;
          end
          3'h5: begin
            if (direction_reg)
              alsu_IF.out <= alsu_IF.out_shift_reg;
            else
              alsu_IF.out <= alsu_IF.out_shift_reg;
          end
        endcase
    end 
  end
end

endmodule