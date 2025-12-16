module ALSU_Gold (ALSU_if.DUT_GOLD alsu_IF);

parameter  INPUT_PRIORITY="A";
parameter  FULL_ADDER="ON";

reg red_op_A_reg, red_op_B_reg, bypass_A_reg, bypass_B_reg, direction_reg, serial_in_reg;
reg signed [1:0] cin_reg;
reg [2:0] opcode_reg;
reg signed [2:0] A_reg, B_reg;

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
    if(alsu_IF.reset)begin
      alsu_IF.out_G<=6'h00;
     alsu_IF.leds_G<=16'h0000;
    end
    else begin
        case (opcode_reg)
     3'b000:begin
        if (red_op_A_reg && red_op_B_reg)
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=|A_reg; else alsu_IF.out_G<=|A_reg;
         else if (red_op_A_reg) 
            alsu_IF.out_G <= |A_reg;
         else if (red_op_B_reg)
            alsu_IF.out_G<= |B_reg;
            else
            alsu_IF.out_G<= A_reg|B_reg;

         if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
            end
            else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
            end
            else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
            end     
     end
     3'b001:begin
        if (red_op_A_reg && red_op_B_reg)
              if (INPUT_PRIORITY=="A") alsu_IF.out_G<=^A_reg; else alsu_IF.out_G<=^B_reg;
            else if (red_op_A_reg) 
              alsu_IF.out_G<= ^A_reg;
            else if (red_op_B_reg)
              alsu_IF.out_G<= ^B_reg;
             else
              alsu_IF.out_G<= A_reg^B_reg; 

         if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
            end
            else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
            end
            else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
            end           
     end
     3'b010:begin
        if (red_op_A_reg || red_op_B_reg)begin
           alsu_IF.out_G =0;
           alsu_IF.leds_G=~alsu_IF.leds_G;
        end
         else if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
         end
         else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
         end
         else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
         end   
        else begin
           if (FULL_ADDER == "ON")
               alsu_IF.out_G<=A_reg+B_reg+cin_reg; 
            else
               alsu_IF.out_G<=A_reg+B_reg; 
        end
     end
     3'b011:begin
        if (red_op_A_reg || red_op_B_reg) begin
           alsu_IF.out_G =0;
           alsu_IF.leds_G=~alsu_IF.leds_G;
        end
         else if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
         end
         else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
         end
         else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
         end   
        else begin
           alsu_IF.out_G<=A_reg*B_reg; 
        end        
     end
     3'b100:begin
        if (red_op_A_reg || red_op_B_reg)begin
           alsu_IF.out_G =0;
           alsu_IF.leds_G=~alsu_IF.leds_G;
        end
         else if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
         end
         else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
         end
         else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
         end   
        else begin
            if (direction_reg) begin
                alsu_IF.out_G<={alsu_IF.out_G[4:0],serial_in_reg};
            end
            else
                alsu_IF.out_G<={serial_in_reg,alsu_IF.out_G[5:1]};
        end        
     end
     3'b101:begin
        if (red_op_A_reg || red_op_B_reg)begin
           alsu_IF.out_G =0;
           alsu_IF.leds_G=~alsu_IF.leds_G;
        end
         else if (bypass_A_reg && bypass_B_reg ) begin
            if (INPUT_PRIORITY=="A") alsu_IF.out_G<=A_reg; else alsu_IF.out_G<=B_reg;
         end
         else if (bypass_A_reg) begin
            alsu_IF.out_G<=A_reg;
         end
         else if (bypass_B_reg) begin
            alsu_IF.out_G<=B_reg;
         end   
        else begin
            if (direction_reg) begin
                alsu_IF.out_G<={alsu_IF.out_G[4:0],alsu_IF.out_G[5]};
            end
            else
                alsu_IF.out_G<={alsu_IF.out_G[0],alsu_IF.out_G[5:1]};
        end   
     end
     3'b110:begin
        alsu_IF.out_G =0;
        alsu_IF.leds_G=~alsu_IF.leds_G;
     end
     3'b111:begin
        alsu_IF.out_G =0;
        alsu_IF.leds_G=~alsu_IF.leds_G;
     end                     
    endcase
  end
end
endmodule