module shift_reg (shift_reg_if.DUT shift_reg_IF);

always @(*) begin
      if (shift_reg_IF.mode) // rotate
         if (shift_reg_IF.direction) // left
            shift_reg_IF.dataout <= {shift_reg_IF.datain[4:0], shift_reg_IF.datain[5]};
         else
            shift_reg_IF.dataout <= {shift_reg_IF.datain[0], shift_reg_IF.datain[5:1]};
      else // shift
         if (shift_reg_IF.direction) // left
            shift_reg_IF.dataout <= {shift_reg_IF.datain[4:0], shift_reg_IF.serial_in};
         else
            shift_reg_IF.dataout <= {shift_reg_IF.serial_in, shift_reg_IF.datain[5:1]};
end

endmodule