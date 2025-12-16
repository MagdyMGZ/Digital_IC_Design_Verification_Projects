interface shift_reg_if ();

  logic serial_in, direction, mode;
  logic signed [5:0] datain, dataout;

  modport DUT (
  input serial_in,direction,mode,datain,
  output dataout
  );

endinterface