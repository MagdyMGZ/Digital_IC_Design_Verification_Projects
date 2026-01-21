module sa_sva (input logic en_i, ina, inb, clk, out, en_o, logic [2:0] temp_out);

property adder_out;
    @(posedge clk) $rose(en_i) |=> ##3 (out == temp_out[2]) |=> (out == temp_out[1]) |=> (out == temp_out[0]);
endproperty

property adder_en_o;
    @(posedge clk) $rose(en_i) |-> ##3 $rose(en_o);
endproperty

Adder_Out_Assertion : assert property (adder_out);
Adder_Out_Cover     : cover  property (adder_out);

Adder_En_O_Assertion : assert property (adder_en_o);
Adder_En_O_Cover     : cover  property (adder_en_o);

endmodule