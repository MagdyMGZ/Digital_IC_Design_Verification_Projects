module RAM_SVA (din,clk,rst_n,rx_valid,dout,tx_valid);

input logic [9:0] din;
input logic       clk, rst_n, rx_valid;
input logic [7:0] dout;
input logic       tx_valid;

sequence write_add_seq;
    ((din[9:8] == 2'b00) && rx_valid);
endsequence

sequence write_data_seq;
    ((din[9:8] == 2'b01) && rx_valid);
endsequence

sequence read_add_seq;
    ((din[9:8] == 2'b10) && rx_valid);
endsequence

sequence read_data_seq;
    ((din[9:8] == 2'b11) && rx_valid);
endsequence

// 1- An assertion ensures that whenever reset is asserted, the output signals (tx_valid and dout) are low
property rstn_property;
    @(posedge clk) !rst_n |=> (!tx_valid && ~dout);
endproperty

// 2- An assertion checks that during address or data input phases (write_add_seq, write_data_seq, read_add_seq), 
//    the tx_valid signal must remain deasserted.
property not_tx_valid_property;
    @(posedge clk) disable iff(!rst_n) (write_add_seq or write_data_seq or read_add_seq) |=> !tx_valid;
endproperty

// 3- An assertion checks that after a read_data_seq occurs, the tx_valid signal must rise to indicate valid output 
//    and after it rises by one clock cycle, it should eventually fall.
property tx_valid_fall_after_rise;
    @(posedge clk) disable iff(!rst_n) (read_data_seq) |=> $rose(tx_valid) |=> ($fell(tx_valid) [->1]);
endproperty

// 4- An assertion checks that every Write Address operation must be eventually followed by a Write Data operation.
property write_sequence;
    @(posedge clk) disable iff(!rst_n) write_add_seq |=> ((din[9:8] == 2'b01) && rx_valid) [->1];
endproperty

// 5- An assertion checks that every Read Address operation must be eventually followed by a Read Data operation.
property read_sequence;
    @(posedge clk) disable iff(!rst_n) read_add_seq |=> ((din[9:8] == 2'b11) && rx_valid) [->1];
endproperty

rstn_assertion: assert property (rstn_property);
rstn_cover:     cover  property (rstn_property);

not_tx_valid_assertion: assert property (not_tx_valid_property);
not_tx_valid_cover:     cover  property (not_tx_valid_property);

tx_valid_fall_after_rise_assertion: assert property (tx_valid_fall_after_rise);
tx_valid_fall_after_rise_cover:     cover  property (tx_valid_fall_after_rise);

write_seq_assertion: assert property (write_sequence);
write_seq_cover:     cover  property (write_sequence);

read_seq_assertion: assert property (read_sequence);
read_seq_cover:     cover  property (read_sequence);

endmodule

