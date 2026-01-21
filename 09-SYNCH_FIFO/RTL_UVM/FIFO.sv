module FIFO # (parameter FIFO_WIDTH = 16 ,
               parameter FIFO_DEPTH = 8)
            (       
                input  logic clk,
                input  logic [FIFO_WIDTH-1:0] data_in,
                input  logic wr_en,
                input  logic rd_en,
                input  logic rst_n,
                output logic [FIFO_WIDTH-1:0] data_out,
                output logic full,
                output logic almostfull,
                output logic empty,
                output logic almostempty,
                output logic overflow,
                output logic underflow,
                output logic wr_ack
            );

// Declaration of max. FIFO address
localparam max_fifo_addr = $clog2(FIFO_DEPTH); // max_fifo_addr = 3

// Declaration of Memory (FIFO)
logic [FIFO_WIDTH-1:0] mem [FIFO_DEPTH-1:0];

// Declaration of read & write pointers
logic [max_fifo_addr-1:0] wr_ptr, rd_ptr; // [2:0] 000 -> 111

logic [max_fifo_addr:0] count; // [3:0]
// Extra logic to Distinguish between full & empty flags & it represents the fill level of the FIFO

// always block specialized for writing operation
always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
                wr_ptr <= 0;
                overflow <= 0;
                wr_ack <= 0;
        end
        else if (wr_en && (count < FIFO_DEPTH)) begin
                mem[wr_ptr] <= data_in;
                wr_ack <= 1;
                wr_ptr <= wr_ptr + 1;
                overflow <= 0;
        end
        else begin 
                wr_ack <= 0; 
                if (full && wr_en)
                        overflow <= 1;
                else
                        overflow <= 0;
        end
end

// always block specialized for reading operation
always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
                rd_ptr <= 0;
                underflow <= 0;
        end
        else if (rd_en && (count != 0)) begin
                data_out <= mem[rd_ptr];
                rd_ptr <= rd_ptr + 1;
                underflow <= 0;
        end
        else begin 
                if (empty && rd_en)
                        underflow <= 1;
                else
                        underflow <= 0;
        end
end

// always block specialized for counter signal
always @(posedge clk or negedge rst_n) begin
        if (!rst_n) 
                count <= 0;
        else begin
                if (({wr_en, rd_en} == 2'b10) && !full) 
                        count <= count + 1;
                else if (({wr_en, rd_en} == 2'b01) && !empty)
                        count <= count - 1;
                else if (({wr_en, rd_en} == 2'b11) && full)      // Priority for Read operation
                        count <= count - 1;
                else if (({wr_en, rd_en} == 2'b11) && empty)     // Priority for Write operation
                        count <= count + 1;
        end
end

// continous assignment for the combinational outputs
assign full = (count == FIFO_DEPTH)? 1 : 0;
assign empty = (count == 0)? 1 : 0;
assign almostfull = (count == FIFO_DEPTH-1)? 1 : 0; 
assign almostempty = (count == 1)? 1 : 0;

endmodule 
