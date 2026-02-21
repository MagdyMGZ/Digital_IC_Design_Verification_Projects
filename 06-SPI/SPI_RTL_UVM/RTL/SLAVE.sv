module SLAVE (MOSI,MISO,SS_n,clk,rst_n,rx_data,rx_valid,tx_data,tx_valid);

localparam IDLE      = 3'b000;
localparam WRITE     = 3'b001;
localparam CHK_CMD   = 3'b010;
localparam READ_ADD  = 3'b011;
localparam READ_DATA = 3'b100;

input            MOSI, clk, rst_n, SS_n, tx_valid;
input      [7:0] tx_data;
output reg [9:0] rx_data;
output reg       rx_valid, MISO;

reg [3:0] counter;
reg       received_address;

reg [2:0] cs, ns;

always @(posedge clk) begin
    if (~rst_n) begin
        cs <= IDLE;
    end
    else begin
        cs <= ns;
    end
end

always @(*) begin
    case (cs)
        IDLE : begin
            if (SS_n)
                ns = IDLE;
            else
                ns = CHK_CMD;
        end
        CHK_CMD : begin
            if (SS_n)
                ns = IDLE;
            else begin
                if (~MOSI)
                    ns = WRITE;
                else begin
                    if (received_address)
                        ns = READ_DATA;
                    else
                        ns = READ_ADD;
                end
            end
        end
        WRITE : begin
            if (SS_n)
                ns = IDLE;
            else
                ns = WRITE;
        end
        READ_ADD : begin
            if (SS_n)
                ns = IDLE;
            else
                ns = READ_ADD;
        end
        READ_DATA : begin
            if (SS_n)
                ns = IDLE;
            else
                ns = READ_DATA;
        end
    endcase
end

always @(posedge clk) begin
    if (~rst_n) begin
        rx_data <= 0;
        rx_valid <= 0;
        received_address <= 0;
        MISO <= 0;
        counter <= 0;
    end
    else begin
        case (cs)
            IDLE : begin
                rx_valid <= 0;
            end
            CHK_CMD : begin
                counter <= 10;
            end
            WRITE : begin
                if (counter > 0) begin
                    rx_data[counter-1] <= MOSI;
                    counter <= counter - 1;
                end
                else begin
                    rx_valid <= 1;
                end
            end
            READ_ADD : begin
                if (counter > 0) begin
                    rx_data[counter-1] <= MOSI;
                    counter <= counter - 1;
                end
                else begin
                    rx_valid <= 1;
                    received_address <= 1;
                end
            end
            READ_DATA : begin
                if (tx_valid) begin
                    rx_valid <= 0;
                    if (counter > 0) begin
                        MISO <= tx_data[counter-1];
                        counter <= counter - 1;
                    end
                    else begin
                        received_address <= 0;
                    end
                end
                else begin
                    if (counter > 0) begin
                        rx_data[counter-1] <= MOSI;
                        counter <= counter - 1;
                    end
                    else begin
                        rx_valid <= 1;
                        counter <= 9;
                    end
                end
            end
        endcase
    end
end

// 3- Add the following assertions in the design to check correct FSM transitions
// • IDLE → CHK_CMD
// • CHK_CMD → WRITE or READ_ADD or READ_DATA
// • WRITE → IDLE 
// • READ_ADD → IDLE 
// • READ_DATA → IDLE

`ifdef SIM
    property FSM_Trans1;
        @(posedge clk) disable iff(!rst_n) (cs == IDLE && !SS_n) |=> (cs == CHK_CMD);
    endproperty

    property FSM_Trans2;
        @(posedge clk) disable iff(!rst_n) (cs == CHK_CMD && !SS_n && !MOSI) |=> (cs == WRITE);
    endproperty

    property FSM_Trans3;
        @(posedge clk) disable iff(!rst_n) (cs == CHK_CMD && !SS_n && MOSI && !received_address) |=> (cs == READ_ADD);
    endproperty

    property FSM_Trans4;
        @(posedge clk) disable iff(!rst_n) (cs == CHK_CMD && !SS_n && MOSI && received_address) |=> (cs == READ_DATA);
    endproperty

    property FSM_Trans5;
        @(posedge clk) disable iff(!rst_n) (cs == WRITE && SS_n) |=> (cs == IDLE);
    endproperty

    property FSM_Trans6;
        @(posedge clk) disable iff(!rst_n) (cs == READ_ADD && SS_n) |=> (cs == IDLE);
    endproperty

    property FSM_Trans7;
        @(posedge clk) disable iff(!rst_n) (cs == READ_DATA && SS_n) |=> (cs == IDLE);
    endproperty

    FSM_Trans_asser1: assert property (FSM_Trans1);
    FSM_Trans_asser2: assert property (FSM_Trans2);
    FSM_Trans_asser3: assert property (FSM_Trans3);
    FSM_Trans_asser4: assert property (FSM_Trans4);
    FSM_Trans_asser5: assert property (FSM_Trans5);
    FSM_Trans_asser6: assert property (FSM_Trans6);
    FSM_Trans_asser7: assert property (FSM_Trans7);

    FSM_Trans_cover1: cover property (FSM_Trans1);
    FSM_Trans_cover2: cover property (FSM_Trans2);
    FSM_Trans_cover3: cover property (FSM_Trans3);
    FSM_Trans_cover4: cover property (FSM_Trans4);
    FSM_Trans_cover5: cover property (FSM_Trans5);
    FSM_Trans_cover6: cover property (FSM_Trans6);
    FSM_Trans_cover7: cover property (FSM_Trans7);

`endif 


endmodule 