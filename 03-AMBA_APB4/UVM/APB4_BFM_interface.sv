`timescale 1ns/1ps
interface APB4_BFM_if ();
    parameter  DATA_WIDTH = 32;
    parameter  ADDR_WIDTH = 32;
    parameter  MEM_DEPTH  = 64;
    localparam STRB_WIDTH = DATA_WIDTH/8;

    logic                                PCLK;
    logic                                PRESETn;
    logic                                TRANSFER;
    logic                                WRITE;
    logic        [ADDR_WIDTH-1:0]        ADDR;
    logic        [DATA_WIDTH-1:0]        WDATA;
    logic        [STRB_WIDTH-1:0]        STRB;
    logic                                READY;
    logic        [DATA_WIDTH-1:0]        RDATA;
    logic                                SLVERR;

    initial begin
        PCLK = 0;
        forever begin
            #5 PCLK = ~PCLK;
        end
    end

    task reset ();
        @(posedge PCLK);                // OR // @(cb_driver);
        cb_driver.PRESETn <= 0;
        cb_driver.TRANSFER <= 0;
        cb_driver.WRITE <= 0;
        cb_driver.ADDR <= 0;
        cb_driver.WDATA <= 0;
        cb_driver.STRB <= 0;
    endtask

    task write (
        input   logic                       resetn,
        input   logic                       transfer,
        input   logic   [ADDR_WIDTH-1:0]    addr,
        input   logic   [DATA_WIDTH-1:0]    wdata,
        input   logic   [STRB_WIDTH-1:0]    strb
    );
        @(posedge PCLK);                // OR // @(cb_driver);
        cb_driver.PRESETn <= resetn;
        cb_driver.TRANSFER <= transfer;
        cb_driver.WRITE <= 1;
        cb_driver.ADDR <= addr;
        cb_driver.WDATA <= wdata;
        cb_driver.STRB <= strb;
    endtask

    task read (
        input   logic                       resetn,
        input   logic                       transfer,
        input   logic   [ADDR_WIDTH-1:0]    addr,
        input   logic   [STRB_WIDTH-1:0]    strb
    );
        @(posedge PCLK);                // OR // @(cb_driver);
        cb_driver.PRESETn <= resetn;
        cb_driver.TRANSFER <= transfer;
        cb_driver.WRITE <= 0;
        cb_driver.ADDR <= addr;
        cb_driver.WDATA <= 0;
        cb_driver.STRB <= strb;
    endtask

    clocking cb_driver @(posedge PCLK);
        default output #1step;
        output PRESETn, TRANSFER, WRITE, ADDR, WDATA, STRB; 
    endclocking

    clocking cb_monitor @(posedge PCLK);
        default input #0;
        input PRESETn, TRANSFER, WRITE, ADDR, WDATA, STRB, READY, RDATA, SLVERR;
    endclocking
endinterface