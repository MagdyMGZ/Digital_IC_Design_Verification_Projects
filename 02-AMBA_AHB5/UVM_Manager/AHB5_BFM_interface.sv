`timescale 1ns/1ps
import shared_pkg::*;
interface AHB5_BFM_if ();
    hburst_e                             HBURST;
    hsize_e                              HSIZE;
    htrans_e                             HTRANS;
    type_e                               HWRITE;

    logic                                HCLK;
    logic                                HRESETn;
    logic                                HSEL1;
    logic                                HREADY;
    logic        [ADDR_WIDTH-1:0]        HADDR;
    logic        [DATA_WIDTH-1:0]        HWDATA;
    logic        [STRB_WIDTH-1:0]        HWSTRB;
    logic        [DATA_WIDTH-1:0]        HRDATA;
    logic                                HREADYOUT;
    logic                                HRESP;
    
    initial begin
        HCLK = 0;
        forever begin
            #5 HCLK = ~HCLK;
        end
    end

    task reset ();
        @(posedge HCLK);                // OR // @(cb_driver);
        cb_driver.HRESETn <= 0;
        cb_driver.HSEL1 <= 0;
        cb_driver.HREADY <= 0;
        cb_driver.HADDR <= 0;
        cb_driver.HBURST <= hburst_e'(0);
        cb_driver.HSIZE <= hsize_e'(0);
        cb_driver.HTRANS <= htrans_e'(0);
        cb_driver.HWDATA <= 0;
        cb_driver.HWSTRB <= 0;
        cb_driver.HWRITE <= type_e'(0);
    endtask

    task write (
        input   logic                       resetn,
        input   logic                       slv_sel,
        input   logic                       slv_ready,
        input   logic   [ADDR_WIDTH-1:0]    addr,
        input   hburst_e                    burst,
        input   hsize_e                     size,
        input   htrans_e                    transfer,
        input   logic   [DATA_WIDTH-1:0]    wdata,
        input   logic   [STRB_WIDTH-1:0]    strb
    );
        @(posedge HCLK);                // OR // @(cb_driver);
        cb_driver.HRESETn <= resetn;
        cb_driver.HSEL1 <= slv_sel;
        cb_driver.HREADY <= slv_ready;
        cb_driver.HADDR <= addr;
        cb_driver.HBURST <= burst;
        cb_driver.HSIZE <= size;
        cb_driver.HTRANS <= transfer;
        cb_driver.HWDATA <= wdata;
        cb_driver.HWSTRB <= strb;
        cb_driver.HWRITE <= type_e'(1);
    endtask

    task read (
        input   logic                       resetn,
        input   logic                       slv_sel,
        input   logic                       slv_ready,
        input   logic   [ADDR_WIDTH-1:0]    addr,
        input   hburst_e                    burst,
        input   hsize_e                     size,
        input   htrans_e                    transfer,
        input   logic   [STRB_WIDTH-1:0]    strb
    );
        @(posedge HCLK);                // OR // @(cb_driver);
        cb_driver.HRESETn <= resetn;
        cb_driver.HSEL1 <= slv_sel;
        cb_driver.HREADY <= slv_ready;
        cb_driver.HADDR <= addr;
        cb_driver.HBURST <= burst;
        cb_driver.HSIZE <= size;
        cb_driver.HTRANS <= transfer;
        cb_driver.HWDATA <= 0;
        cb_driver.HWSTRB <= strb;
        cb_driver.HWRITE <= type_e'(0);
    endtask

    clocking cb_driver @(posedge HCLK);
        default output #1step;
        output HRESETn, HSEL1, HREADY, HADDR, HBURST, HSIZE, HTRANS, HWDATA, HWSTRB, HWRITE;
    endclocking

    clocking cb_monitor @(posedge HCLK);
        default input #0;
        input HRESETn, HSEL1, HREADY, HADDR, HBURST, HSIZE, HTRANS, HWDATA, HWSTRB, HWRITE, HRDATA, HREADYOUT, HRESP;
    endclocking
endinterface