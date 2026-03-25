class AHB5_sequence_item extends uvm_sequence_item;          // Acting Like Bus Matrix

`uvm_object_utils(AHB5_sequence_item)

rand    bit                                 rst_n;           // HRESETn
rand    bit                                 slv_sel;         // HSELx
rand    bit                                 slv_enable;      // HREADY
rand    hburst_e                            burst;           // HBURST
rand    bit         [DATA_WIDTH-1:0]        wdata_arr[];     // HWDATA along the burst
rand    type_e                              write;           // HWRITE
rand    bit         [ADDR_WIDTH-1:0]        address;         // HADDR
rand    hsize_e                             size;            // HSIZE
rand    bit         [STRB_WIDTH-1:0]        strb;            // HWSTRB

        // AHB5 Output to Bus Matrix
        bit         [DATA_WIDTH-1:0]        rdata;           // HRDATA
        bit                                 valid;           // HREADYOUT
        bit                                 trans_error;     // HRESP

        // Response For Reactive Agent
        bit                                 trans_done;

constraint rst_n_c {rst_n dist {0 := 1 , 1 := 99};}

constraint slv_sel_c {slv_sel dist {0 := 2 , 1 := 98};}

constraint slv_enable_c {slv_enable dist {0 := 2 , 1 := 98};}

constraint burst_c {burst dist {SINGLE := 15, INCR := 15, WRAP4 := 15, INCR4 := 15, WRAP8 := 15, INCR8 := 15, WRAP16 := 15, INCR16 := 15};}

constraint wdata_arr_c {
    if (burst == SINGLE)
        wdata_arr.size() == 1;
    else if (burst == INCR)
        wdata_arr.size() == 2;
    else if (burst inside {WRAP4,INCR4})
        wdata_arr.size() == 4;
    else if (burst inside {WRAP8,INCR8})
        wdata_arr.size() == 8;
    else if (burst inside {WRAP16,INCR16})
        wdata_arr.size() == 16;
    ////////////////////////////////////
    foreach(wdata_arr[i])
        wdata_arr[i] dist {0 :/ 10 , {DATA_WIDTH{1'b1}} :/ 10 , [32'h00000000:32'hFFFFFFFE] :/ 80};
}

constraint write_c {write dist {WRITE :/ 60 , READ :/ 40};}

constraint address_c {
    address[ADDR_WIDTH-1 -: (ADDR_WIDTH - OFFSET)] == 0;
}

constraint size_c {
    if (address[1:0] == 2'b00)
        size dist {BYTE := 25, HALFWORD := 25, WORD := 25};
    else if (address[1:0] == 2'b01)
        size == BYTE;
    else if (address[1:0] == 2'b10)
        size dist {BYTE :/ 50, HALFWORD :/ 50};
    else if (address[1:0] == 2'b11)
        size == BYTE;
}

constraint HWSTRB_c {
    if (write == READ)
        strb == 0;
    else if (write == WRITE) {
        if ($onehot(strb))
            strb dist {strb :/ 40};
        else
            strb dist {0 :/ 30 , {STRB_WIDTH{1'b1}} :/ 30};
    }
}

function new (string name = "AHB5_sequence_item");
    super.new(name);
endfunction

function string convert2string ();
    return $sformatf ("%s rst_n = %0d, slv_sel = %0d, slv_enable = %0d, burst = %0s, address = %0d, write = %0s, wdata_arr = %0p, rdata = %0d, valid = %0d, trans_error = %0d, strb = %0b", super.convert2string(),rst_n,slv_sel,slv_enable,burst,address,write,wdata_arr,rdata,valid,trans_error,strb);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("rst_n = %0d, slv_sel = %0d, slv_enable = %0d, burst = %0s, address = %0d, write = %0s, wdata_arr = %0p, strb = %0b",rst_n,slv_sel,slv_enable,burst,address,write,wdata_arr,strb);
endfunction

endclass
