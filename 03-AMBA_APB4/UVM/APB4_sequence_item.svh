class APB4_sequence_item extends uvm_sequence_item;

`uvm_object_utils(APB4_sequence_item)

rand    logic                                PRESETn;
rand    logic                                TRANSFER;
rand    logic                                WRITE;
rand    logic        [ADDR_WIDTH-1:0]        ADDR;
rand    logic        [DATA_WIDTH-1:0]        WDATA;
rand    logic        [STRB_WIDTH-1:0]        STRB;
        logic                                READY;
        logic        [DATA_WIDTH-1:0]        RDATA;
        logic                                SLVERR;

rand    type_e                               kind;
rand    slv_sel                              slave;

constraint kind_c {kind dist {write :/ 60 , read :/ 40};}

constraint slv_sel_c {slave dist {regfile_slv0 :/ 50 , memory_slv1 :/ 50};}

constraint preset_n_c {PRESETn dist {0 :/ 2 , 1 :/ 98 };}

constraint TRANSFER_c {TRANSFER dist {1 :/ 60 , 0 :/ 40};}

constraint WRITE_c {WRITE == bit'(kind);}

constraint ADDR_c {
    if (slave == regfile_slv0) {
        ADDR inside {[32'h00000000 : 32'h0000003C]};
        (ADDR % 4) == 0;
        ADDR[ADDR_WIDTH-1] == 0;
    }   
    else if (slave == memory_slv1) {
        ADDR[ADDR_WIDTH-1] == 1;
    }
}

constraint WDATA_c {WDATA dist {0 :/ 10 , {DATA_WIDTH{1'b1}} :/ 10 , [32'h00000000:32'hFFFFFFFE] :/ 80};}

constraint STRB_c {
    if (kind == read)
        STRB == 0;
    else if (kind == write) {
        if ($onehot(STRB))
            STRB dist {STRB :/ 40};
        else
            STRB dist {0 :/ 30 , {STRB_WIDTH{1'b1}} :/ 30};
    }
}

function new (string name = "APB4_sequence_item");
    super.new(name);    
endfunction

function string convert2string ();
    return $sformatf ("%s PRESETn = %0d, TRANSFER = %0d, WRITE = %0d, ADDR = %0h, WDATA = %0d, STRB = %0b, READY = %0d, RDATA = %0d, SLVERR = %0d, kind = %0s, slave = %0s", super.convert2string(),PRESETn,TRANSFER,WRITE,ADDR,WDATA,STRB,READY,RDATA,SLVERR,kind,slave);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("PRESETn = %0d, TRANSFER = %0d, WRITE = %0d, ADDR = %0h, WDATA = %0d, STRB = %0b",PRESETn,TRANSFER,WRITE,ADDR,WDATA,STRB);
endfunction

endclass
