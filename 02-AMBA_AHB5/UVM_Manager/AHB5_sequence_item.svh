class AHB5_sequence_item extends uvm_sequence_item;

`uvm_object_utils(AHB5_sequence_item)

rand    bit                                HRESETn;
rand    bit                                HSEL1;
rand    bit                                HREADY;
rand    type_e                             HWRITE;
rand    hsize_e                            HSIZE;
rand    bit        [DATA_WIDTH-1:0]        HWDATA;
rand    bit        [STRB_WIDTH-1:0]        HWSTRB;
rand    hburst_e                           HBURST;
rand    htrans_e                           HTRANS;
rand    bit        [ADDR_WIDTH-1:0]        HADDR;
        bit        [DATA_WIDTH-1:0]        HRDATA;
        bit                                HREADYOUT;
        bit                                HRESP;

int hburst_cntr;
rand hburst_e HBURST_ns;
     hburst_e HBURST_cs;

int min_boundary, max_boundary;
rand bit [ADDR_WIDTH-1:0] HADDR_ns;
     bit [ADDR_WIDTH-1:0] HADDR_cs;
     bit [ADDR_WIDTH-1:0] HADDR_reg;

constraint HRESETn_c {HRESETn dist {0 :/ 2 , 1 :/ 98 };}

constraint HSEL1_c {HSEL1 dist {0 :/ 5 , 1 :/ 95};}

constraint HREADY_c {HREADY dist {0 :/ 5 , 1 :/ 95};}

constraint HWRITE_c {HWRITE dist {WRITE :/ 60 , READ :/ 40};}

constraint HSIZE_c {HSIZE dist {BYTE :/ 25, HALFWORD :/ 25, WORD :/ 50};} // Randomized along all burst for undefined length

constraint HWDATA_c {HWDATA dist {0 :/ 10 , {DATA_WIDTH{1'b1}} :/ 10 , [32'h00000000:32'hFFFFFFFE] :/ 80};}

constraint HWSTRB_c {
    if (HWRITE == READ)
        HWSTRB == 0;
    else if (HWRITE == WRITE) {
        if ($onehot(HWSTRB))
            HWSTRB dist {HWSTRB :/ 40};
        else
            HWSTRB dist {0 :/ 30 , {STRB_WIDTH{1'b1}} :/ 30};
    }
}

constraint HBURST_c {
    HBURST_ns dist {SINGLE := 15, INCR := 15, WRAP4 := 15, INCR4 := 15, WRAP8 := 15, INCR8 := 15, WRAP16 := 15, INCR16 := 15};

    HBURST == HBURST_cs;
}

constraint HTRANS_c {
    if (!HRESETn || HRESP)
        HTRANS == IDLE;
    else if (!HREADY)
        HTRANS == BUSY;
    else if (hburst_cntr == 0)
        HTRANS == NONSEQ;
    else
        HTRANS == SEQ;
}

constraint HADDR_c {
    HADDR_ns[ADDR_WIDTH-1 -: (ADDR_WIDTH - OFFSET)] == 0;

    if (hburst_cntr == 0) 
        HADDR == HADDR_cs;
    else {
        if (HBURST_cs inside {WRAP4, WRAP8, WRAP16}) {
            if ((HADDR_reg + (2**HSIZE)) >= max_boundary)
                HADDR == min_boundary;
            else
                HADDR == HADDR_reg + (2**HSIZE);
        }
        else
            HADDR == HADDR_reg + (2**HSIZE);
    }

}

function void post_randomize ();
    if (HRESETn && HREADY && HSEL1) begin
        if (HBURST_cs == SINGLE)
            hburst_cntr = 0;
        else if ((HBURST_cs == INCR) && (hburst_cntr < 2))
            hburst_cntr += 1;
        else if (((HBURST_cs == WRAP4) || (HBURST_cs == INCR4)) && (hburst_cntr < 4))
            hburst_cntr += 1;
        else if (((HBURST_cs == WRAP8) || (HBURST_cs == INCR8)) && (hburst_cntr < 8))
            hburst_cntr += 1;
        else if (((HBURST_cs == WRAP16) || (HBURST_cs == INCR16)) && (hburst_cntr < 16))
            hburst_cntr += 1;
        else
            hburst_cntr = 0;
        ////////////////////////////////////
        if (hburst_cntr == 0) begin
            HBURST_cs = HBURST_ns;
            HADDR_cs = HADDR_ns;
        end
        ////////////////////////////////////
        HADDR_reg = HADDR;
    end
    else begin
        hburst_cntr = 0;
        HADDR_reg = 0;
    end
endfunction

function void pre_randomize ();
    if (HBURST_cs == WRAP4) begin
        min_boundary = int'((HADDR_cs) / (4 * (2**HSIZE))) * (4 * (2**HSIZE));
        max_boundary = min_boundary + (4 * (2**HSIZE));
    end
    else if (HBURST_cs == WRAP8) begin
        min_boundary = int'((HADDR_cs) / (8 * (2**HSIZE))) * (8 * (2**HSIZE));
        max_boundary = min_boundary + (8 * (2**HSIZE));
    end 
    else if (HBURST_cs == WRAP16) begin
        min_boundary = int'((HADDR_cs) / (16 * (2**HSIZE))) * (16 * (2**HSIZE));
        max_boundary = min_boundary + (16 * (2**HSIZE));
    end
    // Variables Printing for Debugging 
    // $display("HADDR_cs = %2d, hburst_cntr = %2d,\t HADDR = %2d,\t HSIZE = %8s,\t HTRANS = %6s,\t HBURST = %6s",HADDR_cs,hburst_cntr,HADDR,HSIZE,HTRANS,HBURST);
endfunction

function new (string name = "AHB5_sequence_item");
    super.new(name);
endfunction

function string convert2string ();
    return $sformatf ("%s HRESETn = %0d, HSEL1 = %0d, HREADY = %0d, HADDR = %0d, HBURST = %0s, HSIZE = %0s, HTRANS = %0s, HWRITE = %0s, HWDATA = %0d, HWSTRB = %0b, HRDATA = %0d, HREADYOUT = %0d, HRESP = %0d", super.convert2string(),HRESETn,HSEL1,HREADY,HADDR,HBURST,HSIZE,HTRANS,HWRITE,HWDATA,HWSTRB,HRDATA,HREADYOUT,HRESP);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("HRESETn = %0d, HSEL1 = %0d, HREADY = %0d, HADDR = %0d, HBURST = %0s, HSIZE = %0s, HTRANS = %0s, HWRITE = %0s, HWDATA = %0d, HWSTRB = %0b",HRESETn,HSEL1,HREADY,HADDR,HBURST,HSIZE,HTRANS,HWRITE,HWDATA,HWSTRB);
endfunction

endclass
