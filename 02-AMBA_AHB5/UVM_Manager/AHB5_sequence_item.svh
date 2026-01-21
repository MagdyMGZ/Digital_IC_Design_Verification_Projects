class AHB5_sequence_item extends uvm_sequence_item;

`uvm_object_utils(AHB5_sequence_item)

rand    bit                                HRESETn;
rand    bit                                HSELx;
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

int wrap_size, min_boundary, max_boundary;
rand bit [ADDR_WIDTH-1:0] HADDR_ns;
     bit [ADDR_WIDTH-1:0] HADDR_cs;
     bit [ADDR_WIDTH-1:0] HADDR_reg;

rand type_e HWRITE_ns;
     type_e HWRITE_cs;

constraint HRESETn_c {HRESETn dist {0 :/ 2 , 1 :/ 98 };}

constraint HSELx_c {HSELx dist {0 := 2 , 1 := 98};}

constraint HREADY_c {HREADY dist {0 := 2 , 1 := 98};}

constraint HWDATA_c {HWDATA dist {0 :/ 10 , {DATA_WIDTH{1'b1}} :/ 10 , [32'h00000000:32'hFFFFFFFE] :/ 80};}

constraint HWRITE_c {
    HWRITE_ns dist {WRITE :/ 60 , READ :/ 40};
    HWRITE == HWRITE_cs;
}

constraint HBURST_c {
    HBURST_ns dist {SINGLE := 15, INCR := 15, WRAP4 := 15, INCR4 := 15, WRAP8 := 15, INCR8 := 15, WRAP16 := 15, INCR16 := 15};
    HBURST == HBURST_cs;
}

constraint HSIZE_c {
    if (HADDR[1:0] == 2'b00)
        HSIZE dist {BYTE := 25, HALFWORD := 25, WORD := 25};
    else if (HADDR[1:0] == 2'b01)
        HSIZE == BYTE;
    else if (HADDR[1:0] == 2'b10)
        HSIZE dist {BYTE :/ 50, HALFWORD :/ 50};
    else if (HADDR[1:0] == 2'b11)
        HSIZE == BYTE;
}

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
    if (HRESETn && HREADY && HSELx) begin
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
            HWRITE_cs = HWRITE_ns;
            ////////////////////////////////
            case (HBURST_cs)
                WRAP4  : wrap_size = 4  << HSIZE;
                WRAP8  : wrap_size = 8  << HSIZE;
                WRAP16 : wrap_size = 16 << HSIZE;
            endcase
            min_boundary = HADDR_cs & ~(wrap_size - 1);
            max_boundary = min_boundary + wrap_size;
        end
        ////////////////////////////////////
        HADDR_reg = HADDR;
    end
    else begin
        hburst_cntr = 0;
        HADDR_reg = 0;
    end
endfunction

function new (string name = "AHB5_sequence_item");
    super.new(name);
endfunction

function string convert2string ();
    return $sformatf ("%s HRESETn = %0d, HSELx = %0d, HREADY = %0d, HADDR = %0d, HBURST = %0s, HSIZE = %0s, HTRANS = %0s, HWRITE = %0s, HWDATA = %0d, HWSTRB = %0b, HRDATA = %0d, HREADYOUT = %0d, HRESP = %0d", super.convert2string(),HRESETn,HSELx,HREADY,HADDR,HBURST,HSIZE,HTRANS,HWRITE,HWDATA,HWSTRB,HRDATA,HREADYOUT,HRESP);
endfunction

function string convert2string_stimulus ();
    return $sformatf ("HRESETn = %0d, HSELx = %0d, HREADY = %0d, HADDR = %0d, HBURST = %0s, HSIZE = %0s, HTRANS = %0s, HWRITE = %0s, HWDATA = %0d, HWSTRB = %0b",HRESETn,HSELx,HREADY,HADDR,HBURST,HSIZE,HTRANS,HWRITE,HWDATA,HWSTRB);
endfunction

endclass
