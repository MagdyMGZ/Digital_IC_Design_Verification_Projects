class AHB5_monitor extends uvm_monitor;

`uvm_component_utils(AHB5_monitor)

virtual AHB5_BFM_if AHB5_vif;
AHB5_sequence_item AHB5_seq_item;
uvm_analysis_port #(AHB5_sequence_item) mon_ap;

int write_index;
int burst_length;

function new (string name = "AHB5_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    @(posedge AHB5_vif.HRESETn);
    forever begin
        AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
        burst_length = burst_length_calc(AHB5_seq_item.burst);
        for (int i = 0 ; i < burst_length ; i++) begin
            @(AHB5_vif.cb_monitor);                                 // OR // @(posedge AHB5_vif.PCLK);
            AHB5_seq_item.wdata_arr[i] = AHB5_vif.cb_monitor.HWDATA;
            AHB5_seq_item.rst_n <= AHB5_vif.cb_monitor.HRESETn;
            AHB5_seq_item.slv_sel <= AHB5_vif.cb_monitor.HSELx;
            AHB5_seq_item.slv_enable <= AHB5_vif.cb_monitor.HREADY;
            AHB5_seq_item.burst <= AHB5_vif.cb_monitor.HBURST;
            AHB5_seq_item.write <= AHB5_vif.cb_monitor.HWRITE;
            AHB5_seq_item.address <= AHB5_vif.cb_monitor.HADDR;
            AHB5_seq_item.size <= AHB5_vif.cb_monitor.HSIZE;
            AHB5_seq_item.strb <= AHB5_vif.cb_monitor.HWSTRB;
            AHB5_seq_item.rdata <= AHB5_vif.cb_monitor.HRDATA;
            AHB5_seq_item.valid <= AHB5_vif.cb_monitor.HREADYOUT;
            AHB5_seq_item.trans_error <= AHB5_vif.cb_monitor.HRESP;
            write_index <= i;
            #1step;
            mon_ap.write(AHB5_seq_item);
            `uvm_info("run_phase",AHB5_seq_item.convert2string(),UVM_FULL)
        end
    end
endtask

function int burst_length_calc(input hburst_e burst);
    case(burst)
        SINGLE          : burst_length_calc = 1;
        INCR            : burst_length_calc = 2;
        WRAP4  , INCR4  : burst_length_calc = 4;
        WRAP8  , INCR8  : burst_length_calc = 8;
        WRAP16 , INCR16 : burst_length_calc = 16;
    endcase
endfunction

endclass