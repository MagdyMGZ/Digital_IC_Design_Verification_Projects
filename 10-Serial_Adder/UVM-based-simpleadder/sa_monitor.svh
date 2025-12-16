class sa_monitor extends uvm_monitor;

`uvm_component_utils(sa_monitor)

virtual sa_if sa_vif;
sa_sequence_item sa_seq_item;
uvm_analysis_port #(sa_sequence_item) mon_ap;

function new (string name = "sa_monitor", uvm_component parent = null);
    super.new(name,parent);    
endfunction

function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    mon_ap = new("mon_ap",this);
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        sa_seq_item = sa_sequence_item::type_id::create("sa_seq_item");
        fork
            begin  // Monitor Input
                @(sa_vif.cb_monitor iff (sa_vif.cb_monitor.en_i == 1'b1)); // Not // @(posedge sa_vif.clk iff (sa_vif.cb_monitor.en_i == 1'b1));
                sa_seq_item.a[1] = sa_vif.cb_monitor.ina;
                sa_seq_item.b[1] = sa_vif.cb_monitor.inb;
                @(sa_vif.cb_monitor);					   // Not // @(posedge sa_vif.clk);
                sa_seq_item.a[0] = sa_vif.cb_monitor.ina;
                sa_seq_item.b[0] = sa_vif.cb_monitor.inb;
                @(sa_vif.cb_monitor);					   // Not // @(posedge sa_vif.clk);
            end

            begin  // Monitor Output
                @(sa_vif.cb_monitor iff (sa_vif.cb_monitor.en_o == 1'b1)); // Not // @(posedge sa_vif.clk iff (sa_vif.cb_monitor.en_o == 1'b1));
                sa_seq_item.out[2] = sa_vif.cb_monitor.out;
                @(sa_vif.cb_monitor);					   // Not // @(posedge sa_vif.clk);
                sa_seq_item.out[1] = sa_vif.cb_monitor.out;
                @(sa_vif.cb_monitor);					   // Not // @(posedge sa_vif.clk);
                sa_seq_item.out[0] = sa_vif.cb_monitor.out;
            end
        join
        mon_ap.write(sa_seq_item);
        `uvm_info("run_phase",sa_seq_item.convert2string(),UVM_FULL)
    end
endtask

endclass