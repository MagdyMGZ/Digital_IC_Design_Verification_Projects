class sa_driver extends uvm_driver #(sa_sequence_item);

`uvm_component_utils(sa_driver)

virtual sa_if sa_vif;
sa_sequence_item sa_seq_item;

function new (string name = "sa_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        sa_seq_item = sa_sequence_item::type_id::create("sa_seq_item");
        seq_item_port.get_next_item(sa_seq_item);
        @(posedge sa_vif.clk);				// OR // @(sa_vif.cb_driver);
        sa_vif.cb_driver.en_i <= 1'b1;
        sa_vif.cb_driver.ina <= sa_seq_item.a[1];
        sa_vif.cb_driver.inb <= sa_seq_item.b[1];
        @(posedge sa_vif.clk);				// OR // @(sa_vif.cb_driver);
        sa_vif.cb_driver.ina <= sa_seq_item.a[0];
        sa_vif.cb_driver.inb <= sa_seq_item.b[0];
        @(posedge sa_vif.clk);				// OR // @(sa_vif.cb_driver);
        sa_vif.cb_driver.en_i <= 1'b0;
        wait(sa_vif.cb_monitor.en_o == 1'b1);
        repeat(3) @(posedge sa_vif.clk);		// OR // @(sa_vif.cb_driver);
        seq_item_port.item_done();
        `uvm_info("run_phase",sa_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

endclass