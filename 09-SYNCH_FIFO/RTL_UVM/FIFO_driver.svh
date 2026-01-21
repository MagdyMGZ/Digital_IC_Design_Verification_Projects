class FIFO_driver extends uvm_driver #(FIFO_sequence_item);

`uvm_component_utils(FIFO_driver)

virtual FIFO_if FIFO_vif;
FIFO_sequence_item FIFO_seq_item;

function new (string name = "FIFO_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        FIFO_seq_item = FIFO_sequence_item::type_id::create("FIFO_seq_item");
        seq_item_port.get_next_item(FIFO_seq_item);
        @(posedge FIFO_vif.clk); // OR // @(FIFO_vif.cb_driver);
        FIFO_vif.cb_driver.data_in <= FIFO_seq_item.data_in;
        FIFO_vif.cb_driver.wr_en   <= FIFO_seq_item.wr_en;
        FIFO_vif.cb_driver.rd_en   <= FIFO_seq_item.rd_en;
        FIFO_vif.cb_driver.rst_n   <= FIFO_seq_item.rst_n;
        seq_item_port.item_done();
        `uvm_info("run_phase",FIFO_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

endclass