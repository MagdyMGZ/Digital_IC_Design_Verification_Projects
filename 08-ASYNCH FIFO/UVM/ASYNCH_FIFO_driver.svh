class ASYNCH_FIFO_driver extends uvm_driver #(ASYNCH_FIFO_sequence_item);

`uvm_component_utils(ASYNCH_FIFO_driver)

virtual ASYNCH_FIFO_if ASYNCH_FIFO_vif;
ASYNCH_FIFO_sequence_item ASYNCH_FIFO_seq_item;

function new (string name = "ASYNCH_FIFO_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    forever begin
        ASYNCH_FIFO_seq_item = ASYNCH_FIFO_sequence_item::type_id::create("ASYNCH_FIFO_seq_item");
        seq_item_port.get_next_item(ASYNCH_FIFO_seq_item);

        case ({ASYNCH_FIFO_seq_item.i_ren , ASYNCH_FIFO_seq_item.i_wen})
            2'b01 : begin
                @(posedge ASYNCH_FIFO_vif.i_wclk);
                ASYNCH_FIFO_vif.cb_driver_wr.i_rst_n <= ASYNCH_FIFO_seq_item.i_rst_n;
                ASYNCH_FIFO_vif.cb_driver_wr.i_wen <= ASYNCH_FIFO_seq_item.i_wen;
                ASYNCH_FIFO_vif.cb_driver_wr.i_ren <= ASYNCH_FIFO_seq_item.i_ren;
                ASYNCH_FIFO_vif.cb_driver_wr.i_wdata <= ASYNCH_FIFO_seq_item.i_wdata;
            end
            2'b10 : begin
                @(posedge ASYNCH_FIFO_vif.i_rclk);
                ASYNCH_FIFO_vif.cb_driver_rd.i_rst_n <= ASYNCH_FIFO_seq_item.i_rst_n;
                ASYNCH_FIFO_vif.cb_driver_rd.i_wen <= ASYNCH_FIFO_seq_item.i_wen;
                ASYNCH_FIFO_vif.cb_driver_rd.i_ren <= ASYNCH_FIFO_seq_item.i_ren;
                ASYNCH_FIFO_vif.cb_driver_rd.i_wdata <= ASYNCH_FIFO_seq_item.i_wdata;
            end
            default : begin
                @(posedge ASYNCH_FIFO_vif.i_wclk);
                @(posedge ASYNCH_FIFO_vif.i_rclk);
                ASYNCH_FIFO_vif.cb_driver_rd.i_rst_n <= ASYNCH_FIFO_seq_item.i_rst_n;
                ASYNCH_FIFO_vif.cb_driver_rd.i_wen <= ASYNCH_FIFO_seq_item.i_wen;
                ASYNCH_FIFO_vif.cb_driver_rd.i_ren <= ASYNCH_FIFO_seq_item.i_ren;
                ASYNCH_FIFO_vif.cb_driver_rd.i_wdata <= ASYNCH_FIFO_seq_item.i_wdata;
            end
        endcase

        seq_item_port.item_done();
        `uvm_info("run_phase",ASYNCH_FIFO_seq_item.convert2string_stimulus(),UVM_FULL)
    end
endtask

endclass