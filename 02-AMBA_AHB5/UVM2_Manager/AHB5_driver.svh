class AHB5_driver extends uvm_driver #(AHB5_sequence_item);

`uvm_component_utils(AHB5_driver)

virtual AHB5_BFM_if AHB5_vif;
AHB5_sequence_item AHB5_seq_item;

int wrap_size, min_boundary, max_boundary;

function new (string name = "AHB5_driver", uvm_component parent = null);
    super.new(name,parent);    
endfunction

task run_phase (uvm_phase phase);
    super.run_phase(phase);
    
    `uvm_info(get_type_name(),"Reset Asserted",UVM_LOW)
    AHB5_vif.reset();
    `uvm_info(get_type_name(),"Reset Deasserted",UVM_LOW)

    forever begin
        AHB5_seq_item = AHB5_sequence_item::type_id::create("AHB5_seq_item");
        seq_item_port.get_next_item(AHB5_seq_item);
        AHB5_seq_item.trans_done = 0;
        drive(AHB5_seq_item);
        AHB5_seq_item.trans_done = 1;
        seq_item_port.item_done(AHB5_seq_item);
        `uvm_info("run_phase",AHB5_seq_item.convert2string_stimulus(),UVM_HIGH)
    end
endtask

virtual task drive (input AHB5_sequence_item AHB5_seq_item);
    int burst_length = burst_length_calc(AHB5_seq_item.burst);
    int address_reg  = AHB5_seq_item.address;
    boundaries(AHB5_seq_item.burst,address_reg,AHB5_seq_item.size); 
    AHB5_vif.addressing(AHB5_seq_item.rst_n,AHB5_seq_item.slv_sel,AHB5_seq_item.slv_enable,AHB5_seq_item.burst,AHB5_seq_item.wdata_arr[0],AHB5_seq_item.write,address_reg,AHB5_seq_item.size,AHB5_seq_item.strb);
    for (int i = 1 ; i < burst_length ; i++) begin
        if (AHB5_seq_item.burst inside {WRAP4, WRAP8, WRAP16}) begin
            if ((address_reg + (2**(AHB5_seq_item.size))) >= max_boundary)
                address_reg = min_boundary;
            else
                address_reg = address_reg + (2**(AHB5_seq_item.size));
        end
        else begin
            address_reg = address_reg + (2**(AHB5_seq_item.size));
        end
        ////////////////////////////////////
        if (AHB5_seq_item.write == WRITE)
            AHB5_vif.write(AHB5_seq_item.rst_n,AHB5_seq_item.slv_sel,AHB5_seq_item.slv_enable,AHB5_seq_item.burst,AHB5_seq_item.wdata_arr[i],address_reg,AHB5_seq_item.size,AHB5_seq_item.strb);
        else if (AHB5_seq_item.write == READ)
            AHB5_vif.read(AHB5_seq_item.rst_n,AHB5_seq_item.slv_sel,AHB5_seq_item.slv_enable,AHB5_seq_item.burst,address_reg,AHB5_seq_item.size,AHB5_seq_item.strb);
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

task boundaries (input hburst_e burst, input logic [ADDR_WIDTH-1:0] address, input hsize_e size);
    case (burst)
        WRAP4  : wrap_size = 4  << size;
        WRAP8  : wrap_size = 8  << size;
        WRAP16 : wrap_size = 16 << size;
    endcase
    min_boundary = address & ~(wrap_size - 1);
    max_boundary = min_boundary + wrap_size;
endtask

endclass