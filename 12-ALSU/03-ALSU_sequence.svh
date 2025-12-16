class ALSU_reset_sequence extends uvm_sequence #(ALSU_seq_item);
    
    `uvm_object_utils(ALSU_reset_sequence);

    ALSU_seq_item seq_item;

    function new(string name="ALSU_reset_sequence");
        super.new(name);
    endfunction

    task body;
        seq_item = ALSU_seq_item::type_id::create("seq_item");
        start_item(seq_item);
        seq_item.reset = 1;
        seq_item.serial_in = 0;
        seq_item.red_op_B = 0;
        seq_item.red_op_A = 0;
        seq_item.bypass_A = 0;
        seq_item.bypass_B = 0;
        seq_item.cin = 0;
        seq_item.direction = 0;
        seq_item.A = 0;
        seq_item.B = 0;
        seq_item.opcode = 0;
        finish_item(seq_item);
    endtask
endclass
    
class ALSU_main_sequence extends uvm_sequence #(ALSU_seq_item);
        `uvm_object_utils(ALSU_main_sequence);

        ALSU_seq_item seq_item;
         function new(string name="ALSU_main_sequence");
         super.new(name);
         endfunction 

         task body;
            repeat(100000) begin
             seq_item = ALSU_seq_item::type_id::create("seq_item");
             start_item(seq_item);
                assert (seq_item.randomize());
             finish_item(seq_item);    
            end
         endtask      
endclass

class direct_test_sequence extends uvm_sequence #(ALSU_seq_item);
    `uvm_object_utils(direct_test_sequence);
       
         ALSU_seq_item seq_item;

         function new(string name="direct_test_sequence");
         super.new(name);
         endfunction 

         task body;
             seq_item = ALSU_seq_item::type_id::create("seq_item");
             start_item(seq_item);
                seq_item.A=50;
                seq_item.B=50;
                #1;
                seq_item.opcode=3'b000;
                    #2;
                seq_item.opcode=3'b001;
                    #2; 
                seq_item.opcode=3'b010;
                    #2;
                seq_item.opcode=3'b011;
                    #2;
                seq_item.opcode=3'b100;
                    #2;
                seq_item.opcode=3'b101;
                    #2;
             finish_item(seq_item);    
         endtask    
endclass
