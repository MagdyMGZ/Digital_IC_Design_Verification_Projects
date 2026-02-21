class shift_reg_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(shift_reg_scoreboard);

    uvm_analysis_export #(shift_reg_seq_item) sb_export;
    uvm_tlm_analysis_fifo #(shift_reg_seq_item) sb_fifo;
    shift_reg_seq_item seq_item_sb;

    logic signed [5:0] out_ref;
    int error_count;
    int correct_count;

    function new(string name ="shift_reg_scoreboard",uvm_component parent = null);
        super.new(name,parent);
    endfunction //new()

    function void build_phase (uvm_phase phase);
        super.build_phase(phase);
        sb_export = new("sb_export",this);
        sb_fifo = new("sb_fifo",this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        sb_export.connect(sb_fifo.analysis_export);
    endfunction

    task run_phase (uvm_phase phase);
        super.run_phase(phase);
        forever begin
            sb_fifo.get(seq_item_sb);
            ref_model(seq_item_sb);
            if (seq_item_sb.dataout !== out_ref) begin
                `uvm_error("run_phase",$sformatf("comparison failed,transaction recieved by the DUT:%s while the referrence out :%0b",seq_item_sb.convert2string(),out_ref));     
                error_count++;
            end
            else begin
                `uvm_info("run_phase",$sformatf("correct output :%s ",seq_item_sb.convert2string()),UVM_HIGH);     
                correct_count++; 
            end
        end
    endtask 

    task ref_model(shift_reg_seq_item seq_item_chk);
      if (seq_item_chk.mode) // rotate
         if (seq_item_chk.direction) // left
            out_ref = {seq_item_chk.datain[4:0],seq_item_chk.datain[5]};
         else
            out_ref = {seq_item_chk.datain[0],seq_item_chk.datain[5:1]};
      else // shift
         if (seq_item_chk.direction) // left
            out_ref = {seq_item_chk.datain[4:0],seq_item_chk.serial_in};
         else
            out_ref = {seq_item_chk.serial_in,seq_item_chk.datain[5:1]};
    endtask    

    function void report_phase (uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("report_phase",$sformatf("Total successful counts of shift_reg : %0d",correct_count),UVM_MEDIUM);     
        `uvm_info("report_phase",$sformatf("Total failed counts of shift_reg : %0d",error_count),UVM_MEDIUM);     
    endfunction

endclass
