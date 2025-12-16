class ALSU_coverage extends uvm_component;
        `uvm_component_utils(ALSU_coverage);
         uvm_analysis_export #(ALSU_seq_item) cov_export;
         uvm_tlm_analysis_fifo #(ALSU_seq_item) cov_fifo;
         ALSU_seq_item seq_item_cov;

         covergroup cvg;
          A_cp:
            coverpoint seq_item_cov.A{
                bins data_max ={MAXPOS};
                bins data_min ={MAXNEG};
                bins data_0   ={ZERO}  ;
                bins Data_walkingones={001,010,100};
                bins data_default=default;
            }

            B_cp: 
            coverpoint seq_item_cov.B{
                bins data_max ={MAXPOS};
                bins data_min ={MAXNEG};
                bins data_0   ={ZERO}  ;
                bins Data_walkingones={001,010,100};
                bins data_default=default;
            }

            red_A_cp:
            coverpoint seq_item_cov.red_op_A{
                bins data0 ={0};
                bins data1 ={1};
            }

            red_B_cp:
            coverpoint seq_item_cov.red_op_B{
                bins data0 ={0};
                bins data1 ={1};
            }

            ALU_cp:
            coverpoint seq_item_cov.opcode{
               bins Bins_shift[]={shift_op,rot_op};
               bins Bins_arith[]={add_op,mul_op};
               bins Bins_bitwise[]={or_op,xor_op};
               illegal_bins Bins_invalid={INVALID_6,INVALID_7};
               bins Bins_trans=(or_op=>xor_op=>add_op=>mul_op=>shift_op=>rot_op);  
               //shift_bin
               bins sh={shift_op};  
            }

            cross_one:
            cross ALU_cp,A_cp,B_cp
            {
              ignore_bins unw0=binsof (B_cp.Data_walkingones);
              ignore_bins unw1=binsof (A_cp.Data_walkingones);
              ignore_bins unw2=binsof (ALU_cp.Bins_bitwise);
              ignore_bins unw4=binsof (ALU_cp.Bins_shift);
              ignore_bins unw5=binsof (ALU_cp.Bins_trans);
              ignore_bins wr=binsof (ALU_cp.sh);
            }

            cross_two:
            cross ALU_cp,seq_item_cov.cin
            {
              ignore_bins unw6=binsof (ALU_cp.Bins_bitwise);
              ignore_bins unw8=binsof (ALU_cp.Bins_shift);
              ignore_bins unw9=binsof (ALU_cp.Bins_trans);
              ignore_bins wr =binsof (ALU_cp.sh);
            }

            cross_three:
            cross ALU_cp,seq_item_cov.serial_in
            {
              ignore_bins unw11=binsof (ALU_cp.Bins_bitwise);
              ignore_bins unw13=binsof (ALU_cp.Bins_arith);
              ignore_bins unw14=binsof (ALU_cp.Bins_trans);
              ignore_bins unw10=binsof (ALU_cp.Bins_shift);               
            }

            cross_four:
            cross ALU_cp,seq_item_cov.direction
            {
              ignore_bins unw15=binsof (ALU_cp.Bins_bitwise);
              ignore_bins unw17=binsof (ALU_cp.Bins_arith);
              ignore_bins unw18=binsof (ALU_cp.Bins_trans); 
              ignore_bins wr =binsof (ALU_cp.sh);
            }

            cross_five:
            cross ALU_cp,red_A_cp,A_cp,B_cp
            {
              ignore_bins unw20=binsof (ALU_cp.Bins_arith);
              ignore_bins unw21=binsof (ALU_cp.Bins_trans); 
              ignore_bins unw22=binsof (ALU_cp.Bins_shift);
              ignore_bins wr =binsof (ALU_cp.sh);
              ignore_bins unw23=binsof (red_A_cp.data0);
              ignore_bins unw24=binsof (A_cp.data_0);
              ignore_bins unw25=binsof (A_cp.data_max);
              ignore_bins unw26=binsof (A_cp.data_min);
              ignore_bins unw27=binsof (B_cp.Data_walkingones);
              ignore_bins unw28=binsof (B_cp.data_max);
              ignore_bins unw29=binsof (B_cp.data_min);              
            }

            cross_six:
            cross ALU_cp,red_B_cp,A_cp,B_cp
            {
              ignore_bins unw31=binsof (ALU_cp.Bins_arith);
              ignore_bins unw32=binsof (ALU_cp.Bins_trans); 
              ignore_bins unw33=binsof (ALU_cp.Bins_shift);
              ignore_bins wr =binsof (ALU_cp.sh);
              ignore_bins unw34=binsof (red_B_cp.data0);
              ignore_bins unw35=binsof (B_cp.data_0);
              ignore_bins unw36=binsof (B_cp.data_max);
              ignore_bins unw37=binsof (B_cp.data_min);
              ignore_bins unw38=binsof (A_cp.Data_walkingones);
              ignore_bins unw39=binsof (A_cp.data_max);
              ignore_bins unw40=binsof (A_cp.data_min);    
            }

            invalid_case:
            cross red_A_cp,red_B_cp,ALU_cp
            {
              ignore_bins unw41=binsof (ALU_cp.Bins_arith);
              ignore_bins unw42=binsof (ALU_cp.Bins_trans); 
              ignore_bins unw43=binsof (ALU_cp.Bins_shift);
              ignore_bins wr=binsof (ALU_cp.sh);
            }

         endgroup

         function new(string name ="ALSU_coverage",uvm_component parent = null);
            super.new(name,parent);
            cvg = new();
        endfunction //new()

        function void build_phase (uvm_phase phase);
            super.build_phase(phase);
            cov_export = new("cov_export",this);
            cov_fifo = new("cov_fifo",this);
        endfunction

        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            cov_export.connect(cov_fifo.analysis_export);
        endfunction

        task run_phase (uvm_phase phase);
        super.run_phase(phase);
            forever begin
               cov_fifo.get(seq_item_cov);
               cvg.sample();
            end
        endtask 
endclass
    