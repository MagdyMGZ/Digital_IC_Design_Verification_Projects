# Formal Signoff - RISCV
# vcf -gui -f vcf_run_risc.tcl
# Appmode
set_fml_appmode FPV 
set_fml_var fml_fta_seq_debug true
# Design Setting
set design RISCV 
# Reset the Past FPV Check
set_fml_var fml_reset_property_check true
# Enable the default setting for most apps and formal variables within the Coverage and Fault Settings
signoff_config -type all
#Blackboxing Main Memory 
set_blackbox -designs {Data_Memory}
set_blackbox -designs {Instruction_Mem}
# Read Source Files and Inject Fault Option
read_file -top $design -format sverilog -sva -vcs {-f src_files.list} -inject_fault all
# COI Analysis Setting and Viewing its Coverage
set_fml_var fml_enable_coi_deadcode_check true -global
save_property_density_results -par_task FPV -db_name COI
view_coverage -cov_input COI -mode PD
# Compute OC Analysis and Viewing its Coverage
compute_bounded_cov -par_task FPV -max_proof_depth -1 -block
view_coverage -cov_input OC -mode OA+BA
# Compute FC Analysis
compute_formal_core
# signoff_check -effort low -time 12H -signoff_bound -1 -signoff_dashboard  # OCI + OC
# signoff_check -effort med -time 12H -signoff_bound -1 -signoff_dashboard  # FC + OC
# signoff_check -effort high -time 12H -signoff_bound -1 -signoff_dashboard # FTA + FC + OC
# Clock Definitions 
create_clock clk -period 100
# Reset Definitions 
create_reset areset -sense low
# Initialisation Commands 
sim_run -stable
sim_save_reset
# Proof
check_fv -block 
# Reports
report_fv -list > results.txt
