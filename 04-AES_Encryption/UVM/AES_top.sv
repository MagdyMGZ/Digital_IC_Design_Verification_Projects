module top ();

import uvm_pkg::*;
`include "uvm_macros.svh"
import AES_pkg::*;

AES_if #(.N(N),.Nr(Nr),.Nk(Nk)) AES_vif ();

AES_Encrypt_Encrypted #(.N(AES_vif.N),.Nr(AES_vif.Nr),.Nk(AES_vif.Nk)) DUT (AES_vif.in,AES_vif.key,AES_vif.out);

initial begin
    uvm_config_db #(virtual AES_if)::set(null,"uvm_test_top","AES_IF",AES_vif);
    run_test();
end

endmodule