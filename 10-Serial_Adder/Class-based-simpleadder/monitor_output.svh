class monitor_output;
    virtual adder_if vif;
    mailbox #(adder_trans) out_check_mbx = new();
    mailbox #(adder_trans) out_cov_mbx = new();

    function new (virtual adder_if vif);
        this.vif = vif;
    endfunction

    task run ();
        forever begin
            adder_trans tr = new();
            @(vif.cb_monitor iff (vif.cb_monitor.en_o == 1'b1)); // Not // @(posedge vif.clk iff (vif.cb_monitor.en_o == 1'b1));
            tr.out[2] = vif.cb_monitor.out;
            @(vif.cb_monitor);					 // Not // @(posedge vif.clk);
            tr.out[1] = vif.cb_monitor.out;
            @(vif.cb_monitor);					 // Not // @(posedge vif.clk);
            tr.out[0] = vif.cb_monitor.out;
            out_check_mbx.put(tr);
            out_cov_mbx.put(tr);
        end
    endtask
endclass