class monitor_input;
    virtual adder_if vif;
    mailbox #(adder_trans) in_check_mbx = new();
    mailbox #(adder_trans) in_cov_mbx = new();

    function new (virtual adder_if vif);
        this.vif = vif;
    endfunction

    task run ();
        forever begin
            adder_trans tr = new();
            @(vif.cb_monitor iff (vif.cb_monitor.en_i == 1'b1)); // Not // @(posedge vif.clk iff (vif.cb_monitor.en_i == 1'b1));
            tr.a[1] = vif.cb_monitor.ina;
            tr.b[1] = vif.cb_monitor.inb;
            @(vif.cb_monitor);					 // Not // @(posedge vif.clk);
            tr.a[0] = vif.cb_monitor.ina;
            tr.b[0] = vif.cb_monitor.inb;
            @(vif.cb_monitor);					 // Not // @(posedge vif.clk);
            in_check_mbx.put(tr);
            in_cov_mbx.put(tr);
        end
    endtask
endclass