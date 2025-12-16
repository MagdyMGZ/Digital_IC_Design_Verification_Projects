class adder_driver;
    virtual adder_if vif;
    mailbox #(adder_trans) stimulus_mbx = new();

    function new (virtual adder_if vif);
        this.vif = vif;      
    endfunction

    task run ();
        forever begin
            adder_trans tr = new();
            stimulus_mbx.get(tr);
            @(posedge vif.clk); 		// OR // @(vif.cb_driver); 
            vif.cb_driver.en_i <= 1'b1;
            vif.cb_driver.ina <= tr.a[1];
            vif.cb_driver.inb <= tr.b[1];
            @(posedge vif.clk);
            vif.cb_driver.ina <= tr.a[0];
            vif.cb_driver.inb <= tr.b[0];
            @(posedge vif.clk); 		// OR // @(vif.cb_driver); 
            vif.cb_driver.en_i <= 1'b0;
            wait(vif.cb_monitor.en_o == 1'b1);
            repeat(3) @(posedge vif.clk); 	// OR // @(vif.cb_driver); 
        end
    endtask
endclass