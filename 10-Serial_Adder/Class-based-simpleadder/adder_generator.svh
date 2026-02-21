class adder_generator;
    mailbox #(adder_trans) stimulus_mbx  = new();

    task run (int count);
        repeat(count) begin
            adder_trans tr = new();
            Randome_Stimulus : assert(tr.randomize());
            stimulus_mbx.put(tr);
        end
    endtask
endclass