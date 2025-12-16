class adder_collector;
    mailbox #(adder_trans) in_mbx = new();
    mailbox #(adder_trans) out_mbx = new();
    
    adder_trans in_tr;
    adder_trans out_tr;

    covergroup adder_cv_grp;
        a_cp: coverpoint in_tr.a {bins a_0 = {0};
                            bins a_1 = {1};
                            bins a_2 = {2};
                            bins a_3 = {3};
                            bins a_trans[] = (0=>1),(1=>2),(2=>3);}

        b_cp: coverpoint in_tr.b {bins b_0 = {0};
                            bins b_1 = {1};
                            bins b_2 = {2};
                            bins b_3 = {3};
                            bins b_trans[] = (0=>1),(1=>2),(2=>3);}

        out_cp: coverpoint out_tr.out {ignore_bins max_out = {7};}
        axb: cross in_tr.a, in_tr.b;
    endgroup

    task run ();
        forever begin
            in_tr = new();
            out_tr = new();
            in_mbx.get(in_tr);
            out_mbx.get(out_tr);
            adder_cv_grp.sample();
        end
    endtask

    function new();
        adder_cv_grp = new();
    endfunction
endclass