class adder_checker;
    mailbox #(adder_trans) in_mbx = new();
    mailbox #(adder_trans) out_mbx = new();

    int error_count, correct_count;
    bit done;

    task run ();
        forever begin
            adder_trans in_tr = new();
            adder_trans out_tr = new();
            in_mbx.get(in_tr);
            out_mbx.get(out_tr);
            if (out_tr.out !== (in_tr.a + in_tr.b)) begin
                $display("FAIL: %0d + %0d = %0d (expected %0d)", in_tr.a, in_tr.a, out_tr.out, in_tr.a + in_tr.a);
                error_count++;
            end
            else begin
                $display("PASS: %0d + %0d = %0d", in_tr.a, in_tr.b, out_tr.out);
                correct_count++;
            end
            if (correct_count == TESTS) done = 1;
        end
    endtask
endclass