class adder_trans;
    rand bit [1:0] a;
    rand bit [1:0] b;
         bit [2:0] out;

    constraint a_c { a dist {0:/20, [1:3]:/80}; }

    constraint b_c { b dist {0:/20, [1:3]:/80}; }
endclass