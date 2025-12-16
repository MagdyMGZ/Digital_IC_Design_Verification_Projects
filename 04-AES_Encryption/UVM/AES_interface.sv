interface AES_if ();
    parameter N  = 128;
    parameter Nr = 10;
    parameter Nk = 4;
    logic [N-1:0] in;
    logic [N-1:0] key;
    logic [N-1:0] out;
endinterface