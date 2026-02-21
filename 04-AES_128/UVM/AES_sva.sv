module AES_sva #(parameter N=128,parameter Nr=10,parameter Nk=4) (in,key,out);
input [127:0] in;
input [N-1:0] key;
input [127:0] out;

logic [127:0] out_exp;
int output_file, key_file;

always @(*) begin
    key_file = $fopen("./key_sva.txt","w");
    $fdisplay(key_file,"%h \n%h",in,key);
    $fclose(key_file);
    $system($sformatf("python ../SIM/Golden_model_sva.py"));
    output_file = $fopen("./output_sva.txt","r");
    $fscanf(output_file,"%h",out_exp);
    $fclose(output_file);

    assert final (out == out_exp);
    cover  final (out == out_exp);
end

endmodule