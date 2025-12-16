module AES_128 (plan_text_128, cipher_key_128, cipher_text_128,flag);


//--------------------------------------
// --------------------inputs-----------
//--------------------------------------
input wire [127:0] plan_text_128;
input wire [127:0] cipher_key_128;
input wire         flag;

//---------------------------------
//------------output---------------
//---------------------------------
output wire [127:0] cipher_text_128;
//-------------------------------

wire [127:0] encrypted_128,decrypted_128;



AES_Encrypt a (plan_text_128,cipher_key_128,encrypted_128);

AES_Decrypt a2 (encrypted_128,cipher_key_128,decrypted_128);


assign cipher_text_128 = (flag) ? encrypted_128 : decrypted_128;


endmodule