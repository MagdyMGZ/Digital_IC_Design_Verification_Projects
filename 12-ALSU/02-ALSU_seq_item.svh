class ALSU_seq_item extends uvm_sequence_item;
    `uvm_object_utils(ALSU_seq_item);
    rand bit reset;
    rand bit serial_in;
    rand bit direction;
    rand bit cin;
    rand bit red_op_A;
    rand bit red_op_B;
    rand bit bypass_A;
    rand bit bypass_B;
    rand bit [2:0] opcode;
    randc bit signed [2:0] A;
    randc bit signed [2:0] B;
    bit signed [5:0] out;
    bit [15:0] leds;
    bit signed [5:0] out_G;
    bit [15:0] leds_G;

    rand opcode_valid_e op_arr [6] ;

        logic [2:0] arr []='{1,2,5,6,7};
        logic [2:0] hig []='{1,2,4};
        logic [2:0] low []='{3,0,5,6,7};

     constraint rst {reset dist {1:=10,0:=90};}
        
        constraint inputs 
        {
            if(opcode==add_op||opcode==mul_op)
            {
                A dist {MAXNEG:=30,MAXPOS:=30,ZERO:=30,arr:=10};
                B dist {MAXNEG:=30,MAXPOS:=30,ZERO:=30,arr:=10};
            }
            else if ((opcode==or_op||opcode==xor_op)&&red_op_A==1)
            {
                A dist {hig:/90,low:/10};
                B==0;
            }
            else if ((opcode==or_op||opcode==xor_op)&&red_op_B==1)
            {
                B dist {hig:/90,low:/10};
                A==0;
            }
            else if (opcode==or_op||opcode==xor_op||opcode==INVALID_6||opcode==INVALID_7)
            {
                A inside {[0:7]};
                B inside {[0:7]};
            }
        }

        constraint valid {opcode dist {[or_op:rot_op]:=80,INVALID_6:=10,INVALID_7:=10};}
        
        constraint bypasses 
        {
            bypass_A dist{0:=90,1:=10};
            bypass_B dist{0:=90,1:=10};
        }

        constraint array 
        {
            foreach (op_arr[i])
            {
            if (i!=0) 
            {
                foreach (op_arr[j])
                {
                    if (i>j)
                    {
                        op_arr[i]!=op_arr[j];
                    }
                } 
            }
            }
        }

    function new(string name="ALSU_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf ("%s reset=%0b ,diretion=%0b,cin=%0b,serial_in=%0b,A=%0d,B=%0d,opcode=%0d,red_op_A=%0d,red_op_B=%0d,bypass_A=%0d,bypass_B=%0d,out=%0d,leds=%0d,out_G=%0d,leds_G=%0d",super.convert2string(),reset,direction,cin,serial_in,A,B,opcode,red_op_A,red_op_B,bypass_A,bypass_B,out,leds,out_G,leds_G);
    endfunction
    function string convert2string_stimulus();
        return $sformatf ("%s reset=%0b ,diretion=%0b,cin=%0b,serial_in=%0b,A=%0d,B=%0d,opcode=%0d,red_op_A=%0d,red_op_B=%0d,bypass_A=%0d,bypass_B=%0d",super.convert2string(),reset,direction,cin,serial_in,A,B,opcode,red_op_A,red_op_B,bypass_A,bypass_B);
    endfunction
endclass