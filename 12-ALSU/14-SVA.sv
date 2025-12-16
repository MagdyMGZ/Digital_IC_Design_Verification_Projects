module SVA (ALSU_if.DUT alsu_IF);

    int cin_signed;
    assign cin_signed = alsu_IF.cin;

    property asser1;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h0)&&(alsu_IF.red_op_A&&alsu_IF.red_op_B&& ~alsu_IF.bypass_A && ~alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==(|$past(alsu_IF.A,2)));
    endproperty

    property asser2;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h0)&&(alsu_IF.red_op_B&&~alsu_IF.red_op_A&&~alsu_IF.bypass_A&&~alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==(|$past(alsu_IF.B,2)));
    endproperty

    property asser3;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h1)&&(alsu_IF.red_op_A&&alsu_IF.red_op_B && !alsu_IF.bypass_A && !alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==(^$past(alsu_IF.A,2)));
    endproperty

    property asser4;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h1)&&(alsu_IF.red_op_B && !alsu_IF.red_op_A && !alsu_IF.bypass_A && !alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==(^$past(alsu_IF.B,2)));
    endproperty

    property asser5;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h2)&&((alsu_IF.red_op_B)||(alsu_IF.red_op_A))) |-> ##2  ((alsu_IF.out==0));
    endproperty  

    property asser6;
   @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h2)&&(~alsu_IF.red_op_B && ~alsu_IF.red_op_A && ~alsu_IF.bypass_A && ~alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==($past(alsu_IF.B,2)+$past(alsu_IF.A,2)+$past(cin_signed,2)));
    endproperty    

    property asser7;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h3)&&(alsu_IF.red_op_B || alsu_IF.red_op_A)) |-> ##2  ((~alsu_IF.out)&& (alsu_IF.leds==~$past(alsu_IF.leds)));
    endproperty      

    property asser8;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h4)&&(alsu_IF.red_op_B || alsu_IF.red_op_A)) |-> ##2  ((~alsu_IF.out) && (alsu_IF.leds==~$past(alsu_IF.leds)));
    endproperty      

    property asser9;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h5)&&(alsu_IF.red_op_B || alsu_IF.red_op_A)) |-> ##2  ((~alsu_IF.out) && (alsu_IF.leds==~$past(alsu_IF.leds)));
    endproperty      

    property asser10;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h3)&&(~alsu_IF.red_op_B && ~alsu_IF.red_op_A)&& ~alsu_IF.bypass_A && ~alsu_IF.bypass_B) |-> ##2  (alsu_IF.out==(($past(alsu_IF.A,2))*($past(alsu_IF.B,2))));
    endproperty 

    property asser11;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h4)&&~alsu_IF.red_op_B && ~alsu_IF.red_op_A&&alsu_IF.direction && ~alsu_IF.bypass_A && ~alsu_IF.bypass_B) |-> ##2  (alsu_IF.out==({$past(alsu_IF.out[4:0],1),$past(alsu_IF.serial_in,2)}));
    endproperty

    property asser12;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h4)&&~alsu_IF.red_op_B && ~alsu_IF.red_op_A&&~alsu_IF.direction&& ~alsu_IF.bypass_A && ~alsu_IF.bypass_B) |-> ##2  (alsu_IF.out==({$past(alsu_IF.serial_in,2),$past(alsu_IF.out[5:1],1)}));
    endproperty   

    property asser13;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h5)&& (~alsu_IF.red_op_B && ~alsu_IF.red_op_A)&&(alsu_IF.direction) && ~alsu_IF.bypass_A && ~alsu_IF.bypass_B) |-> ##2  (alsu_IF.out=={$past(alsu_IF.out[4:0],1),$past(alsu_IF.out[5],1)});
    endproperty       
    
    property asser14;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode==3'h5)&&(~alsu_IF.red_op_B && ~alsu_IF.red_op_A)&&(~alsu_IF.direction) && ~alsu_IF.bypass_A && ~alsu_IF.bypass_B) |-> ##2  (alsu_IF.out=={$past(alsu_IF.out[0],1),$past(alsu_IF.out[5:1],1)});
    endproperty 

    property asser15;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode!=3'h6)&&(alsu_IF.opcode!=3'h7)&&(~alsu_IF.red_op_B && ~alsu_IF.red_op_A)&&alsu_IF.bypass_B && alsu_IF.bypass_A) |-> ##2  (alsu_IF.out==($past(alsu_IF.A,2)));
    endproperty 
    
    property asser16;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset)  ((alsu_IF.opcode!=3'h6)&&(alsu_IF.opcode!=3'h7)&& (~alsu_IF.red_op_B && ~alsu_IF.red_op_A)&&alsu_IF.bypass_B && !alsu_IF.bypass_A) |-> ##2  (alsu_IF.out==($past(alsu_IF.B,2)));
    endproperty 

    property asser17;
    @(negedge alsu_IF.reset) alsu_IF.reset  |-> ##2 (~alsu_IF.out);
    endproperty 

    property asser18;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h0)&&(~alsu_IF.red_op_B&&~alsu_IF.red_op_A&&~alsu_IF.bypass_A&&~alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==($past(alsu_IF.B,2))|($past(alsu_IF.A,2)));
    endproperty

    property asser19;
    @(posedge alsu_IF.clk) disable iff(alsu_IF.reset) ((alsu_IF.opcode==3'h1)&&(~alsu_IF.red_op_B&&~alsu_IF.red_op_A&&~alsu_IF.bypass_A&&~alsu_IF.bypass_B)) |-> ##2  (alsu_IF.out==($past(alsu_IF.A,2))^($past(alsu_IF.B,2)));
    endproperty

    as1:assert property (asser1) else $display("ERROR1"); 
    as2:assert property (asser2) else $display("ERROR2");
    as3:assert property (asser3) else $display("ERROR3"); 
    as4:assert property (asser4) else $display("ERROR4");
    as5:assert property (asser5) else $display("ERROR5");
    as6:assert property (asser6) else $display("ERROR6"); 
    as7:assert property (asser7) else $display("ERROR7");
    as8:assert property (asser8) else $display("ERROR8");
    as9:assert property (asser9) else $display("ERROR9"); 
    as10:assert property (asser10) else $display("ERROR10");
    as11:assert property (asser11) else $display("ERROR11");
    as12:assert property (asser12) else $display("ERROR12"); 
    as13:assert property (asser13) else $display("ERROR13");
    as14:assert property (asser14) else $display("ERROR14");
    as15:assert property (asser15) else $display("ERROR15"); 
    as16:assert property (asser16) else $display("ERROR16");
    as17:assert property (asser17) else $display("ERROR17");
    as18:assert property (asser18) else $display("ERROR18");
    as19:assert property (asser19) else $display("ERROR19");


    cv1:cover property (asser1);
    cv2:cover property (asser2);
    cv3:cover property (asser3);
    cv4:cover property (asser4);
    cv5:cover property (asser5);
    cv6:cover property (asser6);
    cv7:cover property (asser7);
    cv8:cover property (asser8);
    cv9:cover property (asser9);
    cv10:cover property (asser10);
    cv11:cover property (asser11);
    cv12:cover property (asser12);
    cv13:cover property (asser13);
    cv14:cover property (asser14);
    cv15:cover property (asser15);
    cv16:cover property (asser16);
    cv17:cover property (asser17);
    cv18:cover property (asser18);
    cv19:cover property (asser19);


endmodule