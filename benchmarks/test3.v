// test verilog file
module factorization8_simplified (i1,i2,i3,o1);
input i1;
input i2;
input i3;
wire n1;
wire n2;
wire n3;
wire n4;
output o1;
assign n3 = ~i1 &  i2;
assign n2 =  n3 &  n4;
assign n1 = ~n2 &  n4;
assign n4 =  i2 &  i3;
assign o1 =  ~n1;
endmodule
