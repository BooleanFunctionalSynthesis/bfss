// test verilog file
module factorization8_simplified (y1,x1,x2,o1);
input x1;
input x2;
input y1;
wire n1;
wire n2;
wire n3;
wire n4;
wire n5;
output o1;
assign n1 =  ~x1 & x2;
assign n2 =  x1 & ~x2;
assign n3 = ~x2 & y1;
assign n4 = n2 & n3;
assign n5 = n1 & ~n4;
assign o1 = ~n5;
endmodule
