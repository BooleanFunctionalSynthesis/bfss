// test verilog file
module factorization8_simplified (y1,y2,x1,x2,x3,o1);
input x1;
input x2;
input x3;
input y1;
input y2;
wire f1;
wire f2;
wire f3;
wire n1;
wire n2;
wire n3;
wire n4;
wire n5;
output o1;
assign n1 =  y1 & y2;
assign f1 =  n1 & x1;
assign n2 = ~y2 & x3;
assign f2 =  n2 & x2;
assign n3 = ~y1 & y2;
assign f3 =  n3 & ~x3;
assign n4 = ~f1 & ~f2;
assign n5 = n4 & ~f3;
assign o1 = n5;
endmodule
