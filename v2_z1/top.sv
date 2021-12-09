module top(
	 input logic rst,
	 input logic clk,
	 input logic a,
	 input logic b,
	 input logic c,
	 input logic d,
	 input logic e,
	 input logic f,
	 input logic g,
	 input logic h,
	 output logic out1,
     output logic out2
);
	Circuit_v2_p1 uufv
	  (
	   .clk(clk),
	   .rst(rst),
	   .a(a),
	   .b(b),
	   .c(c),
	   .d(d),
	   .e(e),
	   .f(f),
	   .g(g),
	   .h(h),
	   .out1(out1),
	   .out2(out2));

	property p1;
		@(posedge clk) out1 == out2;
	endproperty

	assert property (p1);


endmodule
