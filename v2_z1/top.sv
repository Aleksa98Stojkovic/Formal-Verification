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
	 output logic o1,
     output logic o2
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
	   .o1(o1),
	   .o2(o2));

	property p1;
		@(posedge clk) o1 == o2;
	endproperty

	assert property (p1);


endmodule
