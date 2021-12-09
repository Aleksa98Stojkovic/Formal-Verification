module top(
	 input logic rst_i,
	 input logic clk_i,
	 input logic a,
	 input logic b,
	 input logic c,
	 input logic d,
	 input logic e,
	 input logic f,
	 output logic o1,
     output logic o2
);
	Circuit_v2_p2 uufv
	  (
	   .clk_i(clk_i),
	   .rst_i(rst_i),
	   .a(a),
	   .b(b),
	   .c(c),
	   .d(d),
	   .e(e),
	   .f(f),
	   .o1(o1),
	   .o2(o2));

	property p1;
		@(posedge clk) o1 == o2;
	endproperty

	assert property (p1);


endmodule
