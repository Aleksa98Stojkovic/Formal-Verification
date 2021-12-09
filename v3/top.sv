module top (
    input logic clk,
	input logic rst,
	output logic rt1, 
	output logic rt8,
	output logic rdy1,
	output logic rdy3,
	output logic rdy4,
	output logic rdy5,
	output logic rdy6,
	output logic rdy9,
	output logic start1,
	output logic start4,
	output logic start5,
	output logic start7,
	output logic start9,
	output logic er2,
	output logic er3,
	output logic er5,
	output logic er6,
	output logic endd1,
	output logic endd5,
	output logic endd6,
	output logic endd7,
	output logic stop5,
	output logic stop6,
	output logic status_valid7,
	output logic instartsv7,
	output logic enable8,
	output logic interrupt9,
	output logic ack10,
	output logic req10,
	output logic help1_o
) ;
	z1 my_module
	  (
	   .clk(clk),
	   .rst(rst),
	   .rt1(rt1), 
	   .rt8(rt8),
	   .rdy1(rdy1),
	   .rdy3(rdy3),
	   .rdy4(rdy4),
	   .rdy5(rdy5),
	   .rdy6(rdy6),
	   .rdy9(rdy9),
	   .start1(start1),
	   .start4(start4),
	   .start5(start5),
	   .start7(start7),
	   .start9(start9),
	   .er2(er2),
	   .er3(er3),
	   .er5(er5),
	   .er6(er6),
	   .endd1(endd1),
	   .endd5(endd5),
	   .endd6(endd6),
	   .endd7(endd7),
	   .stop5(stop5),
	   .stop6(stop6),
	   .status_valid7(status_valid7),
	   .instartsv7(instartsv7),
	   .enable8(enable8),
	   .interrupt9(interrupt9),
	   .ack10(ack10),
	   .req10(req10),
	   .help1_o(help1_o)
	   
	   );

default clocking @(posedge clk); endclocking
default disable iff (rst);

	property p1;
		  help1_o;
	endproperty

	property p2;
		  er2[*3] |=> !er2;
	endproperty

	property p3;
		  er3 && rdy3 |=> !er3 || !rdy3;
	endproperty

	property p4;
		  !rdy4 until start4;
	endproperty	

	property p5;
		  endd5 || stop5 || er5 |=> !rdy5;
	endproperty

	property p6;
		  endd6 || stop6 || er6 |-> rdy6;
	endproperty

	property p7;
		  endd7 |-> !(start7 || status_valid7);
	endproperty

	property p8_1;
		  rt8 |-> !enable8;
	endproperty
		  
	property p8_2;
		  $fell(rt8) |=> enable8[*];
	endproperty

	property p9_1;
		  $fell(start9) |-> interrupt9;
	endproperty
		  
	property p9_2;
		  $fell(rdy9) |-> interrupt9;
	endproperty

	property p10;
		  req10 |-> ##5 ack10;
	endproperty

	assert property (p1);
	assert property (p2);
	assert property (p3);
	assert property (p4);	//!!!
	assert property (p5);
	assert property (p6);
	assert property (p7);
	assert property (p8_1);
	assert property (p8_2);
	assert property (p9_1);	// nismo sigurni
	assert property (p9_2);
	assert property (p10);

endmodule
