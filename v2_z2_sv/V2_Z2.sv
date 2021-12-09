`timescale 1ns / 1ps

module V2_Z2
    (
        input clk,
        input rst,
        input a,
        input b,
        input c,
        input d,
        input e,
        input f,
        output logic o1,
        output logic o2
    );
    
// SVA

property p1;
    @(posedge clk) o1 == o2;
endproperty

assert property (p1);

// -------------------------------------------- //    
    
// FF
logic d1_ff, d2_ff, q1_ff, q2_ff;

// MUX 
logic [2 : 0] sel;
logic [7 : 0] mux_i;
logic mux_o;

// LUT
logic lut1_o, lut2_o, lut3_o, lut4_o;

assign sel = {d, e, f};
assign d1_ff = mux_o;
assign o1 = q1_ff;
assign mux_i[3 : 0] = {a, c, b, b};
assign mux_i[7 : 4] = 4'b0101;

// FF
always_ff@(posedge clk) begin
    q1_ff <= rst ? 0 : d1_ff;
    q2_ff <= rst ? 0 : d2_ff;
end  

// MUX
assign mux_o = mux_i[sel];

// LUT
LUT #(.I(16'b0101001101010000)) 
lut1 (.lut_i({b, d, e, f}), .lut_o(lut1_o));

LUT #(.I(16'b0000100000000000)) 
lut2 (.lut_i({a, d, e, f}), .lut_o(lut2_o));

LUT #(.I(16'b0000010000000000)) 
lut3 (.lut_i({c, d, e, f}), .lut_o(lut3_o));

LUT #(.I(16'b1111111111111110)) 
lut4 (.lut_i({1'b0, lut2_o, lut1_o, lut3_o}), .lut_o(lut4_o));

assign d2_ff = lut4_o;
assign o2 = q2_ff;

    
endmodule
