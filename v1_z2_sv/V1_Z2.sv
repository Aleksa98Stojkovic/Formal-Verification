`timescale 1ns / 1ps

module V1_Z2
    (
        input clk,
        input rst,
        input a,
        input b,
        input c,
        input d,
        input e,
        input f,
        input g,
        input h,
        output logic o1,
        output logic o2
    );
    
// SVA

property p1;
    @(posedge clk) o1 == o2;
endproperty

assert property (p1);

// -------------------------------------- //    
    
// D_FF    
logic d1_ff, q1_ff, d2_ff, q2_ff;

// MUX
logic mux_o;
logic [3 : 0] sel;
logic [15 : 0] mux_i;    

// DEC
logic [3 : 0] dec1_o, dec2_o;
logic en1, en2;
logic [1 : 0] dec1_i, dec2_i;

// Comb logic
logic comb;  

assign en1 = 1;
assign en2 = 1;
assign d1_ff = mux_o;
assign sel = {d, c, b, a};
assign mux_i[3 : 0] = dec1_o;
assign mux_i[7 : 4] = dec2_o;
assign mux_i[15 : 8] = {8{1'b1}};
assign dec1_i = {f, e};
assign dec2_i = {h, g};

// D_FF
always_ff@(posedge clk) begin
    q1_ff <= rst ? 0 : d1_ff;
    q2_ff <= rst ? 0 : d2_ff;
end

// MUX
assign mux_o = mux_i[sel];

// DEC
always_comb begin
    dec1_o = 0;
    if(en1) begin
        dec1_o = 4'b0001 << dec1_i;
    end
    
    dec2_o = en2 ? (4'b0001 << dec2_i) : 0;
end

assign o1 = q1_ff;

always_comb begin
    logic temp;
    
    temp = (!a)&(!b)&(!c)&(!e)&(!f);
    temp |= (a)&(!b)&(!c)&(e)&(!f);
    temp |= (!a)&(b)&(!c)&(!e)&(f);
    temp |= (a)&(b)&(!c)&(e)&(f);
    temp |= (!a)&(!b)&(c)&(!g)&(!h);
    temp |= (a)&(!b)&(c)&(g)&(!h);
    temp |= (!a)&(b)&(c)&(!g)&(h);
    temp |= (a)&(b)&(c)&(g)&(h);
    temp &= !d;
    temp |= d;
    
    d2_ff = temp; 
end

assign o2 = q2_ff;

endmodule
