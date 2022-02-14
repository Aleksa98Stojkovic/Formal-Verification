`timescale 1ns / 1ps

module Hanoi_tb ();

parameter S = 3;

logic clk;
logic rst;
logic [1 : 0] fr;
logic [1 : 0] to;
logic [(S + 1) * $clog2(S + 1) - 1 : 0] fr_o;
logic [(S + 1) * $clog2(S + 1) - 1 : 0] to_o;

Hanoi #(.S(S)) inst (.clk(clk), .rst(rst), .fr(fr), .to(to), .fr_o(fr_o), .to_o(to_o));
always begin
    #10ns clk = ~clk; 
end

initial begin
    rst = 1;
    clk = 0;
    #30ns;
    rst = 0;
end

initial begin
  repeat(4) begin
    @(posedge clk) begin
        fr <= 0;
        to <= 1;
    end
    @(posedge clk) begin
        fr <= 0;
        to <= 1;
    end
    @(posedge clk) begin
        fr <= 0;
        to <= 2;
    end
    @(posedge clk) begin
        fr <= 1;
        to <= 0;
    end
    @(posedge clk) begin
        fr <= 2;
        to <= 1;
    end
    @(posedge clk) begin
        fr <= 0;
        to <= 1;
    end
  end
end
   

endmodule
