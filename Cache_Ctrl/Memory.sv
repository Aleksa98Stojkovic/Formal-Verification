`timescale 1ns / 1ps

module Memory
    #(
        parameter addr_width = 10,
        parameter data_width = 64
    )
    (
        input logic clk,
        input logic write_en,
        input logic [addr_width : 0] raddr,
        input logic [addr_width : 0] waddr,
        input logic [data_width - 1 : 0] wdata,
        output logic [data_width - 1 : 0] rdata
    );
    
logic [data_width - 1 : 0] mem [2 ** addr_width];

always_ff@(posedge clk) begin
    if(write_en) mem[waddr] <= wdata;
    rdata <= mem[raddr];    
end 
    
endmodule
