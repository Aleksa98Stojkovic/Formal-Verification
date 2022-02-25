`timescale 1ns / 1ps

module Memory
    #(
        parameter addr_width = 10,
        parameter data_width = 64,
        parameter init_zero = 0
    )
    (
        input logic clk,
        input logic write_en,
        input logic [addr_width : 0] raddr,
        input logic [addr_width : 0] waddr,
        input logic [data_width - 1 : 0] wdata,
        output logic [data_width - 1 : 0] rdata
    );
    
typedef logic [data_width - 1 : 0] mem_tag_type [2 ** addr_width];

function mem_data_type init_mem_data();

    mem_tag_type mem;
    for(int i = 0; i < 2 ** addr_width; i++) begin
        mem[i] = init_zero ? 0 : i + 1;
    end
    
    return mem;    

endfunction
    
logic [data_width - 1 : 0] mem [2 ** addr_width];

always_ff@(posedge clk) begin
    if(write_en) mem[waddr] <= wdata;
    rdata <= mem[raddr];    
end 
    
endmodule
