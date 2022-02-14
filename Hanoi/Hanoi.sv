// Ogrnicenja za SVA
// Ograniciti da sp_fr nikada nije 0
// Mora vaziti data_fr < data_to
// Trazim trenutak kada je stack pointer za poslednji stap 3

// default clocking @(posedge clk); endclocking
// default disable iff (rst);
// cover property (RF[2][(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] == S);
// cover property (wdata_b[(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] == S);
// assume property(sp_fr != 0);
// assume property(data_fr < data_to);

`timescale 1ns / 1ps

module Hanoi
    #(
        parameter S = 3
    )
    (
        input clk,
        input rst,
        input [1 : 0] fr,
        input [1 : 0] to,
        // Dummy izlaz kako bih elaborirao
        output logic [(S + 1) * $clog2(S + 1) - 1 : 0] fr_o,
        output logic [(S + 1) * $clog2(S + 1) - 1 : 0] to_o
    );
    
// Register File
// Register File's entery layout : stack pointer | rings on a stick 
// Stap 0   3 | 1, 2, 3 -> 2 | 0, 2, 3
// Stap 1   0 | 0, 0, 0 -> 0 | 0, 0, 0            
// Stap 2   0 | 0, 0, 0 -> 1 | 0, 0, 1
// For a given S S + 1 states are needed for stack pointer
// 0 -> there is no ring, 1 -> the smallest ring, 2 -> the middle ring, 3 -> the biggest one, in case of S = 3
logic [(S + 1) * $clog2(S + 1) - 1 : 0] RF [3];
logic [1 : 0] r_address_a, r_address_b;
logic [1 : 0] w_address_a, w_address_b;
logic [(S + 1) * $clog2(S + 1) - 1 : 0] rdata_a, rdata_b, wdata_a, wdata_b;
logic write_en;

// Cominatonal Logic for Processing
logic [$clog2(S + 1) - 1 : 0] sp_fr, sp_to, data_fr, data_to;

// Register write_en
logic [1 : 0] write_en_reg, write_en_next;

// Assigments
assign r_address_a = fr;
assign r_address_b = to;
assign w_address_a = fr;    
assign w_address_b = to;    
assign write_en = write_en_reg; // Potential source of throubles
assign sp_fr = rdata_a[(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)];
assign sp_to = rdata_b[(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)];
assign fr_o = rdata_a;
assign to_o = rdata_b;
assign write_en_next = 1;

// Register File Implementation
always_ff@(posedge clk) begin
    if(rst) begin
        
        RF[0] <= 0;
        for(int i = 0; i < S; i++) begin
            RF[0][(i + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] <= S - i;
        end
        RF[0][(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] <= S;
       
        RF[1] <= 0;
        RF[2] <= 0;
    end
    else begin
        if(write_en) begin
            RF[w_address_a] <= wdata_a;
            RF[w_address_b] <= wdata_b;
        end
    end    
end

assign rdata_a = RF[r_address_a];
assign rdata_b = RF[r_address_b]; 

// Implementation of the Combinational Logic for Processing
always_comb begin
    
    logic [S * $clog2(S + 1) - 1 : 0] only_data_a, only_data_b;
    logic [(S + 1) * $clog2(S + 1) - 1 : 0] RF_next_fr, RF_next_to;
     
    // Extracting only info about sticks and not about stack pointers
    only_data_a = rdata_a[S * $clog2(S + 1) - 1 : 0];
    only_data_b = rdata_b[S * $clog2(S + 1) - 1 : 0];
    
    // Initialization
    data_fr = 0;
    data_to = 0;
    RF_next_fr = rdata_a;
    RF_next_to = rdata_b;
    
    // Changing the values of the stack pointers 
    RF_next_fr[(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] = sp_fr - 1;
    RF_next_to[(S + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] = sp_to + 1;

    // Indexing Register File entery to find the right value
    for(int i = 0; i < S; i++) begin
        if(i == (sp_fr - 1)) begin
            data_fr = only_data_a[(i + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)];
            // Deleting the accessed ring
            RF_next_fr[(i + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] = 0;
        end
        if(i == (sp_to - 1)) begin
            data_to = only_data_b[(i + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)];  
        end
    end
    
    // Writing of the new ring to the destination
    for(int i = 0; i < S; i++) begin
        if(i == sp_to) RF_next_to[(i + 1) * $clog2(S + 1) - 1 -: $clog2(S + 1)] = data_fr;
    end
   
   wdata_a = RF_next_fr;
   wdata_b = RF_next_to;
    
end

// Implementation of Registers
always_ff@(posedge clk) begin
    if(rst) begin
        write_en_reg <= 0;
    end
    else begin
        write_en_reg <= write_en_next;
    end
end

endmodule
