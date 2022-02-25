`timescale 1ns / 1ps

module Cache_Ctrl
    #(
        parameter index_width = 10,
        parameter tag_width = 16
    )
    (
        input logic clk_i,
        input logic rst_i,
        input logic [index_width - 1 : 0] index_i,
        input logic [tag_width - 1 : 0] tag_i,
        input logic it_valid_i,
        input logic hm_ready_i,
        output logic it_ready_o,
        output logic hm_valid_o,
        output logic hit_miss_o,
        output logic [1 : 0] col_o
    );

// FSM states
typedef enum logic[1 : 0] {IDLE, CHECK, FINISH} fsm_state;
fsm_state next_state, current_state;

// Registers
logic [3 : 0] comp_reg, comp_next;
logic [tag_width - 1 : 0] tag_reg, tag_next;
logic [index_width - 1 : 0] index_reg, index_next;

// Tag and LRU memory
logic [4 * tag_width - 1 : 0] tag_data;
logic [15 : 0] lru_data;
logic [index_width - 1 : 0] waddr;
logic write_en;
logic [15 : 0] wdata;

// Mux
logic [index_width - 1 : 0] mux; 
logic sel;

// Comparators
logic [3 : 0] comp;

// Or gate
logic or_gate;

// Encoder
logic [1 : 0] dec;
logic dec_valid;

// LRU
logic [3 : 0] matrix0 [4];
logic [3 : 0] matrix1 [4];
logic [3 : 0] state_matrix [4]; // ##### Ovo treba negde držati #####
logic [3 : 0] result_matrix [4];

// Concurrent assigments
assign or_gate = ((comp_reg[0] | comp_reg[1]) | (comp_reg[2] | comp_reg[3]));
assign col_o = dec;
assign hit_miss_o = or_gate;
assign waddr = index_reg;

// Registers
always_ff@(posedge clk_i) begin
    if(rst_i == 1) begin
        comp_reg <= 0;
        tag_reg <= 0;
        index_reg <= 0;
    end
    else begin
        comp_reg <= comp_next;
        tag_reg <= tag_next;
        index_reg <= index_next;
    end
end

// MUX
always_comb begin
    if(sel) mux = index_i;
    else mux = index_reg;
end

// Tag memory implementation
Memory #(.addr_width(index_width), .data_width(4 * tag_width), .init_zero(0)) 
    Tag_Memory(
               .clk(clk_i), 
               .write_en(0), 
               .raddr(index_i), 
               .waddr(0), 
               .wdata(0), 
               .rdata(tag_data));
               
// LRU memory
Memory #(.addr_width(index_width), .data_width(16), .init_zero(1)) 
    LRU_Memory(
               .clk(clk_i), 
               .write_en(write_en), 
               .raddr(mux),
               .waddr(index_reg), 
               .wdata(wdata), 
               .rdata(lru_data));               

// Comparators
always_comb begin
    for(int i = 0; i < 4; i++) begin
        comp[i] = (tag_reg == tag_data[(i + 1) * tag_width - 1 -: tag_width]);
    end
end

// Encoder
always_comb begin
    dec = 0;
    dec_valid = 0;
    for(int i = 3; i >= 0; i--) begin
        if(comp_reg[i]) begin
            dec = i;
            dec_valid = 1;
        end
    end
end

// LRU implementation
always_comb begin
    
    state_matrix[0] = lru_data[15 : 12];
    state_matrix[1] = lru_data[11 : 8];
    state_matrix[2] = lru_data[7 : 4];
    state_matrix[3] = lru_data[3 : 0];

    for(int i = 0; i < 4; i++) begin
        for(int j = 0; j < 4; j++) begin
            matrix0[i][j] = ~comp_reg[j];
            matrix1[i][j] = comp_reg[3 - i];
            result_matrix[i][j] = (state_matrix[i][j] | matrix1[i][j]) & matrix0[i][j];
        end
    end
    
    wdata = {result_matrix[0], result_matrix[1], result_matrix[2], result_matrix[3]};
    
end

// FSM storage elements
always_ff@(posedge clk_i) begin
    if(rst_i == 1) begin
        current_state <= IDLE;
    end
    else begin
        current_state <= next_state;
    end
end

// FSM combinational logic
always_comb begin

    it_ready_o = 0;
    hm_valid_o = 0;
    comp_next = comp_reg;
    tag_next = tag_reg;
    index_next = index_reg;
    write_en = 0;
    sel = 0;

    case(current_state)
        IDLE: begin
            sel = 1;
            it_ready_o = 1;
            next_state = IDLE;
            if(it_valid_i) begin
                next_state = CHECK;
                tag_next = tag_i;
                index_next = index_i;
            end
        end
        CHECK: begin
            next_state = FINISH;
            comp_next = comp;
        end
        FINISH: begin
            hm_valid_o = 1;
            write_en = 1;
            next_state = (hm_ready_i == 1) ? IDLE : FINISH;
        end
        default: begin
            next_state = IDLE;
        end
    endcase
end
    
endmodule
