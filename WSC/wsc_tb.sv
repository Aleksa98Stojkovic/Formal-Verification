`timescale 1ns / 1ps

module wsc_tb();

typedef logic [10 : 0] table_type [0 : 15];

function logic check_state(input logic [3 : 0] state);

    logic t, w, s, c, pass;
    t = state[3];
    w = state[2];
    s = state[1];
    c = state[0];
    
    pass = 1;
    if((w == s) && (t != w)) pass = 0;
    if((s == c) && (t != c)) pass = 0;
    
    return pass;

endfunction

function table_type init_lookup();

    table_type lookup;
    logic [3 : 0] state;
    logic [2 : 0] base;

    for(int i = 0; i < 16; i++) begin
       state = i;
       lookup[i] = 0;
       base = 3'b100;
       if(check_state(state)) begin
            logic [1 : 0] count;
            count = 0;
            for(int j = 0; j < 4; j++) begin
                logic [2 : 0] wsc;
                logic [3 : 0] new_state;
                wsc = base >> j;
                
                new_state[3] = !state[3];
                new_state[2] = (wsc[2] == 1) ? !state[2] : state[2];
                new_state[1] = (wsc[1] == 1) ? !state[1] : state[1];
                new_state[0] = (wsc[0] == 1) ? !state[0] : state[0];
                
                if(check_state(new_state)) begin
                    lookup[i][10 - 3 * count -: 3] = wsc;
                    count++;
                end
            end
            
            lookup[i][1 : 0] = count;
            
       end
    end
    
    return lookup;

endfunction


function logic [2 : 0] generate_input(input logic [10 : 0] lookup_line);
    
    logic [1 : 0] options;
    int index;
    
    options = lookup_line[1 : 0];
    index = $urandom_range(int'(options - 1));
    $display("Value of index %d in time %d\n", index, $time);
    $display("Value of lookup_line %d in time %d\n", lookup_line, $time);
    
    return lookup_line[10 - index * 3 -: 3];
    
endfunction

logic clk_s, rst_s;
logic [2 : 0] wsc;
logic [3 : 0] state_s;
logic fail, hit;
int seed = 0;
table_type lookup = init_lookup();

wsc wsc_inst
  ( .clk(clk_s),
    .rst(rst_s),
    .wolf(wsc[2]),
    .sheep(wsc[1]),
    .cab(wsc[0]),
    .state(state_s));
    
always begin
    #10ns clk_s = !clk_s;
end

// reset block
initial begin
    clk_s = 0;
    rst_s = 1;
    #15ns rst_s = 0;
end 

assign fail = !check_state(state_s);
assign hit = (state_s == 15) & !fail;


assign wsc = generate_input(lookup[state_s]);


endmodule
