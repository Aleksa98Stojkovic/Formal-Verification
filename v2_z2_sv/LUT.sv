`timescale 1ns / 1ps

module LUT
    #(
        parameter logic [15 : 0] I = 0
    )
    (
        input logic [3 : 0] lut_i,
        output logic lut_o
        
    );
    
// assign lut_o = I[lut_i];
     
always_comb begin
    case(lut_i)
        0 :
            lut_o = I[0]; 
        1 :
            lut_o = I[1];
        2 :
            lut_o = I[2];
        3 :  
            lut_o = I[3];
        4 :
            lut_o = I[4]; 
        5 :
            lut_o = I[5];
        6 :
            lut_o = I[6];
        7 :  
            lut_o = I[7];
        8 :
            lut_o = I[8]; 
        9 :
            lut_o = I[9];
        10 :
            lut_o = I[10];
        11 :  
            lut_o = I[11];
        12 :
            lut_o = I[12]; 
        13 :
            lut_o = I[13];
        14 :
            lut_o = I[14];
        15 :  
            lut_o = I[15];
    endcase
end
    
endmodule
