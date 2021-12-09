analyze -sv09 V2_Z2.sv LUT.sv
elaborate -top {V2_Z2}
clock clk
reset rst
prove -bg -all
