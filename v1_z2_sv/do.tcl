analyze -sv09 V1_Z2.sv
elaborate -top {V1_Z2}
clock clk
reset rst
prove -bg -all
