analyze -sv09 V1_Z2.sv
elaborate -V1_Z2 {V1_Z2}
clock clk
reset rst
prove -bg -all
