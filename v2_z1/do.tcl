analyze -vhdl2k Circuit_v2_p1.vhd lut3.vhd
analyze -sv09 top.sv
elaborate -top {top}
clock clk
reset rst
prove -bg -all
