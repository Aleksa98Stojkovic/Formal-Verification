analyze -vhdl2k Circuit_v2_p2.vhd Generic_LUT.vhd
analyze -sv09 top.sv
elaborate -top {top}
clock clk_i
reset rst_i
prove -bg -all
