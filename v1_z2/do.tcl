analyze -vhdl2k Circuit_v1_p2.vhd generic_dec.vhd
analyze -sv09 top.sv
elaborate -top {top}
clock clk_i
reset rst_i
prove -bg -all
