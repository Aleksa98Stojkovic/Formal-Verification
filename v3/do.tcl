analyze -vhdl z1.vhd
analyze -sv09 top.sv
elaborate -top {top}
clock clk
reset rst
prove -bg -all
