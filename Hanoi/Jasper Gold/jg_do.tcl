clear -all
analyze -sv09 Hanoi.sv
elaborate -top Hanoi
clock clk
reset rst
prove -all
