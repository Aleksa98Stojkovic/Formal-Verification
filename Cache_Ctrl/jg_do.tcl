analyze -sv09 Cache_Ctrl.sv Memory.sv
elaborate -top {Cache_Ctrl.sv}
clock clk
reset rst
prove -bg -all