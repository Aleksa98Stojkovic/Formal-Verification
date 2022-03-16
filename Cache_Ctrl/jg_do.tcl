clear -all
#set_elaborate_single_run_mode off
analyze -sv09 Cache_Ctrl.sv Memory.sv
elaborate -top {Cache_Ctrl}
#elaborate -bbox_a {0}
#elaborate -bbox_a {1}
clock clk_i
reset rst_i
prove -bg -all
