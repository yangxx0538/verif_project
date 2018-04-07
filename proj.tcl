#Tcl script which can be used with JasperGold
#Use "source lab4.tcl" in the console to source this script

# #Reading the files 
# analyze -v2k {AXIS_master.v};
# analyze -sv {verif_AXIS_master.sv};

# #Elaborating the design
# elaborate -top {AXIS_master};

# #You will need to add commands below

# #Set the clock
# clock -clear; clock M_AXIS_ACLK

# #Set Reset
# reset -expression {~M_AXIS_ARESETN};

# #Prove all
# prove -bg -all


##################################################################################
# analyze -v2k {AXIS_slave.v};
# analyze -sv {verif_AXIS_slave.sv};

# #Elaborating the design
# elaborate -top {AXIS_slave};

# #You will need to add commands below

# #Set the clock
# clock -clear; clock S_AXIS_ACLK

# #Set Reset
# reset -expression {~S_AXIS_ARESETN};

# #Prove all
# prove -bg -all

#############################################################################

# analyze -v2k {arbiter.v priority_encoder.v axis_switch_4x4.v};
# analyze -sv {verif_axis_switch_4x4.sv};

# #Elaborating the design
# elaborate -top {axis_switch_4x4} -bbox_m {priority_encoder};

# #You will need to add commands below

# #Set the clock
# clock -clear; clock clk

# #Set Reset
# reset -expression {rst};

# #Prove all
# prove -bg -all

####################################################################

# analyze -v2k {arbiter.v priority_encoder.v axis_arb_mux_4.v axis_mux_4.v};
# analyze -sv {verif_axis_arb_mux_4.sv};

# #Elaborating the design
# elaborate -top {axis_arb_mux_4}; #-bbox_m {priority_encoder};

# #You will need to add commands below

# #Set the clock
# clock -clear; clock clk

# #Set Reset
# reset -expression {rst};

# #Prove all
# prove -bg -all

#################################################################3
analyze -v2k {priority_encoder.v};
analyze -sv {verif_priority_encoder.sv};

#Elaborating the design
elaborate -top {priority_encoder}; #-bbox_m {priority_encoder};

#You will need to add commands below

#Set the clock
#clock -clear; clock clk

#Set Reset
#reset -expression {rst};

#Prove all
prove -bg -all

