
`timescale 1 ns / 1 ps

	module AXIS_slave_props #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Slave Bus Interface S00_AXIS
		parameter integer C_S00_AXIS_TDATA_WIDTH	= 32
	)
	(
		// Users to add ports here

		// User ports ends
		// Do not modify the ports beyond this line


		// Ports of Axi Slave Bus Interface S00_AXIS
		input wire  s00_axis_aclk,
		input wire  s00_axis_aresetn,
		input wire  s00_axis_tready,
		input wire [C_S00_AXIS_TDATA_WIDTH-1 : 0] s00_axis_tdata,
		input wire [(C_S00_AXIS_TDATA_WIDTH/8)-1 : 0] s00_axis_tstrb,
		input wire  s00_axis_tlast,
		input wire  s00_axis_tvalid
	);

	// Add user logic here
	// AXI4STREAM_ERRM_TVALID_RESET: assert property (
		// @(posedge s00_axis_aclk) $rose(s00_axis_aresetn) |-> s00_axis_tvalid == 0
	// );
	
	// property stable_value(signal, condition);
		// @(posedge s00_axis_aclk) disable iff (~s00_axis_aresetn | ~condition) 
			// //$stable(signal) throughout  ($rose(condition) ##[1:$] $fell(condition));
			// condition |=> ##1 (signal == $past(signal,1));
	// endproperty
	
	property x_not_permit_rst(signal);
		@(posedge s00_axis_aclk) s00_axis_aresetn |-> ~$isunknown(signal);
	endproperty
	
	AXI4STREAM_ERRS_TREADY_X: assert property (x_not_permit_rst(s00_axis_tready));
	// User logic ends

	endmodule

	
	module Wrapper;
	// Instantiation of Axi Bus Interface S00_AXIS
	bind AXIS_slave AXIS_slave_props # ( 
		.C_S00_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH)
	) AXIS_slave_props_inst (
		.s00_axis_aclk(S_AXIS_ACLK),
		.s00_axis_aresetn(S_AXIS_ARESETN),
		.s00_axis_tready(S_AXIS_TREADY),
		.s00_axis_tdata(S_AXIS_TDATA),
		.s00_axis_tstrb(S_AXIS_TSTRB),
		.s00_axis_tlast(S_AXIS_TLAST),
		.s00_axis_tvalid(S_AXIS_TVALID)
	);
	
	endmodule