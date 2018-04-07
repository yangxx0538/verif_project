
`timescale 1 ns / 1 ps

	module AXIS_master_props #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 32,
		parameter integer C_M00_AXIS_START_COUNT	= 32
	)
	(
		// Users to add ports here
		// input   [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0] M_AXIS_TKEEP,
		// input   [M_AXIS_TID_WIDTH-1:0] M_AXIS_TID,
		// input   [M_AXIS_TDEST_WIDTH-1:0] M_AXIS_TDEST,
		// input   [C_M_AXIS_TDATA_WIDTH-1:0] M_AXIS_TUSER
		// User ports ends
		// Do not modify the ports beyond this line


		// Ports of Axi Master Bus Interface M00_AXIS
		input wire  m00_axis_aclk,
		input wire  m00_axis_aresetn,
		input wire  m00_axis_tvalid,
		input wire [ (C_M00_AXIS_TDATA_WIDTH-1 >=0 ? C_M00_AXIS_TDATA_WIDTH-1 : 0) : 0] m00_axis_tdata,
		input wire [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		input wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);


	// Add user logic here property for verification
	
	
	
	AXI4STREAM_ERRM_TVALID_RESET: assert property (
		@(posedge m00_axis_aclk) $rose(m00_axis_aresetn) |-> m00_axis_tvalid == 0
	);
	
	property stable_value(signal, condition);
		@(posedge m00_axis_aclk) disable iff (~m00_axis_aresetn | ~condition) 
			//$stable(signal) throughout  ($rose(condition) ##[1:$] $fell(condition));
			condition |=> ##1 (signal == $past(signal,1));
	endproperty
	// AXI4STREAM_ERRM_TID_STABLE:   assert property (stable_value(M_AXIS_TID));
	// AXI4STREAM_ERRM_TDEST_STABLE: assert property (stable_value(M_AXIS_TDEST));
	// AXI4STREAM_ERRM_TUSER_STABLE: assert property (stable_value(M_AXIS_TUSER));
	AXI4STREAM_ERRM_TDATA_STABLE: assert property (stable_value(m00_axis_tdata, m00_axis_tvalid && ~m00_axis_tready));
	AXI4STREAM_ERRM_TSTRB_STABLE: assert property (stable_value(m00_axis_tstrb, m00_axis_tvalid && ~m00_axis_tready));
	AXI4STREAM_ERRM_TLAST_STABLE: assert property (stable_value(m00_axis_tlast, m00_axis_tvalid && ~m00_axis_tready));
	// AXI4STREAM_ERRM_TKEEP_STABLE: assert property (stable_value(M_AXIS_TKEEP));
	AXI4STREAM_ERRM_TVALID_STABLE: assert property (stable_value(m00_axis_tvalid, m00_axis_tvalid && ~m00_axis_tready));

	
	property x_not_permit(signal);
		@(posedge m00_axis_aclk) disable iff (~m00_axis_aresetn) m00_axis_tvalid |-> ~$isunknown(signal);
	endproperty
	//AXI4STREAM_ERRM_TID_X:   assert property (x_not_permit(M_AXIS_TID));
	//AXI4STREAM_ERRM_TDEST_X: assert property (x_not_permit(M_AXIS_TDEST));
	AXI4STREAM_ERRM_TDATA_X: assert property (x_not_permit(m00_axis_tdata));
	AXI4STREAM_ERRM_TSTRB_X: assert property (x_not_permit(m00_axis_tstrb));
	AXI4STREAM_ERRM_TLAST_X: assert property (x_not_permit(m00_axis_tlast));
	// AXI4STREAM_ERRM_TKEEP_X: assert property (x_not_permit(M_AXIS_TKEEP));
	property x_not_permit_rst(signal);
		@(posedge m00_axis_aclk) m00_axis_aresetn |-> ~$isunknown(signal);
	endproperty
	AXI4STREAM_ERRM_TVALID_X: assert property (x_not_permit_rst(m00_axis_tvalid));
	AXI4STREAM_ERRS_TREADY_X: assert property (x_not_permit_rst(m00_axis_tready));
	// AXI4STREAM_ERRM_TUSER_X:  assert property (x_not_permit_rst(M_AXIS_TUSER));
	
	//AXI4STREAM_ERRM_STREAM_ALL_DONE_EOS: 
	
	// AXI4STREAM_ERRM_TKEEP_TSTRB: assert property (
		// @(posedge m00_axis_aclk) disable iff (~m00_axis_aresetn) ~M_AXIS_TKEEP |-> ~m00_axis_tstrb
	// );
	property set_to_zero (condition, signal);
		@(posedge m00_axis_aclk) disable iff (~m00_axis_aresetn) condition == 0 |-> signal == 0;
	endproperty
	AXI4STREAM_ERRM_TDATA_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,m00_axis_tdata));
	// AXI4STREAM_ERRM_TKEEP_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,M_AXIS_TKEEP));
	AXI4STREAM_ERRM_TSTRB_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,m00_axis_tstrb));
	// AXI4STREAM_ERRM_TUSER_TIEOFF: assert property(set_to_zero(C_M_AXIS_TDATA_WIDTH,M_AXIS_TUSER));
	// AXI4STREAM_ERRM_TID_TIEOFF: assert property(set_to_zero(M_AXIS_TID_WIDTH,M_AXIS_TID));
	// AXI4STREAM_ERRM_TDEST_TIEOFF: assert property(set_to_zero(M_AXIS_TDEST_WIDTH,M_AXIS_TDEST));
	
	// AXI4STREAM_AUXM_TID_TDTEST_WIDTH: assert property(
		// @(posedge m00_axis_aclk) (M_AXIS_TID_WIDTH + M_AXIS_TDEST_WIDTH) <= 24
	// );
	
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tvalid)
	);
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tready)
	);
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tlast)
	);
	cover property (
		@(posedge m00_axis_aclk) m00_axis_tready && m00_axis_tvalid
	);
	
	// User logic ends

	endmodule
	
	module AXIS_master_props_0 #
	(
		// Users to add parameters here

		// User parameters ends
		// Do not modify the parameters beyond this line


		// Parameters of Axi Master Bus Interface M00_AXIS
		parameter integer C_M00_AXIS_TDATA_WIDTH	= 0,
		parameter integer C_M00_AXIS_START_COUNT	= 32
	)
	(
		// Users to add ports here
		// input   [(C_M_AXIS_TDATA_WIDTH/8)-1 : 0] M_AXIS_TKEEP,
		// input   [M_AXIS_TID_WIDTH-1:0] M_AXIS_TID,
		// input   [M_AXIS_TDEST_WIDTH-1:0] M_AXIS_TDEST,
		// input   [C_M_AXIS_TDATA_WIDTH-1:0] M_AXIS_TUSER
		// User ports ends
		// Do not modify the ports beyond this line


		// Ports of Axi Master Bus Interface M00_AXIS
		input wire  m00_axis_aclk,
		input wire  m00_axis_aresetn,
		input wire  m00_axis_tvalid,
		input wire [ (C_M00_AXIS_TDATA_WIDTH-1 >=0 ? C_M00_AXIS_TDATA_WIDTH-1 : 0) : 0] m00_axis_tdata,
		input wire [(C_M00_AXIS_TDATA_WIDTH/8)-1 : 0] m00_axis_tstrb,
		input wire  m00_axis_tlast,
		input wire  m00_axis_tready
	);


	// Add user logic here property for verification

	property set_to_zero (condition, signal);
		@(posedge m00_axis_aclk) disable iff (~m00_axis_aresetn) condition == 0 |-> signal == 0;
	endproperty
	AXI4STREAM_ERRM_TDATA_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,m00_axis_tdata));
	// AXI4STREAM_ERRM_TKEEP_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,M_AXIS_TKEEP));
	AXI4STREAM_ERRM_TSTRB_TIEOFF: assert property(set_to_zero(C_M00_AXIS_TDATA_WIDTH,m00_axis_tstrb));
	// AXI4STREAM_ERRM_TUSER_TIEOFF: assert property(set_to_zero(C_M_AXIS_TDATA_WIDTH,M_AXIS_TUSER));
	// AXI4STREAM_ERRM_TID_TIEOFF: assert property(set_to_zero(M_AXIS_TID_WIDTH,M_AXIS_TID));
	// AXI4STREAM_ERRM_TDEST_TIEOFF: assert property(set_to_zero(M_AXIS_TDEST_WIDTH,M_AXIS_TDEST));
	
	// AXI4STREAM_AUXM_TID_TDTEST_WIDTH: assert property(
		// @(posedge m00_axis_aclk) (M_AXIS_TID_WIDTH + M_AXIS_TDEST_WIDTH) <= 24
	// );
	
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tvalid)
	);
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tready)
	);
	cover property (
		@(posedge m00_axis_aclk) $rose(m00_axis_tlast)
	);
	cover property (
		@(posedge m00_axis_aclk) m00_axis_tready && m00_axis_tvalid
	);
	
	// User logic ends

	endmodule
	
	
	module Wrapper;
	
	bind AXIS_master AXIS_master_props # ( 
		.C_M00_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
		.C_M00_AXIS_START_COUNT(C_M_START_COUNT)
	)AXIS_master_props_inst (
		.m00_axis_aclk(M_AXIS_ACLK),
		.m00_axis_aresetn(M_AXIS_ARESETN),
		.m00_axis_tvalid(M_AXIS_TVALID),
		.m00_axis_tdata(M_AXIS_TDATA),
		.m00_axis_tstrb(M_AXIS_TSTRB),
		.m00_axis_tlast(M_AXIS_TLAST),
		.m00_axis_tready(M_AXIS_TREADY)
	);
	
	bind AXIS_master AXIS_master_props_0 # ( 
		.C_M00_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
		.C_M00_AXIS_START_COUNT(C_M_START_COUNT)
	)AXIS_master_props_inst_0 (
		.m00_axis_aclk(M_AXIS_ACLK),
		.m00_axis_aresetn(M_AXIS_ARESETN),
		.m00_axis_tvalid(M_AXIS_TVALID),
		.m00_axis_tdata(M_AXIS_TDATA),
		.m00_axis_tstrb(M_AXIS_TSTRB),
		.m00_axis_tlast(M_AXIS_TLAST),
		.m00_axis_tready(M_AXIS_TREADY)
	);
	
	endmodule
