`timescale 1ns / 1ps

module top_module #
(
    parameter integer C_M_AXIS_TDATA_WIDTH = 0,

    parameter integer C_M_START_COUNT	= 32,

    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1,
    // arbitration type: "PRIORITY" or "ROUND_ROBIN"
    parameter ARB_TYPE = "PRIORITY",
    // LSB priority: "LOW", "HIGH"
    parameter LSB_PRIORITY = "HIGH",
    parameter integer C_S_AXIS_TDATA_WIDTH	= 32
)
(
    input wire clk,
    input wire rst,
    output wire input_0_tdata,
    output wire input_0_tvalid,
    output wire input_0_tlast,
    output wire input_0_tready,

    output wire input_1_tdata,
    output wire input_1_tvalid,
    output wire input_1_tlast,
    output wire input_1_tready,

    output wire input_2_tdata,
    output wire input_2_tvalid,
    output wire input_2_tlast,
    output wire input_2_tready,

    output wire input_3_tdata,
    output wire input_3_tvalid,
    output wire input_3_tlast,
    output wire input_3_tready,

    output wire output_tdata,
    output wire output_tready,
    output wire output_tvalid,
    output wire output_tlast

);

AXIS_master #(
    .C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
    .C_M_START_COUNT(C_M_START_COUNT)
)
axis_master_0 (
    .M_AXIS_ACLK(clk),
    .M_AXIS_ARESETN(rst),
    .M_AXIS_TVALID(input_0_tvalid),
    .M_AXIS_TDATA(input_0_tdata),
    .M_AXIS_TLAST(input_0_tlast),
    .M_AXIS_TREADY(input_0_tready)
);

AXIS_master #(
    .C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
    .C_M_START_COUNT(C_M_START_COUNT)
)
axis_master_1 (
    .M_AXIS_ACLK(clk),
    .M_AXIS_ARESETN(rst),
    .M_AXIS_TVALID(input_1_tvalid),
    .M_AXIS_TDATA(input_1_tdata),
    .M_AXIS_TLAST(input_1_tlast),
    .M_AXIS_TREADY(input_1_tready)
);

AXIS_master #(
    .C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
    .C_M_START_COUNT(C_M_START_COUNT)
)
axis_master_2 (
    .M_AXIS_ACLK(clk),
    .M_AXIS_ARESETN(rst),
    .M_AXIS_TVALID(input_2_tvalid),
    .M_AXIS_TDATA(input_2_tdata),
    .M_AXIS_TLAST(input_2_tlast),
    .M_AXIS_TREADY(input_2_tready)
);

AXIS_master #(
    .C_M_AXIS_TDATA_WIDTH(C_M_AXIS_TDATA_WIDTH),
    .C_M_START_COUNT(C_M_START_COUNT)
)
axis_master_3 (
    .M_AXIS_ACLK(clk),
    .M_AXIS_ARESETN(rst),
    .M_AXIS_TVALID(input_3_tvalid),
    .M_AXIS_TDATA(input_3_tdata),
    .M_AXIS_TLAST(input_3_tlast),
    .M_AXIS_TREADY(input_3_tready)
);

axis_arb_mux_4 #(
    .DATA_WIDTH(DATA_WIDTH),
    .KEEP_ENABLE(KEEP_ENABLE),
    .KEEP_WIDTH(KEEP_WIDTH),
    .ID_ENABLE(ID_ENABLE),
    .ID_WIDTH(ID_WIDTH),
    .DEST_ENABLE(DEST_ENABLE),
    .DEST_WIDTH(DEST_WIDTH),
    .USER_ENABLE(USER_ENABLE),
    .USER_WIDTH(USER_WIDTH),
    .ARB_TYPE(ARB_TYPE),
    .LSB_PRIORITY(LSB_PRIORITY)
)
(
    .clk(clk),
    .rst(rst),
    .input_0_axis_tdata(input_0_tdata),
    .input_0_axis_tvalid(input_0_tvalid),
    .input_0_axis_tready(input_0_tready),
    .input_0_axis_tlast(input_0_tlast),

    .input_1_axis_tdata(input_1_tdata),
    .input_1_axis_tvalid(input_1_tvalid),
    .input_1_axis_tready(input_1_tready),
    .input_1_axis_tlast(input_1_tlast),

    .input_2_axis_tdata(input_2_tdata),
    .input_2_axis_tvalid(input_2_tvalid),
    .input_2_axis_tready(input_2_tready),
    .input_2_axis_tlast(input_2_tlast),

    .input_3_axis_tdata(input_3_tdata),
    .input_3_axis_tvalid(input_3_tvalid),
    .input_3_axis_tready(input_3_tready),
    .input_3_axis_tlast(input_3_tlast),   

    .output_axis_tdata(output_tdata),
    .output_axis_tvalid(output_tvalid),
    .output_axis_tready(output_tready),
    .output_axis_tlast(output_tlast) 

);

AXIS_slave # 
(
    .C_S_AXIS_TDATA_WIDTH(C_S_AXIS_TDATA_WIDTH)
)
(
    .S_AXIS_ACLK(clk),
    .S_AXIS_ARESETN(.rst),
    .S_AXIS_TREADY(output_tready),
    .S_AXIS_TDATA(output_tdata),
    .S_AXIS_TLAST(output_tlast),
    .S_AXIS_TVALID(output_tvalid)
);
 
endmodule
