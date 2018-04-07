/*

Copyright (c) 2016-2018 Alex Forencich

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

*/

// Language: Verilog 2001

`timescale 1ns / 1ps

/*
 * AXI4-Stream 4x4 switch
 */
module verif_axis_switch_4x4 #
(
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_WIDTH = 2,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1,
    parameter OUT_0_BASE = 0,
    parameter OUT_0_TOP = 0,
    parameter OUT_0_CONNECT = 4'b1111,
    parameter OUT_1_BASE = 1,
    parameter OUT_1_TOP = 1,
    parameter OUT_1_CONNECT = 4'b1111,
    parameter OUT_2_BASE = 2,
    parameter OUT_2_TOP = 2,
    parameter OUT_2_CONNECT = 4'b1111,
    parameter OUT_3_BASE = 3,
    parameter OUT_3_TOP = 3,
    parameter OUT_3_CONNECT = 4'b1111,
    // arbitration type: "PRIORITY" or "ROUND_ROBIN"
    parameter ARB_TYPE = "ROUND_ROBIN",
    // LSB priority: "LOW", "HIGH"
    parameter LSB_PRIORITY = "HIGH"
)
(
    input  wire        clk,
    input  wire        rst,

    /*
     * AXI Stream inputs
     */
    input  wire [DATA_WIDTH-1:0]  input_0_axis_tdata,
    input  wire                   input_0_axis_tvalid,
    output wire                   input_0_axis_tready,
    input  wire                   input_0_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_1_axis_tdata,
    input  wire                   input_1_axis_tvalid,
    output wire                   input_1_axis_tready,
    input  wire                   input_1_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_2_axis_tdata,
    input  wire                   input_2_axis_tvalid,
    output wire                   input_2_axis_tready,
    input  wire                   input_2_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_3_axis_tdata,
    input  wire                   input_3_axis_tvalid,
    output wire                   input_3_axis_tready,
    input  wire                   input_3_axis_tlast,

    /*
     * AXI Stream outputs
     */
    output wire [DATA_WIDTH-1:0]  output_0_axis_tdata,
    output wire                   output_0_axis_tvalid,
    input  wire                   output_0_axis_tready,
    output wire                   output_0_axis_tlast,

    output wire [DATA_WIDTH-1:0]  output_1_axis_tdata,
    output wire                   output_1_axis_tvalid,
    input  wire                   output_1_axis_tready,
    output wire                   output_1_axis_tlast,

    output wire [DATA_WIDTH-1:0]  output_2_axis_tdata,
    output wire                   output_2_axis_tvalid,
    input  wire                   output_2_axis_tready,
    output wire                   output_2_axis_tlast,


    output wire [DATA_WIDTH-1:0]  output_3_axis_tdata,
    output wire                   output_3_axis_tvalid,
    input  wire                   output_3_axis_tready,
    output wire                   output_3_axis_tlast
);

	module Wrapper;
	
	bind axis_switch_4x4 verif_axis_switch_4x4 # ( 
	
	.DATA_WIDTH(DATA_WIDTH),
    .KEEP_ENABLE(KEEP_ENABLE),
    .KEEP_WIDTH(KEEP_WIDTH),
    .ID_ENABLE(ID_ENABLE),
    .ID_WIDTH(ID_WIDTH),
    .DEST_WIDTH(DEST_WIDTH),
    .USER_ENABLE(USER_ENABLE),
    .USER_WIDTH(USER_WIDTH),
    .OUT_0_BASE(OUT_0_BASE),
    .OUT_0_TOP(OUT_0_TOP),
    .OUT_0_CONNECT(OUT_0_CONNECT),
    .OUT_1_BASE(OUT_1_BASE),
    .OUT_1_TOP(OUT_1_TOP),
    .OUT_1_CONNECT(OUT_1_CONNECT),
    .OUT_2_BASE(OUT_2_BASE),
    .OUT_2_TOP(OUT_2_TOP),
    .OUT_2_CONNECT(OUT_2_CONNECT),
    .OUT_3_BASE(OUT_3_BASE),
    .OUT_3_TOP(OUT_3_TOP),
    .OUT_3_CONNECT(OUT_3_CONNECT),
    .ARB_TYPE(ARB_TYPE),
    .LSB_PRIORITY(LSB_PRIORITY)
	)verif_axis_switch_4x4_inst (
		.clk(clk),
		.rst(rst),

    /*
     * AXI Stream inputs
     */
    .input_0_axis_tdata(input_0_axis_tdata),
    .input_0_axis_tvalid(input_0_axis_tvalid),
    .input_0_axis_tready(input_0_axis_tready),
    .input_0_axis_tlast(input_0_axis_tlast),

    .input_1_axis_tdata(input_1_axis_tdata),
	.input_1_axis_tvalid(input_1_axis_tvalid),
    .input_1_axis_tready(input_1_axis_tready),
    .input_1_axis_tlast(input_1_axis_tlast),

    .input_2_axis_tdata(input_2_axis_tdata),
    .input_2_axis_tvalid(input_2_axis_tvalid),
    .input_2_axis_tready(input_2_axis_tready),
    .input_2_axis_tlast(input_2_axis_tlast),

    .input_3_axis_tdata(input_3_axis_tdata),
    .input_3_axis_tvalid(input_3_axis_tvalid),
	.input_3_axis_tready(input_3_axis_tready),
    .input_3_axis_tlast(input_3_axis_tlast),


    /*
     * AXI Stream outputs
     */
    .output_0_axis_tdata(output_0_axis_tdata),
    .output_0_axis_tvalid(output_0_axis_tvalid),
    .output_0_axis_tready(output_0_axis_tready),
	.output_0_axis_tlast(output_0_axis_tlast),

    .output_1_axis_tdata(output_1_axis_tdata),
    .output_1_axis_tvalid(output_1_axis_tvalid),
    .output_1_axis_tready(output_1_axis_tready),
    .output_1_axis_tlast(output_1_axis_tlast),

    .output_2_axis_tdata(output_2_axis_tdata),
    .output_2_axis_tvalid(output_2_axis_tvalid),
    .output_2_axis_tready(output_2_axis_tready),
    .output_2_axis_tlast(output_2_axis_tlast),

    .output_3_axis_tdata(output_3_axis_tdata),
    .output_3_axis_tvalid(output_3_axis_tvalid),
    .output_3_axis_tready(output_3_axis_tready),
    .output_3_axis_tlast(output_3_axis_tlast)
	);
	
	endmodule

endmodule
