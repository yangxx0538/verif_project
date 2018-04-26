/*

Copyright (c) 2014-2018 Alex Forencich

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
 * Arbiter module
 */
 
 module verif_top_module #
(
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
    parameter LSB_PRIORITY = "HIGH"
)
(
    input wire clk,
    input wire rst,
    input wire [DATA_WIDTH-1:0] input_0_tdata,
    input wire input_0_tvalid,
    input wire input_0_tlast,
    input wire input_0_tready,

    input wire [DATA_WIDTH-1:0] input_1_tdata,
    input wire input_1_tvalid,
    input wire input_1_tlast,
    input wire input_1_tready,

    input wire [DATA_WIDTH-1:0] input_2_tdata,
    input wire input_2_tvalid,
    input wire input_2_tlast,
    input wire input_2_tready,

    input wire [DATA_WIDTH-1:0] input_3_tdata,
    input wire input_3_tvalid,
    input wire input_3_tlast,
    input wire input_3_tready,

    input wire [DATA_WIDTH-1:0] output_tdata,
    input wire output_tready,
    input wire output_tvalid,
    input wire output_tlast

);

// assume property(
	// @(posedge clk) disable iff (rst) input_0_tdata != $
// );


assert property(
	@(posedge clk) input_0_tready |-> (!input_1_tready & !input_2_tready & !input_3_tready)
);
assert property(
	@(posedge clk) input_1_tready |-> (!input_0_tready & !input_2_tready & !input_3_tready)
);
assert property(
	@(posedge clk) input_2_tready |-> (!input_1_tready & !input_0_tready & !input_3_tready)
);
assert property(
	@(posedge clk) input_3_tready |-> (!input_1_tready & !input_2_tready & !input_0_tready)
);

assert property (
	@(posedge clk) $fell(rst) |-> input_0_tvalid == 0 & input_1_tvalid == 0 & input_2_tvalid == 0 & input_3_tvalid == 0
);

sequence dat(t,out, in);
	##t out == $past(in,t-1);
endsequence
property check_sel_data_consistent (tvalid, tready, tlast, out_tvalid, out_data, in_data);
	@(posedge clk) disable iff (rst) tvalid & !(tvalid & tready & tlast) |-> dat(2, out_data, in_data) or dat(3, out_data, in_data) or dat(4, out_data, in_data);
endproperty
assert property (check_sel_data_consistent(input_0_tvalid, input_0_tready, input_0_tlast, output_tvalid, output_tdata, input_0_tdata));

//assert property (
//	@(posedge clk) disable iff (rst) input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_1_tdata) or dat(3, output_tdata, input_1_tdata) or dat(4, output_tdata, input_1_tdata)
//);
//assert property (
//	@(posedge clk) disable iff (rst) input_2_tvalid & !(input_2_tvalid & input_2_tready & input_2_tlast) & !(input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast)) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_2_tdata) or dat(3, output_tdata, input_2_tdata) or dat(4, output_tdata, input_2_tdata)
//);
// assert property (
	// @(posedge clk) disable iff (rst) input_3_tvalid & !(input_3_tvalid & input_3_tready & input_3_tlast) & !(input_2_tvalid & !(input_2_tvalid & input_2_tready & input_2_tlast)) & !(input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast)) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_3_tdata) or dat(3, output_tdata, input_3_tdata) or dat(4, output_tdata, input_3_tdata)
// );
cover property(
	@(posedge clk) disable iff(rst) $rose(output_tvalid)
);
cover property(
	@(posedge clk) disable iff(rst) $rose(output_tready)
);

endmodule

module verif_top_module1 #
(
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
    parameter LSB_PRIORITY = "HIGH"
)
(
    input wire clk,
    input wire rst,
    input wire [DATA_WIDTH-1:0] input_0_tdata,
    input wire input_0_tvalid,
    input wire input_0_tlast,
    input wire input_0_tready,

    input wire [DATA_WIDTH-1:0] input_1_tdata,
    input wire input_1_tvalid,
    input wire input_1_tlast,
    input wire input_1_tready,

    input wire [DATA_WIDTH-1:0] input_2_tdata,
    input wire input_2_tvalid,
    input wire input_2_tlast,
    input wire input_2_tready,

    input wire [DATA_WIDTH-1:0] input_3_tdata,
    input wire input_3_tvalid,
    input wire input_3_tlast,
    input wire input_3_tready,

    input wire [DATA_WIDTH-1:0] output_tdata,
    input wire output_tready,
    input wire output_tvalid,
    input wire output_tlast

);

sequence dat(t,out, in);
	##t out == $past(in,t-1);
endsequence

assert property (
	@(posedge clk) disable iff (rst) input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_1_tdata) or dat(3, output_tdata, input_1_tdata) or dat(4, output_tdata, input_1_tdata)
);

cover property(
	@(posedge clk) disable iff(rst) $rose(output_tvalid)
);
cover property(
	@(posedge clk) disable iff(rst) $rose(output_tready)
);

endmodule

module verif_top_module2 #
(
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
    parameter LSB_PRIORITY = "HIGH"
)
(
    input wire clk,
    input wire rst,
    input wire [DATA_WIDTH-1:0] input_0_tdata,
    input wire input_0_tvalid,
    input wire input_0_tlast,
    input wire input_0_tready,

    input wire [DATA_WIDTH-1:0] input_1_tdata,
    input wire input_1_tvalid,
    input wire input_1_tlast,
    input wire input_1_tready,

    input wire [DATA_WIDTH-1:0] input_2_tdata,
    input wire input_2_tvalid,
    input wire input_2_tlast,
    input wire input_2_tready,

    input wire [DATA_WIDTH-1:0] input_3_tdata,
    input wire input_3_tvalid,
    input wire input_3_tlast,
    input wire input_3_tready,

    input wire [DATA_WIDTH-1:0] output_tdata,
    input wire output_tready,
    input wire output_tvalid,
    input wire output_tlast

);

sequence dat(t,out, in);
	##t out == $past(in,t-1);
endsequence

assert property (
	@(posedge clk) disable iff (rst) input_2_tvalid & !(input_2_tvalid & input_2_tready & input_2_tlast) & !(input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast)) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_2_tdata) or dat(3, output_tdata, input_2_tdata) or dat(4, output_tdata, input_2_tdata)
);

cover property(
	@(posedge clk) disable iff(rst) $rose(output_tvalid)
);
cover property(
	@(posedge clk) disable iff(rst) $rose(output_tready)
);

endmodule


module verif_top_module3 #
(
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
    parameter LSB_PRIORITY = "HIGH"
)
(
    input wire clk,
    input wire rst,
    input wire [DATA_WIDTH-1:0] input_0_tdata,
    input wire input_0_tvalid,
    input wire input_0_tlast,
    input wire input_0_tready,

    input wire [DATA_WIDTH-1:0] input_1_tdata,
    input wire input_1_tvalid,
    input wire input_1_tlast,
    input wire input_1_tready,

    input wire [DATA_WIDTH-1:0] input_2_tdata,
    input wire input_2_tvalid,
    input wire input_2_tlast,
    input wire input_2_tready,

    input wire [DATA_WIDTH-1:0] input_3_tdata,
    input wire input_3_tvalid,
    input wire input_3_tlast,
    input wire input_3_tready,

    input wire [DATA_WIDTH-1:0] output_tdata,
    input wire output_tready,
    input wire output_tvalid,
    input wire output_tlast

);

sequence dat(t,out, in);
	##t out == $past(in,t-1);
endsequence

assert property (
	@(posedge clk) disable iff (rst) input_3_tvalid & !(input_3_tvalid & input_3_tready & input_3_tlast) & !(input_2_tvalid & !(input_2_tvalid & input_2_tready & input_2_tlast)) & !(input_1_tvalid & !(input_1_tvalid & input_1_tready & input_1_tlast)) & !(input_0_tvalid & !(input_0_tvalid & input_0_tready & input_0_tlast)) |-> dat(2, output_tdata, input_3_tdata) or dat(3, output_tdata, input_3_tdata) or dat(4, output_tdata, input_3_tdata)
);

cover property(
	@(posedge clk) disable iff(rst) $rose(output_tvalid)
);
cover property(
	@(posedge clk) disable iff(rst) $rose(output_tready)
);

endmodule


module Wrapper;
//change module number here below to verify 
bind top_module verif_top_module # (

    .C_M_START_COUNT(C_M_START_COUNT),
	.DATA_WIDTH(DATA_WIDTH),
    .KEEP_ENABLE(KEEP_ENABLE),
    .KEEP_WIDTH(KEEP_WIDTH),
    .ID_ENABLE(ID_ENABLE),
    .ID_WIDTH(ID_WIDTH),
    .DEST_ENABLE(DEST_ENABLE),
    .DEST_WIDTH(DEST_WIDTH),
    .USER_ENABLE(USER_ENABLE),
    .USER_WIDTH(USER_WIDTH),
    // arbitration type: "PRIORITY" or "ROUND_ROBIN"
    .ARB_TYPE(ARB_TYPE),
    // LSB priority: "LOW", "HIGH"
    .LSB_PRIORITY(LSB_PRIORITY)
)verif_top_module_inst (
	.clk(clk),
	.rst(rst),
	.input_0_tdata(input_0_tdata),
	.input_0_tvalid(input_0_tvalid),
	.input_0_tlast(input_0_tlast),
	.input_0_tready(input_0_tready),
	.input_1_tdata(input_1_tdata),
	.input_1_tvalid(input_1_tvalid),
	.input_1_tlast(input_1_tlast),
	.input_1_tready(input_1_tready),
	.input_2_tdata(input_2_tdata),
	.input_2_tvalid(input_2_tvalid),
	.input_2_tlast(input_2_tlast),
	.input_2_tready(input_2_tready),
	.input_3_tdata(input_3_tdata),
	.input_3_tvalid(input_3_tvalid),
	.input_3_tlast(input_3_tlast),
	.input_3_tready(input_3_tready),
	.output_tdata(output_tdata),
	.output_tvalid(output_tvalid),
	.output_tlast(output_tlast),
	.output_tready(output_tready)
);


endmodule
