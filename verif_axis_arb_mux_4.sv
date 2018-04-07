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
 * AXI4-Stream 4 port arbitrated multiplexer
 */
module verif_axis_arb_mux_4 #
(
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
    input  wire                   clk,
    input  wire                   rst,

    /*
     * AXI inputs
     */
    input  wire [DATA_WIDTH-1:0]  input_0_axis_tdata,
    input  wire                   input_0_axis_tvalid,
    input wire                   input_0_axis_tready,
    input  wire                   input_0_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_1_axis_tdata,
    input  wire                   input_1_axis_tvalid,
    input wire                   input_1_axis_tready,
    input  wire                   input_1_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_2_axis_tdata,
    input  wire                   input_2_axis_tvalid,
    input wire                   input_2_axis_tready,
    input  wire                   input_2_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_3_axis_tdata,
    input  wire                   input_3_axis_tvalid,
    input wire                   input_3_axis_tready,
    input  wire                   input_3_axis_tlast,

    /*
     * AXI output
     */
    input wire [DATA_WIDTH-1:0]  output_axis_tdata,
    input wire                   output_axis_tvalid,
    input  wire                   output_axis_tready,
    input wire                   output_axis_tlast
);

endmodule

module verif_arbiter #
(
    parameter PORTS = 4,
    // arbitration type: "PRIORITY" or "ROUND_ROBIN"
    parameter TYPE = "PRIORITY",
    // block type: "NONE", "REQUEST", "ACKNOWLEDGE"
    parameter BLOCK = "ACKNOWLEDGE",
    // LSB priority: "LOW", "HIGH"
    parameter LSB_PRIORITY = "HIGH"
)
(
    input  wire                     clk,
    input  wire                     rst,

    input  wire [PORTS-1:0]         request,
    input  wire [PORTS-1:0]         acknowledge,
	input wire request_valid,

    input wire [PORTS-1:0]         grant,
    input wire                     grant_valid,
    input wire [$clog2(PORTS)-1:0] grant_encoded
);


property req_until_grant(gnt, req);
	@(posedge clk) disable iff(rst) $rose(req) |-> (req throughout gnt[->1]) ##1 !req ;
endproperty
assume property (req_until_grant(grant[0], request[0]));
assume property (req_until_grant(grant[1], request[1]));
assume property (req_until_grant(grant[2], request[2]));
assume property (req_until_grant(grant[3], request[3]));

property req_gnt_until_ack(gnt, req, ack);
	@(posedge clk) disable iff(rst) ($rose(gnt) & req) |-> ( (req & gnt)throughout ack[->1]) ##1 !req ;
endproperty
assume property (req_gnt_until_ack(grant[0], request[0], acknowledge[0]));
assume property (req_gnt_until_ack(grant[1], request[1], acknowledge[1]));
assume property (req_gnt_until_ack(grant[2], request[2], acknowledge[2]));
assume property (req_gnt_until_ack(grant[3], request[3], acknowledge[3]));


assert property(
	@(posedge clk) disable iff(rst) $onehot0(grant)
);

property no_grant_without_req(gnt, req);
	@(posedge clk) disable iff(rst) $rose(gnt) |-> $past(req,1);
endproperty
assert property (no_grant_without_req(grant[0], request[0]));
assert property (no_grant_without_req(grant[1], request[1]));
assert property (no_grant_without_req(grant[2], request[2]));
assert property (no_grant_without_req(grant[3], request[3]));

assert property(
	@(posedge clk) $fell(rst) |-> (!grant)
);

assert property (@(posedge clk) disable iff (rst) 
						($past(request[3],1)  ) |-> grant[3]);
assert property (@(posedge clk) disable iff (rst) 
						($past(!request[3],1))&($past(request[2],1))   |-> grant[2]);
assert property (@(posedge clk) disable iff (rst) 
						($past(!request[3],1))&($past(!request[2],1))&($past(request[1],1))   |-> grant[1]);
assert property (@(posedge clk) disable iff (rst) 
						($past(!request[3],1))&($past(!request[2],1))&($past(!request[1],1))&($past(request[0],1))  ) |-> grant[0]);
						
						
endmodule



module verif_axis_mux_4 #
(
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1
)
(
    input  wire                   clk,
    input  wire                   rst,

    /*
     * AXI inputs
     */
    input  wire [DATA_WIDTH-1:0]  input_0_axis_tdata,
    input  wire                   input_0_axis_tvalid,
    input  wire                   input_0_axis_tready,
    input  wire                   input_0_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_1_axis_tdata,
    input  wire                   input_1_axis_tvalid,
    input  wire                   input_1_axis_tready,
    input  wire                   input_1_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_2_axis_tdata,
    input  wire                   input_2_axis_tvalid,
    input  wire                   input_2_axis_tready,
    input  wire                   input_2_axis_tlast,

    input  wire [DATA_WIDTH-1:0]  input_3_axis_tdata,
    input  wire                   input_3_axis_tvalid,
    input  wire                   input_3_axis_tready,
    input  wire                   input_3_axis_tlast,

    /*
     * AXI output
     */
    input wire [DATA_WIDTH-1:0]  output_axis_tdata,
    input wire                   output_axis_tvalid,
    input  wire                   output_axis_tready,
    input wire                   output_axis_tlast,

    /*
     * Control
     */
    input  wire                   enable,
    input  wire [1:0]             select
);



endmodule


module Wrapper;

bind axis_arb_mux_4 verif_axis_arb_mux_4 # (
	.DATA_WIDTH(DATA_WIDTH),
    .KEEP_ENABLE(KEEP_ENABLE),
    .KEEP_WIDTH(KEEP_WIDTH),
    .ID_ENABLE(ID_ENABLE),
    .ID_WIDTH(ID_WIDTH),
    .DEST_ENABLE(DEST_ENABLE),
    .USER_ENABLE(USER_ENABLE),
    .USER_WIDTH(USER_WIDTH),
    .ARB_TYPE(ARB_TYPE),
    .LSB_PRIORITY(LSB_PRIORITY)
)verif_axis_arb_mux_4_inst (

	.clk(clk),
    .rst(rst),
    /*
     * AXI inputs
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
     * AXI output
     */
    .output_axis_tdata(output_axis_tdata),
    .output_axis_tvalid(output_axis_tvalid),
    .output_axis_tready(output_axis_tready),
    .output_axis_tlast(output_axis_tlast)
);

bind arbiter verif_arbiter # (

	.PORTS(PORTS),
    .TYPE(TYPE),
    .BLOCK(BLOCK),
    .LSB_PRIORITY(LSB_PRIORITY)

)verif_arbiter_inst (
	.clk(clk),
	.rst(rst),
	.request(request),
	.request_valid(request_valid),
	.acknowledge(acknowledge),
	.grant(grant),
	.grant_valid(grant_valid),
	.grant_encoded(grant_encoded)

);

bind axis_mux_4 verif_axis_mux_4 # (

	.DATA_WIDTH(DATA_WIDTH),
    .KEEP_ENABLE(KEEP_ENABLE),
    .KEEP_WIDTH(KEEP_WIDTH),
    .ID_ENABLE(ID_ENABLE),
    .ID_WIDTH(ID_WIDTH),
    .DEST_ENABLE(DEST_ENABLE),
    .DEST_WIDTH(DEST_WIDTH),
    .USER_ENABLE(USER_ENABLE),
    .USER_WIDTH(USER_WIDTH)

)verif_axis_mux_4_inst (
	.clk(clk),
	.rst(rst),
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
	.output_axis_tdata(output_axis_tdata),
	.output_axis_tvalid(output_axis_tvalid),
	.output_axis_tready(output_axis_tready),
	.output_axis_tlast(output_axis_tlast),
	.enable(enable),
	.select(select)
	
);

endmodule
