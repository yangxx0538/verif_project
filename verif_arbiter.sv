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
module verif_arbiter #
(
    parameter PORTS = 4,
    // arbitration type: "PRIORITY" or "ROUND_ROBIN"
    parameter TYPE = "PRIORITY",
    // block type: "NONE", "REQUEST", "ACKNOWLEDGE"
    parameter BLOCK = "NONE",
    // LSB priority: "LOW", "HIGH"
    parameter LSB_PRIORITY = "LOW"
)
(
    input  wire                     clk,
    input  wire                     rst,

    input  wire [PORTS-1:0]         request,
    input  wire [PORTS-1:0]         acknowledge,

    input wire [PORTS-1:0]         grant,
    input wire                     grant_valid,
    input wire [$clog2(PORTS)-1:0] grant_encoded
);


endmodule

module Wrapper

bind arbiter verif_arbiter # (

	.PORTS(PORTS),
    .TYPE(TYPE),
    .BLOCK(BLOCK),
    .LSB_PRIORITY(LSB_PRIORITY)

)verif_arbiter_inst (
	.clk(clk),
	.rst(rst),
	.request(request),
	.acknowledge(acknowledge),
	.grant(grant),
	.grant_valid(grant_valid),
	.grant_encoded(grant_encoded)

);





endmodule
