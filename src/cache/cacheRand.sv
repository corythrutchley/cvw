///////////////////////////////////////////
// cacheLRU.sv
//
// Written: Rose Thompson ross1728@gmail.com
// Created: 20 July 2021
// Modified: 20 January 2023
//
// Purpose: Implements Pseudo LRU. Tested for Powers of 2.
//
// Documentation: RISC-V System on Chip Design Chapter 7 (Figures 7.8 and 7.15 to 7.18)
//
// A component of the CORE-V-WALLY configurable RISC-V project.
// https://github.com/openhwgroup/cvw
//
// Copyright (C) 2021-23 Harvey Mudd College & Oklahoma State University
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may not use this file 
// except in compliance with the License, or, at your option, the Apache License version 2.0. You 
// may obtain a copy of the License at
//
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work distributed under the 
// License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, 
// either express or implied. See the License for the specific language governing permissions 
// and limitations under the License.
////////////////////////////////////////////////////////////////////////////////////////////////

module cacheRand
  #(parameter NUMWAYS = 4, SETLEN = 9, OFFSETLEN = 5, NUMLINES = 128) (
  input  logic                clk, 
  input  logic                reset,
  input  logic                FlushStage,
  input  logic [NUMWAYS-1:0]  ValidWay,        // Which ways for a particular set are valid, ignores tag
  input  logic [SETLEN-1:0]   CacheSetData,    // Cache address, the output of the address select mux, NextAdr, PAdr, or FlushAdr
  input  logic                WriteEn,         // Update the LRU state
  input  logic                ClearValid,      // Clear the dirty bit in the selected way and set
  input  logic                InvalidateCache, // Clear all valid bits
  output logic [NUMWAYS-1:0]  VictimWay        // LRU selects a victim to evict
);

  localparam                           LOGNUMWAYS = $clog2(NUMWAYS);
  logic [NUMWAYS-2:0]                  Memory [NUMLINES-1:0];

  // logic [NUMWAYS-2:0]                  Curr;
  logic [6:0]                          Curr;
  // logic                                Curr0, Curr1, Curr2, Curr3, Curr4, Curr5, Curr6;
  logic                                ShiftIn;
  logic [NUMWAYS-2:0]                  Next;
  logic [LOGNUMWAYS-1:0]               HitWayEncoded, Way;
  logic                                AllValid;
  genvar                               row;
  logic                                en;
  /* verilator lint_off UNOPTFLAT */
  // Rose: For some reason verilator does not like this.  I checked and it is not a circular path.
  logic [LOGNUMWAYS-1:0] Intermediate [NUMWAYS-2:0];
  /* verilator lint_on UNOPTFLAT */
  logic [NUMWAYS-1:0] FirstZero;
  logic [LOGNUMWAYS-1:0] FirstZeroWay;
  logic [LOGNUMWAYS-1:0] VictimWayEnc;
  binencoder #(NUMWAYS) hitwayencoder(HitWay, HitWayEncoded);
  assign AllValid = &ValidWay;
  ///// Update replacement bits.
  // coverage off
  // Excluded from coverage b/c it is untestable without varying NUMWAYS.
  function integer log2 (integer value);
    int val;
    val = value;
    for (log2 = 0; val > 0; log2 = log2+1)
      val = val >> 1;
    return log2;
  endfunction // log2
  // coverage on
  genvar               node;
  for(node = NUMWAYS-2; node >= NUMWAYS/2; node--) begin : enables
    localparam ctr = NUMWAYS - node - 1;
    localparam ctr_depth = log2(ctr);
    localparam lchild = node - ctr;
    localparam rchild = lchild - 1;
    localparam r = LOGNUMWAYS - ctr_depth;

    // the child node will be updated if its parent was updated and
    // the Way bit was the correct value.
  end

  priorityonehot #(NUMWAYS) FirstZeroEncoder(~ValidWay, FirstZero);
  binencoder #(NUMWAYS) FirstZeroWayEncoder(FirstZero, FirstZeroWay);
  mux2 #(LOGNUMWAYS) VictimMux(FirstZeroWay, Curr[1:0], AllValid, VictimWayEnc);
  decoder #(LOGNUMWAYS) decoder (VictimWayEnc, VictimWay);

  flopenr #(7) flop0(clk, reset, en, Curr[1], Curr[0]);
  flopenr #(7) flop1(clk, reset, en, Curr[2], Curr[1]);
  flopenr #(7) flop2(clk, reset, en, Curr[3], Curr[2]);
  flopenr #(7) flop3(clk, reset, en, Curr[4], Curr[3]);
  flopenr #(7) flop4(clk, reset, en, Curr[5], Curr[4]);
  flopenr #(7) flop5(clk, reset, en, Curr[6], Curr[5]);
  flopenr #(7) flop6(clk, reset, en, ShiftIn, Curr[6]);

  assign ShiftIn = Curr6 ^ Curr5 ^ Curr3 ^ Curr0;

  assign en = ~FlushStage & WriteEn;
  // LRU storage must be reset for modelsim to run. However the reset value does not actually matter in practice.
  // This is a two port memory.
  // Every cycle must read from CacheSetData and each load/store must write the new LRU.
  module flopenr #(parameter WIDTH = 8)
   (input  logic             clk, reset, en,
    input logic [WIDTH-1:0]  d, 
    output logic [WIDTH-1:0] q);

   always_ff @(posedge clk, posedge reset)
     if (reset)   q <= 0;
     else if (en) q <= d;
  endmodule

  always_ff @(posedge clk) begin
    if (reset | (InvalidateCache & ~FlushStage)) 
      for (int set = 0; set < NUMLINES; set++) Memory[set] = '0; // exclusion-tag: initialize
    else if(CacheEn) begin
      // Because we are using blocking assignments, change to LRUMemory must occur after LRUMemory is used so we get the proper value
      if(WriteEn & (PAdr == CacheSetTag)) Curr = Next;
      else                                Curr = Memory[CacheSetTag];
      if(WriteEn)                         Memory[PAdr] = Next;
    end
  end

endmodule