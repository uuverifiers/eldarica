/**
 * Copyright (c) 2011-2016 Philipp Ruemmer. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.concurrency

import ap.parser._
import lazabs.horn.bottomup.{HornClauses, HornPredAbs, DagInterpolator, Util}
import ap.theories.SimpleArray

object MainGPUPara extends App {

  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  
  ap.util.Debug enableAllAssertions true

  //////////////////////////////////////////////////////////////////////////////

  {
  println("CSR multiplication")
    
  val p = for (i <- 0 to 12) yield (new Predicate("p" + i, 8 + 5))

  val ar = SimpleArray(1)
  
  val lock         = new ConstantTerm("lock")
  val N            = new ConstantTerm("N")
  val row_offset   = new ConstantTerm("row_offset")
  val ro_s         = new ConstantTerm("ro_s")
  val col_s        = new ConstantTerm("col_s")
  val val_s        = new ConstantTerm("val_s")
  val in_s         = new ConstantTerm("in_s")
  val out_s        = new ConstantTerm("out_s")
  val id           = new ConstantTerm("id")
  val ai           = new ConstantTerm("ai")
  val aj           = new ConstantTerm("aj")
  val nrow         = new ConstantTerm("nrow")
  val sum          = new ConstantTerm("sum")
  val any          = new ConstantTerm("any")
   
/*

 CSR multiplication (see
http://www.paralution.com/downloads/paralution-um.pdf page 18, CSR matrix)

 (ocl_kernels_csr.cl)

 __kernel void kernel_csr_spmv_scalar(const int nrow, __global const int
*row_offset, __global const int *col,
                                     __global const ValueType *val,
__global const ValueType *in,
                                     __global ValueType *out) {

  int ai = get_global_id(0);

  if (ai < nrow) {

    ValueType sum = 0;

    for (int aj=row_offset[ai]; aj<row_offset[ai+1]; ++aj)
      sum += val[aj] * in[col[aj]];

    out[ai] = sum;

  }

}

 */

  val kernel = List(

    // init
    (p(0)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
         (ro_s >= N + 1,
          all(x => trig(ar.select(row_offset, x) >= 0 & ar.select(row_offset, x) <= val_s,
                        ar.select(row_offset, x)))),
     NoSync),

    // assume(!lock && 0 <= id && id < N)
    (p(1)(0, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
          (p(0)(0, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
           id >= 0, id < N),
     NoSync),
    
    // lock := 1
    (p(2)(1, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
           p(1)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),
    
    // ai = get_global_id(0)
    (p(3)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, id, aj, nrow, sum) :-
           p(2)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),
    
    // assume(ai < nrow)
    (p(4)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
          (p(3)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum), ai < nrow),
     NoSync),
    
    // sum = 0
    (p(5)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, 0) :-
           p(4)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),
    
    // aj=row_offset[ai]
    (p(6)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai,
                                                 ar.select(row_offset, ai), nrow, sum) :-
           p(5)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),
    
    // assume(aj < row_offset[ai+1])
    (p(7)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
           (p(6)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
            aj < ar.select(row_offset, ai+1)),
     NoSync),

    // read val[aj]
    (p(8)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
           p(7)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),

    // read col[aj]
    (p(9)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
           p(8)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),

    // read in[*]
    (p(10)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum) :-
           p(9)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),

    // sum = ...; aj = aj + 1
    (p(6)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj + 1, nrow, any) :-
           p(10)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync),

    // assume(!(aj < row_offset[ai+1]))
    (p(11)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, any) :-
           (p(6)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
            aj >= ar.select(row_offset, ai+1)),
     NoSync),

    // out[ai] = sum
    (p(12)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, any) :-
           p(11)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
     NoSync)

  )

  val assertions = List(
    (ai >= 0 & ai < ro_s) :-
        p(5)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),
    (ai+1 >= 0 & ai+1 < ro_s) :-
        p(6)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum),

    (aj >= 0 & aj < val_s) :-
        p(7)(lock, N, row_offset, ro_s, col_s, val_s, in_s, out_s, id, ai, aj, nrow, sum)

    // , ...
  )

  val system =
    System(List((kernel, Infinite)), 7, None, NoTime, List(), assertions)

  new VerificationLoop(system)
  }

}
