module util/int16bits
open util/boolean


/*
*
*  A collection of utility functions for using Integers in Alloy.
*   
*/


/** Representation of a Integer of 16 bits */
sig Number16 {
   b00: Bool,
   b01: Bool,
   b02: Bool,
   b03: Bool,
   b04: Bool,
   b05: Bool,
   b06: Bool,
   b07: Bool,
   b08: Bool,
   b09: Bool,
   b10: Bool,
   b11: Bool,
   b12: Bool,
   b13: Bool,
   b14: Bool,
   b15: Bool,
}


/** AdderCarry and AdderSum used as reserved functions */

fun AdderCarry[a: Bool, b: Bool, cin: Bool]: Bool {
Or[ And[a,b], And[cin, Xor[a,b]]]
}

fun AdderSum[a: Bool, b: Bool, cin: Bool]: Bool {
Xor[Xor[a, b], cin]
}

/**Frome here there are the well knowns preds and functions over integers provided by Alloy
with 8 bits representation*/ 

fun add [n1, n2 : Number16] : Number16 {
   {result : Number16 | predAdd[n1, n2, result]}
}

fun plus [n1, n2 : Number16] : Number16 {
   {result : Number16 | predAdd[n1, n2, result]}
}

fun sub [n1, n2 : Number16] : Number16 {
   {result : Number16 | predAdd[n2, result, n1]}
}

fun minus [n1, n2 : Number16] : Number16 {
   {result : Number16 | predAdd[n2, result, n1]}
}

fun mul [n1, n2: Number16] : Number16 {
   {result : Number16 | predMul[n1, n2, result]}
}

fun div [n1, n2: Number16] : Number16 {
   {result : Number16 | predMul[n1, result, n2]}
}

pred predRem[n1, n2, rem: Number16]{
   let div = div[n1, n2] |
   let aux = mul[div, n2] |
   rem = sub[n1, aux]
}

fun rem [n1, n2: Number16] : Number16{
 --  {result, div, aux : Number8 |  div = division[n1, n2] && aux = multiplicacion[div, n2] && result = resta[n1,aux]}
 {result : Number16 | predRem[n1, n2, result]}
}


/** Predicate to state if a is equal to b */
pred eq[a: Number16, b: Number16] {
   a.b00 = b.b00
   a.b01 = b.b01
   a.b02 = b.b02
   a.b03 = b.b03
   a.b04 = b.b04
   a.b05 = b.b05
   a.b06 = b.b06
   a.b07 = b.b07
   a.b08 = b.b08
   a.b09 = b.b09
   a.b10 = b.b10
   a.b11 = b.b11
   a.b12 = b.b12
   a.b13 = b.b13
   a.b14 = b.b14
   a.b15 = b.b15
}

/** Predicate to state if a is not equal to b */
pred neq[a: Number16, b: Number16] {
   not eq[a, b]
}

/** Predicate to state if a is greater than b */
pred gt[a: Number16, b: Number16] {
   (a.b15 = False and b.b15 = True) 
   or (a.b15 = b.b15) and (a.b14 = True and b.b14 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = True and b.b13 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = True and b.b12 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = True and b.b11 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = True and b.b10 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = True and b.b09 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = True and b.b08 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = True and b.b07 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = True and b.b06 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = True and b.b05 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = True and b.b04 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = True and b.b03 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = True and b.b02 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = True and b.b01 = False) 
   or (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = b.b01) and (a.b00 = True and b.b00 = False) 
}

/** Predicate to state if a is less than b */
pred lt[a: Number16, b: Number16] {
   not gte[a, b]
}


/** Predicate to state if a is greater than or equal to b */
pred gte[a: Number16, b: Number16] {
   gt[a, b] or eq[a, b]
}

/** Predicate to state if a is less or equal to b */
pred lte[a: Number16, b: Number16] {
   not gt[a, b]
}

pred zero [n1: Number16]{
   n1.b00 in False 
   n1.b01 in False
   n1.b02 in False
   n1.b03 in False
   n1.b04 in False
   n1.b05 in False
   n1.b06 in False
   n1.b07 in False
   n1.b08 in False 
   n1.b09 in False
   n1.b10 in False
   n1.b11 in False
   n1.b12 in False
   n1.b13 in False
   n1.b14 in False
   n1.b15 in False
}

pred pos [n1: Number16]{
   
   n1.b15 in False and not zero[n1]
}

pred neg [n1: Number16]{
   n1.b15 in True
}

pred nonpos[n1: Number16]{
   n1.b15 = True or zero[n1]
}

pred nonneg[n1: Number16]{
   n1.b15 = False
}




fun maxInt : Number16 {
   {result : Number16 | result.b00 = True and 
                        result.b01 = True and 
                        result.b02 = True and 
                        result.b03 = True and
                        result.b04 = True and
                        result.b05 = True and
                        result.b06 = True and
                        result.b07 = True and
                        result.b08 = True and 
                        result.b09 = True and 
                        result.b10 = True and 
                        result.b11 = True and
                        result.b12 = True and
                        result.b13 = True and
                        result.b14 = True and
                        result.b15 = False
                     }
}

fun minInt : Number16 {
   {result : Number16 | result.b00 = True and 
                        result.b01 = False and 
                        result.b02 = False and 
                        result.b03 = False and
                        result.b04 = False and
                        result.b05 = False and
                        result.b06 = False and
                        result.b07 = False and
                        result.b08 = False and 
                        result.b09 = False and 
                        result.b10 = False and 
                        result.b11 = False and
                        result.b12 = False and
                        result.b13 = False and
                        result.b14 = False and
                        result.b15 = True
                     }
}

fun max[n: set Number16] : lone Number16 {
   {result : Number16 | all aux : n | gte[result,aux] and result in n}
}

fun min[n: set Number16] : lone Number16 {
   {result : Number16 | all aux : n | lte[result,aux] and result in n}
}

fun prevs[n: Number16]: set Number16 {
   {result : Number16 | all a : result | lt[a, n]}
}


fun nexts[n: Number16]: set Number16 {
   {result: Number16 | all a : result | gt[a,n]}
}

fun larger [n1, n2: Number16] : Number16 {gte[n1, n2] => n1 else n2}

fun smaller [n1, n2: Number16] : Number16 {lte[n1, n2] => n1 else n2}




/** Auxiliar predicate to sum two numbers, the result is kept in result*/
pred predAdd[a: Number16, b: Number16, result: Number16] {
   let c_0 = False | 
   let s_0 = AdderSum[a.b00, b.b00, c_0] | 
   let c_1 = AdderCarry[a.b00, b.b00, c_0] | 
   let s_1 = AdderSum[a.b01, b.b01, c_1] | 
   let c_2 = AdderCarry[a.b01, b.b01, c_1] | 
   let s_2 = AdderSum[a.b02, b.b02, c_2] | 
   let c_3 = AdderCarry[a.b02, b.b02, c_2] | 
   let s_3 = AdderSum[a.b03, b.b03, c_3] | 
   let c_4 = AdderCarry[a.b03, b.b03, c_3] | 
   let s_4 = AdderSum[a.b04, b.b04, c_4] | 
   let c_5 = AdderCarry[a.b04, b.b04, c_4] | 
   let s_5 = AdderSum[a.b05, b.b05, c_5] | 
   let c_6 = AdderCarry[a.b05, b.b05, c_5] | 
   let s_6 = AdderSum[a.b06, b.b06, c_6] | 
   let c_7 = AdderCarry[a.b06, b.b06, c_6] | 
   let s_7 = AdderSum[a.b07, b.b07, c_7] | 
   let c_8 = AdderCarry[a.b07, b.b07, c_7] | 
   let s_8 = AdderSum[a.b08, b.b08, c_8] | 
   let c_9 = AdderCarry[a.b08, b.b08, c_8] | 
   let s_9 = AdderSum[a.b09, b.b09, c_9] | 
   let c_10 = AdderCarry[a.b09, b.b09, c_9] | 
   let s_10 = AdderSum[a.b10, b.b10, c_10] | 
   let c_11 = AdderCarry[a.b10, b.b10, c_10] | 
   let s_11 = AdderSum[a.b11, b.b11, c_11] | 
   let c_12 = AdderCarry[a.b11, b.b11, c_11] | 
   let s_12 = AdderSum[a.b12, b.b12, c_12] | 
   let c_13 = AdderCarry[a.b12, b.b12, c_12] | 
   let s_13 = AdderSum[a.b13, b.b13, c_13] | 
   let c_14 = AdderCarry[a.b13, b.b13, c_13] | 
   let s_14 = AdderSum[a.b14, b.b14, c_14] | 
   let c_15 = AdderCarry[a.b14, b.b14, c_14] | 
   let s_15 = AdderSum[a.b15, b.b15, c_15] | 
      result.b00 in s_0  and
      result.b01 in s_1  and
      result.b02 in s_2  and
      result.b03 in s_3  and
      result.b04 in s_4  and
      result.b05 in s_5  and
      result.b06 in s_6  and
      result.b07 in s_7  and
      result.b08 in s_8  and
      result.b09 in s_9  and
      result.b10 in s_10  and
      result.b11 in s_11  and
      result.b12 in s_12  and
      result.b13 in s_13  and
      result.b14 in s_14  and
      result.b15 in s_15 
}

/** Auxiliar predicate to multiplies two numbers, the result is kept in result*/
pred predMul[a: Number16, b: Number16, result: Number16] {
   let c_0_0 = False | 
   let s_0_0 = False | 
   let s_0_1 = AdderSum  [s_0_0,  And[a.b00, b.b00], c_0_0] | 
   let c_1_0 = False | 
   let c_1_1 = AdderCarry[s_0_0,  And[a.b00, b.b00], c_0_0] | 
   let s_1_0 = False | 
   let s_1_1 = AdderSum  [s_1_0,  And[a.b01, b.b00], c_1_0] | 
   let s_1_2 = AdderSum  [s_1_1,  And[a.b00, b.b01], c_1_1] | 
   let c_2_0 = False | 
   let c_2_1 = AdderCarry[s_1_0,  And[a.b01, b.b00], c_1_0] | 
   let c_2_2 = AdderCarry[s_1_1,  And[a.b00, b.b01], c_1_1] | 
   let s_2_0 = False | 
   let s_2_1 = AdderSum  [s_2_0,  And[a.b02, b.b00], c_2_0] | 
   let s_2_2 = AdderSum  [s_2_1,  And[a.b01, b.b01], c_2_1] | 
   let s_2_3 = AdderSum  [s_2_2,  And[a.b00, b.b02], c_2_2] | 
   let c_3_0 = False | 
   let c_3_1 = AdderCarry[s_2_0,  And[a.b02, b.b00], c_2_0] | 
   let c_3_2 = AdderCarry[s_2_1,  And[a.b01, b.b01], c_2_1] | 
   let c_3_3 = AdderCarry[s_2_2,  And[a.b00, b.b02], c_2_2] | 
   let s_3_0 = False | 
   let s_3_1 = AdderSum  [s_3_0,  And[a.b03, b.b00], c_3_0] | 
   let s_3_2 = AdderSum  [s_3_1,  And[a.b02, b.b01], c_3_1] | 
   let s_3_3 = AdderSum  [s_3_2,  And[a.b01, b.b02], c_3_2] | 
   let s_3_4 = AdderSum  [s_3_3,  And[a.b00, b.b03], c_3_3] | 
   let c_4_0 = False | 
   let c_4_1 = AdderCarry[s_3_0,  And[a.b03, b.b00], c_3_0] | 
   let c_4_2 = AdderCarry[s_3_1,  And[a.b02, b.b01], c_3_1] | 
   let c_4_3 = AdderCarry[s_3_2,  And[a.b01, b.b02], c_3_2] | 
   let c_4_4 = AdderCarry[s_3_3,  And[a.b00, b.b03], c_3_3] | 
   let s_4_0 = False | 
   let s_4_1 = AdderSum  [s_4_0,  And[a.b04, b.b00], c_4_0] | 
   let s_4_2 = AdderSum  [s_4_1,  And[a.b03, b.b01], c_4_1] | 
   let s_4_3 = AdderSum  [s_4_2,  And[a.b02, b.b02], c_4_2] | 
   let s_4_4 = AdderSum  [s_4_3,  And[a.b01, b.b03], c_4_3] | 
   let s_4_5 = AdderSum  [s_4_4,  And[a.b00, b.b04], c_4_4] | 
   let c_5_0 = False | 
   let c_5_1 = AdderCarry[s_4_0,  And[a.b04, b.b00], c_4_0] | 
   let c_5_2 = AdderCarry[s_4_1,  And[a.b03, b.b01], c_4_1] | 
   let c_5_3 = AdderCarry[s_4_2,  And[a.b02, b.b02], c_4_2] | 
   let c_5_4 = AdderCarry[s_4_3,  And[a.b01, b.b03], c_4_3] | 
   let c_5_5 = AdderCarry[s_4_4,  And[a.b00, b.b04], c_4_4] | 
   let s_5_0 = False | 
   let s_5_1 = AdderSum  [s_5_0,  And[a.b05, b.b00], c_5_0] | 
   let s_5_2 = AdderSum  [s_5_1,  And[a.b04, b.b01], c_5_1] | 
   let s_5_3 = AdderSum  [s_5_2,  And[a.b03, b.b02], c_5_2] | 
   let s_5_4 = AdderSum  [s_5_3,  And[a.b02, b.b03], c_5_3] | 
   let s_5_5 = AdderSum  [s_5_4,  And[a.b01, b.b04], c_5_4] | 
   let s_5_6 = AdderSum  [s_5_5,  And[a.b00, b.b05], c_5_5] | 
   let c_6_0 = False | 
   let c_6_1 = AdderCarry[s_5_0,  And[a.b05, b.b00], c_5_0] | 
   let c_6_2 = AdderCarry[s_5_1,  And[a.b04, b.b01], c_5_1] | 
   let c_6_3 = AdderCarry[s_5_2,  And[a.b03, b.b02], c_5_2] | 
   let c_6_4 = AdderCarry[s_5_3,  And[a.b02, b.b03], c_5_3] | 
   let c_6_5 = AdderCarry[s_5_4,  And[a.b01, b.b04], c_5_4] | 
   let c_6_6 = AdderCarry[s_5_5,  And[a.b00, b.b05], c_5_5] | 
   let s_6_0 = False | 
   let s_6_1 = AdderSum  [s_6_0,  And[a.b06, b.b00], c_6_0] | 
   let s_6_2 = AdderSum  [s_6_1,  And[a.b05, b.b01], c_6_1] | 
   let s_6_3 = AdderSum  [s_6_2,  And[a.b04, b.b02], c_6_2] | 
   let s_6_4 = AdderSum  [s_6_3,  And[a.b03, b.b03], c_6_3] | 
   let s_6_5 = AdderSum  [s_6_4,  And[a.b02, b.b04], c_6_4] | 
   let s_6_6 = AdderSum  [s_6_5,  And[a.b01, b.b05], c_6_5] | 
   let s_6_7 = AdderSum  [s_6_6,  And[a.b00, b.b06], c_6_6] | 
   let c_7_0 = False | 
   let c_7_1 = AdderCarry[s_6_0,  And[a.b06, b.b00], c_6_0] | 
   let c_7_2 = AdderCarry[s_6_1,  And[a.b05, b.b01], c_6_1] | 
   let c_7_3 = AdderCarry[s_6_2,  And[a.b04, b.b02], c_6_2] | 
   let c_7_4 = AdderCarry[s_6_3,  And[a.b03, b.b03], c_6_3] | 
   let c_7_5 = AdderCarry[s_6_4,  And[a.b02, b.b04], c_6_4] | 
   let c_7_6 = AdderCarry[s_6_5,  And[a.b01, b.b05], c_6_5] | 
   let c_7_7 = AdderCarry[s_6_6,  And[a.b00, b.b06], c_6_6] | 
   let s_7_0 = False | 
   let s_7_1 = AdderSum  [s_7_0,  And[a.b07, b.b00], c_7_0] | 
   let s_7_2 = AdderSum  [s_7_1,  And[a.b06, b.b01], c_7_1] | 
   let s_7_3 = AdderSum  [s_7_2,  And[a.b05, b.b02], c_7_2] | 
   let s_7_4 = AdderSum  [s_7_3,  And[a.b04, b.b03], c_7_3] | 
   let s_7_5 = AdderSum  [s_7_4,  And[a.b03, b.b04], c_7_4] | 
   let s_7_6 = AdderSum  [s_7_5,  And[a.b02, b.b05], c_7_5] | 
   let s_7_7 = AdderSum  [s_7_6,  And[a.b01, b.b06], c_7_6] | 
   let s_7_8 = AdderSum  [s_7_7,  And[a.b00, b.b07], c_7_7] | 
   let c_8_0 = False | 
   let c_8_1 = AdderCarry[s_7_0,  And[a.b07, b.b00], c_7_0] | 
   let c_8_2 = AdderCarry[s_7_1,  And[a.b06, b.b01], c_7_1] | 
   let c_8_3 = AdderCarry[s_7_2,  And[a.b05, b.b02], c_7_2] | 
   let c_8_4 = AdderCarry[s_7_3,  And[a.b04, b.b03], c_7_3] | 
   let c_8_5 = AdderCarry[s_7_4,  And[a.b03, b.b04], c_7_4] | 
   let c_8_6 = AdderCarry[s_7_5,  And[a.b02, b.b05], c_7_5] | 
   let c_8_7 = AdderCarry[s_7_6,  And[a.b01, b.b06], c_7_6] | 
   let c_8_8 = AdderCarry[s_7_7,  And[a.b00, b.b07], c_7_7] | 
   let s_8_0 = False | 
   let s_8_1 = AdderSum  [s_8_0,  And[a.b08, b.b00], c_8_0] | 
   let s_8_2 = AdderSum  [s_8_1,  And[a.b07, b.b01], c_8_1] | 
   let s_8_3 = AdderSum  [s_8_2,  And[a.b06, b.b02], c_8_2] | 
   let s_8_4 = AdderSum  [s_8_3,  And[a.b05, b.b03], c_8_3] | 
   let s_8_5 = AdderSum  [s_8_4,  And[a.b04, b.b04], c_8_4] | 
   let s_8_6 = AdderSum  [s_8_5,  And[a.b03, b.b05], c_8_5] | 
   let s_8_7 = AdderSum  [s_8_6,  And[a.b02, b.b06], c_8_6] | 
   let s_8_8 = AdderSum  [s_8_7,  And[a.b01, b.b07], c_8_7] | 
   let s_8_9 = AdderSum  [s_8_8,  And[a.b00, b.b08], c_8_8] | 
   let c_9_0 = False | 
   let c_9_1 = AdderCarry[s_8_0,  And[a.b08, b.b00], c_8_0] | 
   let c_9_2 = AdderCarry[s_8_1,  And[a.b07, b.b01], c_8_1] | 
   let c_9_3 = AdderCarry[s_8_2,  And[a.b06, b.b02], c_8_2] | 
   let c_9_4 = AdderCarry[s_8_3,  And[a.b05, b.b03], c_8_3] | 
   let c_9_5 = AdderCarry[s_8_4,  And[a.b04, b.b04], c_8_4] | 
   let c_9_6 = AdderCarry[s_8_5,  And[a.b03, b.b05], c_8_5] | 
   let c_9_7 = AdderCarry[s_8_6,  And[a.b02, b.b06], c_8_6] | 
   let c_9_8 = AdderCarry[s_8_7,  And[a.b01, b.b07], c_8_7] | 
   let c_9_9 = AdderCarry[s_8_8,  And[a.b00, b.b08], c_8_8] | 
   let s_9_0 = False | 
   let s_9_1 = AdderSum  [s_9_0,  And[a.b09, b.b00], c_9_0] | 
   let s_9_2 = AdderSum  [s_9_1,  And[a.b08, b.b01], c_9_1] | 
   let s_9_3 = AdderSum  [s_9_2,  And[a.b07, b.b02], c_9_2] | 
   let s_9_4 = AdderSum  [s_9_3,  And[a.b06, b.b03], c_9_3] | 
   let s_9_5 = AdderSum  [s_9_4,  And[a.b05, b.b04], c_9_4] | 
   let s_9_6 = AdderSum  [s_9_5,  And[a.b04, b.b05], c_9_5] | 
   let s_9_7 = AdderSum  [s_9_6,  And[a.b03, b.b06], c_9_6] | 
   let s_9_8 = AdderSum  [s_9_7,  And[a.b02, b.b07], c_9_7] | 
   let s_9_9 = AdderSum  [s_9_8,  And[a.b01, b.b08], c_9_8] | 
   let s_9_10 = AdderSum  [s_9_9,  And[a.b00, b.b09], c_9_9] | 
   let c_10_0 = False | 
   let c_10_1 = AdderCarry[s_9_0,  And[a.b09, b.b00], c_9_0] | 
   let c_10_2 = AdderCarry[s_9_1,  And[a.b08, b.b01], c_9_1] | 
   let c_10_3 = AdderCarry[s_9_2,  And[a.b07, b.b02], c_9_2] | 
   let c_10_4 = AdderCarry[s_9_3,  And[a.b06, b.b03], c_9_3] | 
   let c_10_5 = AdderCarry[s_9_4,  And[a.b05, b.b04], c_9_4] | 
   let c_10_6 = AdderCarry[s_9_5,  And[a.b04, b.b05], c_9_5] | 
   let c_10_7 = AdderCarry[s_9_6,  And[a.b03, b.b06], c_9_6] | 
   let c_10_8 = AdderCarry[s_9_7,  And[a.b02, b.b07], c_9_7] | 
   let c_10_9 = AdderCarry[s_9_8,  And[a.b01, b.b08], c_9_8] | 
   let c_10_10 = AdderCarry[s_9_9,  And[a.b00, b.b09], c_9_9] | 
   let s_10_0 = False | 
   let s_10_1 = AdderSum  [s_10_0,  And[a.b10, b.b00], c_10_0] | 
   let s_10_2 = AdderSum  [s_10_1,  And[a.b09, b.b01], c_10_1] | 
   let s_10_3 = AdderSum  [s_10_2,  And[a.b08, b.b02], c_10_2] | 
   let s_10_4 = AdderSum  [s_10_3,  And[a.b07, b.b03], c_10_3] | 
   let s_10_5 = AdderSum  [s_10_4,  And[a.b06, b.b04], c_10_4] | 
   let s_10_6 = AdderSum  [s_10_5,  And[a.b05, b.b05], c_10_5] | 
   let s_10_7 = AdderSum  [s_10_6,  And[a.b04, b.b06], c_10_6] | 
   let s_10_8 = AdderSum  [s_10_7,  And[a.b03, b.b07], c_10_7] | 
   let s_10_9 = AdderSum  [s_10_8,  And[a.b02, b.b08], c_10_8] | 
   let s_10_10 = AdderSum  [s_10_9,  And[a.b01, b.b09], c_10_9] | 
   let s_10_11 = AdderSum  [s_10_10,  And[a.b00, b.b10], c_10_10] | 
   let c_11_0 = False | 
   let c_11_1 = AdderCarry[s_10_0,  And[a.b10, b.b00], c_10_0] | 
   let c_11_2 = AdderCarry[s_10_1,  And[a.b09, b.b01], c_10_1] | 
   let c_11_3 = AdderCarry[s_10_2,  And[a.b08, b.b02], c_10_2] | 
   let c_11_4 = AdderCarry[s_10_3,  And[a.b07, b.b03], c_10_3] | 
   let c_11_5 = AdderCarry[s_10_4,  And[a.b06, b.b04], c_10_4] | 
   let c_11_6 = AdderCarry[s_10_5,  And[a.b05, b.b05], c_10_5] | 
   let c_11_7 = AdderCarry[s_10_6,  And[a.b04, b.b06], c_10_6] | 
   let c_11_8 = AdderCarry[s_10_7,  And[a.b03, b.b07], c_10_7] | 
   let c_11_9 = AdderCarry[s_10_8,  And[a.b02, b.b08], c_10_8] | 
   let c_11_10 = AdderCarry[s_10_9,  And[a.b01, b.b09], c_10_9] | 
   let c_11_11 = AdderCarry[s_10_10,  And[a.b00, b.b10], c_10_10] | 
   let s_11_0 = False | 
   let s_11_1 = AdderSum  [s_11_0,  And[a.b11, b.b00], c_11_0] | 
   let s_11_2 = AdderSum  [s_11_1,  And[a.b10, b.b01], c_11_1] | 
   let s_11_3 = AdderSum  [s_11_2,  And[a.b09, b.b02], c_11_2] | 
   let s_11_4 = AdderSum  [s_11_3,  And[a.b08, b.b03], c_11_3] | 
   let s_11_5 = AdderSum  [s_11_4,  And[a.b07, b.b04], c_11_4] | 
   let s_11_6 = AdderSum  [s_11_5,  And[a.b06, b.b05], c_11_5] | 
   let s_11_7 = AdderSum  [s_11_6,  And[a.b05, b.b06], c_11_6] | 
   let s_11_8 = AdderSum  [s_11_7,  And[a.b04, b.b07], c_11_7] | 
   let s_11_9 = AdderSum  [s_11_8,  And[a.b03, b.b08], c_11_8] | 
   let s_11_10 = AdderSum  [s_11_9,  And[a.b02, b.b09], c_11_9] | 
   let s_11_11 = AdderSum  [s_11_10,  And[a.b01, b.b10], c_11_10] | 
   let s_11_12 = AdderSum  [s_11_11,  And[a.b00, b.b11], c_11_11] | 
   let c_12_0 = False | 
   let c_12_1 = AdderCarry[s_11_0,  And[a.b11, b.b00], c_11_0] | 
   let c_12_2 = AdderCarry[s_11_1,  And[a.b10, b.b01], c_11_1] | 
   let c_12_3 = AdderCarry[s_11_2,  And[a.b09, b.b02], c_11_2] | 
   let c_12_4 = AdderCarry[s_11_3,  And[a.b08, b.b03], c_11_3] | 
   let c_12_5 = AdderCarry[s_11_4,  And[a.b07, b.b04], c_11_4] | 
   let c_12_6 = AdderCarry[s_11_5,  And[a.b06, b.b05], c_11_5] | 
   let c_12_7 = AdderCarry[s_11_6,  And[a.b05, b.b06], c_11_6] | 
   let c_12_8 = AdderCarry[s_11_7,  And[a.b04, b.b07], c_11_7] | 
   let c_12_9 = AdderCarry[s_11_8,  And[a.b03, b.b08], c_11_8] | 
   let c_12_10 = AdderCarry[s_11_9,  And[a.b02, b.b09], c_11_9] | 
   let c_12_11 = AdderCarry[s_11_10,  And[a.b01, b.b10], c_11_10] | 
   let c_12_12 = AdderCarry[s_11_11,  And[a.b00, b.b11], c_11_11] | 
   let s_12_0 = False | 
   let s_12_1 = AdderSum  [s_12_0,  And[a.b12, b.b00], c_12_0] | 
   let s_12_2 = AdderSum  [s_12_1,  And[a.b11, b.b01], c_12_1] | 
   let s_12_3 = AdderSum  [s_12_2,  And[a.b10, b.b02], c_12_2] | 
   let s_12_4 = AdderSum  [s_12_3,  And[a.b09, b.b03], c_12_3] | 
   let s_12_5 = AdderSum  [s_12_4,  And[a.b08, b.b04], c_12_4] | 
   let s_12_6 = AdderSum  [s_12_5,  And[a.b07, b.b05], c_12_5] | 
   let s_12_7 = AdderSum  [s_12_6,  And[a.b06, b.b06], c_12_6] | 
   let s_12_8 = AdderSum  [s_12_7,  And[a.b05, b.b07], c_12_7] | 
   let s_12_9 = AdderSum  [s_12_8,  And[a.b04, b.b08], c_12_8] | 
   let s_12_10 = AdderSum  [s_12_9,  And[a.b03, b.b09], c_12_9] | 
   let s_12_11 = AdderSum  [s_12_10,  And[a.b02, b.b10], c_12_10] | 
   let s_12_12 = AdderSum  [s_12_11,  And[a.b01, b.b11], c_12_11] | 
   let s_12_13 = AdderSum  [s_12_12,  And[a.b00, b.b12], c_12_12] | 
   let c_13_0 = False | 
   let c_13_1 = AdderCarry[s_12_0,  And[a.b12, b.b00], c_12_0] | 
   let c_13_2 = AdderCarry[s_12_1,  And[a.b11, b.b01], c_12_1] | 
   let c_13_3 = AdderCarry[s_12_2,  And[a.b10, b.b02], c_12_2] | 
   let c_13_4 = AdderCarry[s_12_3,  And[a.b09, b.b03], c_12_3] | 
   let c_13_5 = AdderCarry[s_12_4,  And[a.b08, b.b04], c_12_4] | 
   let c_13_6 = AdderCarry[s_12_5,  And[a.b07, b.b05], c_12_5] | 
   let c_13_7 = AdderCarry[s_12_6,  And[a.b06, b.b06], c_12_6] | 
   let c_13_8 = AdderCarry[s_12_7,  And[a.b05, b.b07], c_12_7] | 
   let c_13_9 = AdderCarry[s_12_8,  And[a.b04, b.b08], c_12_8] | 
   let c_13_10 = AdderCarry[s_12_9,  And[a.b03, b.b09], c_12_9] | 
   let c_13_11 = AdderCarry[s_12_10,  And[a.b02, b.b10], c_12_10] | 
   let c_13_12 = AdderCarry[s_12_11,  And[a.b01, b.b11], c_12_11] | 
   let c_13_13 = AdderCarry[s_12_12,  And[a.b00, b.b12], c_12_12] | 
   let s_13_0 = False | 
   let s_13_1 = AdderSum  [s_13_0,  And[a.b13, b.b00], c_13_0] | 
   let s_13_2 = AdderSum  [s_13_1,  And[a.b12, b.b01], c_13_1] | 
   let s_13_3 = AdderSum  [s_13_2,  And[a.b11, b.b02], c_13_2] | 
   let s_13_4 = AdderSum  [s_13_3,  And[a.b10, b.b03], c_13_3] | 
   let s_13_5 = AdderSum  [s_13_4,  And[a.b09, b.b04], c_13_4] | 
   let s_13_6 = AdderSum  [s_13_5,  And[a.b08, b.b05], c_13_5] | 
   let s_13_7 = AdderSum  [s_13_6,  And[a.b07, b.b06], c_13_6] | 
   let s_13_8 = AdderSum  [s_13_7,  And[a.b06, b.b07], c_13_7] | 
   let s_13_9 = AdderSum  [s_13_8,  And[a.b05, b.b08], c_13_8] | 
   let s_13_10 = AdderSum  [s_13_9,  And[a.b04, b.b09], c_13_9] | 
   let s_13_11 = AdderSum  [s_13_10,  And[a.b03, b.b10], c_13_10] | 
   let s_13_12 = AdderSum  [s_13_11,  And[a.b02, b.b11], c_13_11] | 
   let s_13_13 = AdderSum  [s_13_12,  And[a.b01, b.b12], c_13_12] | 
   let s_13_14 = AdderSum  [s_13_13,  And[a.b00, b.b13], c_13_13] | 
   let c_14_0 = False | 
   let c_14_1 = AdderCarry[s_13_0,  And[a.b13, b.b00], c_13_0] | 
   let c_14_2 = AdderCarry[s_13_1,  And[a.b12, b.b01], c_13_1] | 
   let c_14_3 = AdderCarry[s_13_2,  And[a.b11, b.b02], c_13_2] | 
   let c_14_4 = AdderCarry[s_13_3,  And[a.b10, b.b03], c_13_3] | 
   let c_14_5 = AdderCarry[s_13_4,  And[a.b09, b.b04], c_13_4] | 
   let c_14_6 = AdderCarry[s_13_5,  And[a.b08, b.b05], c_13_5] | 
   let c_14_7 = AdderCarry[s_13_6,  And[a.b07, b.b06], c_13_6] | 
   let c_14_8 = AdderCarry[s_13_7,  And[a.b06, b.b07], c_13_7] | 
   let c_14_9 = AdderCarry[s_13_8,  And[a.b05, b.b08], c_13_8] | 
   let c_14_10 = AdderCarry[s_13_9,  And[a.b04, b.b09], c_13_9] | 
   let c_14_11 = AdderCarry[s_13_10,  And[a.b03, b.b10], c_13_10] | 
   let c_14_12 = AdderCarry[s_13_11,  And[a.b02, b.b11], c_13_11] | 
   let c_14_13 = AdderCarry[s_13_12,  And[a.b01, b.b12], c_13_12] | 
   let c_14_14 = AdderCarry[s_13_13,  And[a.b00, b.b13], c_13_13] | 
   let s_14_0 = False | 
   let s_14_1 = AdderSum  [s_14_0,  And[a.b14, b.b00], c_14_0] | 
   let s_14_2 = AdderSum  [s_14_1,  And[a.b13, b.b01], c_14_1] | 
   let s_14_3 = AdderSum  [s_14_2,  And[a.b12, b.b02], c_14_2] | 
   let s_14_4 = AdderSum  [s_14_3,  And[a.b11, b.b03], c_14_3] | 
   let s_14_5 = AdderSum  [s_14_4,  And[a.b10, b.b04], c_14_4] | 
   let s_14_6 = AdderSum  [s_14_5,  And[a.b09, b.b05], c_14_5] | 
   let s_14_7 = AdderSum  [s_14_6,  And[a.b08, b.b06], c_14_6] | 
   let s_14_8 = AdderSum  [s_14_7,  And[a.b07, b.b07], c_14_7] | 
   let s_14_9 = AdderSum  [s_14_8,  And[a.b06, b.b08], c_14_8] | 
   let s_14_10 = AdderSum  [s_14_9,  And[a.b05, b.b09], c_14_9] | 
   let s_14_11 = AdderSum  [s_14_10,  And[a.b04, b.b10], c_14_10] | 
   let s_14_12 = AdderSum  [s_14_11,  And[a.b03, b.b11], c_14_11] | 
   let s_14_13 = AdderSum  [s_14_12,  And[a.b02, b.b12], c_14_12] | 
   let s_14_14 = AdderSum  [s_14_13,  And[a.b01, b.b13], c_14_13] | 
   let s_14_15 = AdderSum  [s_14_14,  And[a.b00, b.b14], c_14_14] | 
   let c_15_0 = False | 
   let c_15_1 = AdderCarry[s_14_0,  And[a.b14, b.b00], c_14_0] | 
   let c_15_2 = AdderCarry[s_14_1,  And[a.b13, b.b01], c_14_1] | 
   let c_15_3 = AdderCarry[s_14_2,  And[a.b12, b.b02], c_14_2] | 
   let c_15_4 = AdderCarry[s_14_3,  And[a.b11, b.b03], c_14_3] | 
   let c_15_5 = AdderCarry[s_14_4,  And[a.b10, b.b04], c_14_4] | 
   let c_15_6 = AdderCarry[s_14_5,  And[a.b09, b.b05], c_14_5] | 
   let c_15_7 = AdderCarry[s_14_6,  And[a.b08, b.b06], c_14_6] | 
   let c_15_8 = AdderCarry[s_14_7,  And[a.b07, b.b07], c_14_7] | 
   let c_15_9 = AdderCarry[s_14_8,  And[a.b06, b.b08], c_14_8] | 
   let c_15_10 = AdderCarry[s_14_9,  And[a.b05, b.b09], c_14_9] | 
   let c_15_11 = AdderCarry[s_14_10,  And[a.b04, b.b10], c_14_10] | 
   let c_15_12 = AdderCarry[s_14_11,  And[a.b03, b.b11], c_14_11] | 
   let c_15_13 = AdderCarry[s_14_12,  And[a.b02, b.b12], c_14_12] | 
   let c_15_14 = AdderCarry[s_14_13,  And[a.b01, b.b13], c_14_13] | 
   let c_15_15 = AdderCarry[s_14_14,  And[a.b00, b.b14], c_14_14] | 
   let s_15_0 = False | 
   let s_15_1 = AdderSum  [s_15_0,  And[a.b15, b.b00], c_15_0] | 
   let s_15_2 = AdderSum  [s_15_1,  And[a.b14, b.b01], c_15_1] | 
   let s_15_3 = AdderSum  [s_15_2,  And[a.b13, b.b02], c_15_2] | 
   let s_15_4 = AdderSum  [s_15_3,  And[a.b12, b.b03], c_15_3] | 
   let s_15_5 = AdderSum  [s_15_4,  And[a.b11, b.b04], c_15_4] | 
   let s_15_6 = AdderSum  [s_15_5,  And[a.b10, b.b05], c_15_5] | 
   let s_15_7 = AdderSum  [s_15_6,  And[a.b09, b.b06], c_15_6] | 
   let s_15_8 = AdderSum  [s_15_7,  And[a.b08, b.b07], c_15_7] | 
   let s_15_9 = AdderSum  [s_15_8,  And[a.b07, b.b08], c_15_8] | 
   let s_15_10 = AdderSum  [s_15_9,  And[a.b06, b.b09], c_15_9] | 
   let s_15_11 = AdderSum  [s_15_10,  And[a.b05, b.b10], c_15_10] | 
   let s_15_12 = AdderSum  [s_15_11,  And[a.b04, b.b11], c_15_11] | 
   let s_15_13 = AdderSum  [s_15_12,  And[a.b03, b.b12], c_15_12] | 
   let s_15_14 = AdderSum  [s_15_13,  And[a.b02, b.b13], c_15_13] | 
   let s_15_15 = AdderSum  [s_15_14,  And[a.b01, b.b14], c_15_14] | 
   let s_15_16 = AdderSum  [s_15_15,  And[a.b00, b.b15], c_15_15] | 
      result.b00 = s_0_1  and
      result.b01 = s_1_2  and
      result.b02 = s_2_3  and
      result.b03 = s_3_4  and
      result.b04 = s_4_5  and
      result.b05 = s_5_6  and
      result.b06 = s_6_7  and
      result.b07 = s_7_8  and
      result.b08 = s_8_9  and
      result.b09 = s_9_10  and
      result.b10 = s_10_11  and
      result.b11 = s_11_12  and
      result.b12 = s_12_13  and
      result.b13 = s_13_14  and
      result.b14 = s_14_15  and
      result.b15 = s_15_16 
}
/*
fun suma [n1, n2 : Number16] : Number16 {
   {result : Number16 | Sum[n1, n2, result]}
}

fun resta [n1, n2 : Number16] : Number16 {
   {result : Number16 | Sum[n1, result, n2]}
}

fun multiplicacion [n1, n2: Number16] : Number16 {
   {result : Number16 | Mul[n1, n2, result]}
}

fun division [n1, n2: Number16] : Number16 {
   {result : Number16 | Mul[n1, result, n2]}
}*/

//fun sum
//fun sub
//fun mul
//fun div
