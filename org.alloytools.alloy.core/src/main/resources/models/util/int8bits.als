module util/int8bits
open util/boolean


/*
*
*  A collection of utility functions for using Integers in Alloy.
*   
*/


/** Representation of a Integer of 8 bits */
sig Number8 {
   b00: Bool,
   b01: Bool,
   b02: Bool,
   b03: Bool,
   b04: Bool,
   b05: Bool,
   b06: Bool,
   b07: Bool
}

/** AdderCarry and AdderSum reserver functions */

fun AdderCarry[a: Bool, b: Bool, cin: Bool]: Bool {
Or[ And[a,b], And[cin, Xor[a,b]]]
}

fun AdderSum[a: Bool, b: Bool, cin: Bool]: Bool {
Xor[Xor[a, b], cin]
}



/**Frome here there are the well knowns preds and functions over integers provided by Alloy
with 8 bits representation*/ 

fun add [n1, n2 : Number8] : Number8 {
   {result : Number8 | predAdd[n1, n2, result]}
}

fun plus [n1, n2 : Number8] : Number8 {
   {result : Number8 | predAdd[n1, n2, result]}
}

fun sub [n1, n2 : Number8] : Number8 {
   {result : Number8 | predAdd[n2, result, n1]}
}

fun minus [n1, n2 : Number8] : Number8 {
   {result : Number8 | predAdd[n2, result, n1]}
}

fun mul [n1, n2: Number8] : Number8 {
   {result : Number8 | predMul[n1, n2, result]}
}

fun div [n1, n2: Number8] : Number8 {
   {result : Number8 | predMul[n1, result, n2]}
}

pred predRem[n1, n2, rem: Number8]{
   let div = div[n1, n2] |
   let aux = mul[div, n2] |
   rem = sub[n1, aux]
}

fun rem [n1, n2: Number8] : Number8{
 {result : Number8 | predRem[n1, n2, result]}
}


/** Predicate to state if a is equal to b */
pred eq[a: Number8, b: Number8] {
   a.b00 = b.b00
   a.b01 = b.b01
   a.b02 = b.b02
   a.b03 = b.b03
   a.b04 = b.b04
   a.b05 = b.b05
   a.b06 = b.b06
   a.b07 = b.b07
}

/** Predicate to state if a is not equal to b */
pred neq[a: Number8, b: Number8] {
   not eq[a, b]
}

/** Predicate to state if a is greater than b */
pred gt[a: Number8, b: Number8] {
   (a.b07 = False and b.b07 = True) 
   or (a.b07 = b.b07) and (a.b06 = True and b.b06 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = True and b.b05 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = True and b.b04 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = True and b.b03 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = True and b.b02 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = True and b.b01 = False) 
   or (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = b.b01) and (a.b00 = True and b.b00 = False) 
}


/** Predicate to state if a is less than b */
pred lt[a: Number8, b: Number8] {
   not gte[a, b]
}

/** Predicate to state if a is greater than or equal to b */
pred gte[a: Number8, b: Number8] {
   gt[a, b] or eq[a, b]
}

/** Predicate to state if a is less or equal to b */
pred lte[a: Number8, b: Number8] {
   not gt[a, b]
}


pred zero [n1: Number8]{
   n1.b00 in False 
   n1.b01 in False
   n1.b02 in False
   n1.b03 in False
   n1.b04 in False
   n1.b05 in False
   n1.b06 in False
   n1.b07 in False
}


pred pos [n1: Number8]{
   n1.b07 in False and not zero[n1]
}


pred neg [n1: Number8]{
   n1.b07 in True
}

pred nonpos[n1: Number8]{
   n1.b07 = True or zero[n1]
}

pred nonneg[n1: Number8]{
  n1.b07 = False 
}

fun maxInt : Number8 {
   {result : Number8 | result.b00 = True and 
                       result.b01 = True and 
                       result.b02 = True and 
                       result.b03 = True and
                       result.b04 = True and
                       result.b05 = True and
                       result.b06 = True and
                       result.b07 = False}
}

fun minInt : Number8 {
   {result : Number8 | result.b00 = True and 
                       result.b01 = False and 
                       result.b02 = False and 
                       result.b03 = False and
                       result.b04 = False and
                       result.b05 = False and
                       result.b06 = False and
                       result.b07 = True}
}



fun max[n: set Number8] : lone Number8 {
   {result : Number8 | all aux : n | gte[result,aux] and result in n}
}

fun min[n: set Number8] : lone Number8 {
   {result : Number8 | all aux : n | lte[result,aux] and result in n}
}

fun prevs[n: Number8]: set Number8 {
{result : Number8 | all a : result | lt[a, n]}
}


fun nexts[n: Number8]: set Number8 {
   {result: Number8 | all a : result | gt[a,n]}
}

fun larger [n1, n2: Number8] : Number8 {gte[n1, n2] => n1 else n2}

fun smaller [n1, n2: Number8] : Number8 {lte[n1, n2] => n1 else n2}


/** Auxiliar predicate to sum two numbers, the result is kept in result*/
pred predAdd[a: Number8, b: Number8, result: Number8] {
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
      result.b00 in s_0  and
      result.b01 in s_1  and
      result.b02 in s_2  and
      result.b03 in s_3  and
      result.b04 in s_4  and
      result.b05 in s_5  and
      result.b06 in s_6  and
      result.b07 in s_7 
}





/** Auxiliar predicate to multiplies two numbers, the result is kept in result*/
pred predMul[a: Number8, b: Number8, result: Number8] {
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
      result.b00 = s_0_1  and
      result.b01 = s_1_2  and
      result.b02 = s_2_3  and
      result.b03 = s_3_4  and
      result.b04 = s_4_5  and
      result.b05 = s_5_6  and
      result.b06 = s_6_7  and
      result.b07 = s_7_8 
}



--fun neg





/** given an integer, return all integers prior to it */
--fun prevs [e: Int]: set Int { e.^prev }


//fun sum
//fun sub
//fun mul
//fun div

/** returns the larger of the two integers */
--fun larger [e1, e2: Int]: Int { let a=int[e1], b=int[e2] | (a<b => b else a) }

/** returns the smaller of the two integers */
--fun smaller [e1, e2: Int]: Int { let a=int[e1], b=int[e2] | (a<b => a else b) }


sig s{
	conj : set Number8
}

pred toRun[n : Number8, aux : s]{
s.conj = nexts[n] and n !in s.conj
}

run toRun for 6 Number8, 1 s
