module util/int32bits
open util/boolean

/*
*
*  A collection of utility functions for using Integers in Alloy.
*   
*/


/** Representation of a Integer of 32 bits */
sig Number32 {
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
   b16: Bool,
   b17: Bool,
   b18: Bool,
   b19: Bool,
   b20: Bool,
   b21: Bool,
   b22: Bool,
   b23: Bool,
   b24: Bool,
   b25: Bool,
   b26: Bool,
   b27: Bool,
   b28: Bool,
   b29: Bool,
   b30: Bool,
   b31: Bool,
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

fun add [n1, n2 : Number32] : Number32 {
   {result : Number32 | predAdd[n1, n2, result]}
}

fun plus [n1, n2 : Number32] : Number32 {
   {result : Number32 | predAdd[n1, n2, result]}
}

fun sub [n1, n2 : Number32] : Number32 {
   {result : Number32 | predAdd[n2, result, n1]}
}

fun minus [n1, n2 : Number32] : Number32 {
   {result : Number32 | predAdd[n2, result, n1]}
}

fun mul [n1, n2: Number32] : Number32 {
   {result : Number32 | predMul[n1, n2, result]}
}

fun div [n1, n2: Number32] : Number32 {
   {result : Number32 | predMul[n1, result, n2]}
}

pred predRem[n1, n2, rem: Number32]{
   let div = div[n1, n2] |
   let aux = mul[div, n2] |
   rem = sub[n1, aux]
}

fun rem [n1, n2: Number32] : Number32{
 --  {result, div, aux : Number8 |  div = division[n1, n2] && aux = multiplicacion[div, n2] && result = resta[n1,aux]}
 {result : Number32 | predRem[n1, n2, result]}
}

/** Predicate to state if a is equal to b */
pred eq[a: Number32, b: Number32] {
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
   a.b16 = b.b16
   a.b17 = b.b17
   a.b18 = b.b18
   a.b19 = b.b19
   a.b20 = b.b20
   a.b21 = b.b21
   a.b22 = b.b22
   a.b23 = b.b23
   a.b24 = b.b24
   a.b25 = b.b25
   a.b26 = b.b26
   a.b27 = b.b27
   a.b28 = b.b28
   a.b29 = b.b29
   a.b30 = b.b30
   a.b31 = b.b31
}

/** Predicate to state if a is not equal to b */
pred neq[a: Number32, b: Number32] {
   not eq[a, b]
}

/** Predicate to state if a is greater than b */
pred gt[a: Number32, b: Number32] {
   (a.b31 = False and b.b31 = True) 
   or (a.b31 = b.b31) and (a.b30 = True and b.b30 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = True and b.b29 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = True and b.b28 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = True and b.b27 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = True and b.b26 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = True and b.b25 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = True and b.b24 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = True and b.b23 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = True and b.b22 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = True and b.b21 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = True and b.b20 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = True and b.b19 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = True and b.b18 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = True and b.b17 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = True and b.b16 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = True and b.b15 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = True and b.b14 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = True and b.b13 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = True and b.b12 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = True and b.b11 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = True and b.b10 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = True and b.b09 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = True and b.b08 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = True and b.b07 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = True and b.b06 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = True and b.b05 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = True and b.b04 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = True and b.b03 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = True and b.b02 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = True and b.b01 = False) 
   or (a.b31 = b.b31) and (a.b30 = b.b30) and (a.b29 = b.b29) and (a.b28 = b.b28) and (a.b27 = b.b27) and (a.b26 = b.b26) and (a.b25 = b.b25) and (a.b24 = b.b24) and (a.b23 = b.b23) and (a.b22 = b.b22) and (a.b21 = b.b21) and (a.b20 = b.b20) and (a.b19 = b.b19) and (a.b18 = b.b18) and (a.b17 = b.b17) and (a.b16 = b.b16) and (a.b15 = b.b15) and (a.b14 = b.b14) and (a.b13 = b.b13) and (a.b12 = b.b12) and (a.b11 = b.b11) and (a.b10 = b.b10) and (a.b09 = b.b09) and (a.b08 = b.b08) and (a.b07 = b.b07) and (a.b06 = b.b06) and (a.b05 = b.b05) and (a.b04 = b.b04) and (a.b03 = b.b03) and (a.b02 = b.b02) and (a.b01 = b.b01) and (a.b00 = True and b.b00 = False) 
}

/** Predicate to state if a is less than b */
pred lt[a: Number32, b: Number32] {
   not gte[a, b]
}

/** Predicate to state if a is greater than or equal to b */
pred gte[a: Number32, b: Number32] {
   gt[a, b] or eq[a, b]
}


/** Predicate to state if a is less or equal to b */
pred lte[a: Number32, b: Number32] {
   not gt[a, b]
}


pred zero [n1: Number32]{
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
   n1.b16 in False 
   n1.b17 in False
   n1.b18 in False
   n1.b19 in False
   n1.b20 in False
   n1.b21 in False
   n1.b22 in False
   n1.b23 in False
   n1.b24 in False 
   n1.b25 in False
   n1.b26 in False
   n1.b27 in False
   n1.b28 in False
   n1.b29 in False
   n1.b30 in False
   n1.b31 in False
}

pred pos [n1: Number32]{
   n1.b31 in False and not zero[n1]
}

pred neg [n1: Number32]{
   n1.b31 in True
}

pred nonpos[n1: Number32]{
   n1.b31 = True or zero[n1]
}

pred nonneg[n1: Number32]{
   n1.b31 = False
}




fun maxInt : Number32 {
   {result : Number32 | result.b00 = True and 
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
                        result.b15 = True and
                        result.b16 = True and 
                        result.b17 = True and 
                        result.b18 = True and 
                        result.b19 = True and
                        result.b20 = True and
                        result.b21 = True and
                        result.b22 = True and
                        result.b23 = True and
                        result.b24 = True and 
                        result.b25 = True and 
                        result.b26 = True and 
                        result.b27 = True and
                        result.b28 = True and
                        result.b29 = True and
                        result.b30 = True and
                        result.b31 = False
                     }
}

fun minInt : Number32 {
   {result : Number32 | result.b00 = True and 
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
                        result.b15 = False and
                        result.b16 = False and 
                        result.b17 = False and 
                        result.b18 = False and 
                        result.b19 = False and
                        result.b20 = False and
                        result.b21 = False and
                        result.b22 = False and
                        result.b23 = False and
                        result.b24 = False and 
                        result.b25 = False and 
                        result.b26 = False and 
                        result.b27 = False and
                        result.b28 = False and
                        result.b29 = False and
                        result.b30 = False and
                        result.b31 = True
                     }
}

fun max[n: set Number32] : lone Number32 {
   {result : Number32 | all aux : n | gte[result,aux] and result in n}
}

fun min[n: set Number32] : lone Number32 {
   {result : Number32 | all aux : n | lte[result,aux] and result in n}
}

fun prevs[n: Number32]: set Number32 {
   {result : Number32 | all a : result | lt[a, n]}
}


fun nexts[n: Number32]: set Number32 {
   {result: Number32 | all a : result | gt[a,n]}
}

fun larger [n1, n2: Number32] : Number32 {gte[n1, n2] => n1 else n2}

fun smaller [n1, n2: Number32] : Number32 {lte[n1, n2] => n1 else n2}




/** Auxiliar predicate to sum two numbers, the result is kept in result*/
pred predAdd[a: Number32, b: Number32, result: Number32] {
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
   let c_16 = AdderCarry[a.b15, b.b15, c_15] | 
   let s_16 = AdderSum[a.b16, b.b16, c_16] | 
   let c_17 = AdderCarry[a.b16, b.b16, c_16] | 
   let s_17 = AdderSum[a.b17, b.b17, c_17] | 
   let c_18 = AdderCarry[a.b17, b.b17, c_17] | 
   let s_18 = AdderSum[a.b18, b.b18, c_18] | 
   let c_19 = AdderCarry[a.b18, b.b18, c_18] | 
   let s_19 = AdderSum[a.b19, b.b19, c_19] | 
   let c_20 = AdderCarry[a.b19, b.b19, c_19] | 
   let s_20 = AdderSum[a.b20, b.b20, c_20] | 
   let c_21 = AdderCarry[a.b20, b.b20, c_20] | 
   let s_21 = AdderSum[a.b21, b.b21, c_21] | 
   let c_22 = AdderCarry[a.b21, b.b21, c_21] | 
   let s_22 = AdderSum[a.b22, b.b22, c_22] | 
   let c_23 = AdderCarry[a.b22, b.b22, c_22] | 
   let s_23 = AdderSum[a.b23, b.b23, c_23] | 
   let c_24 = AdderCarry[a.b23, b.b23, c_23] | 
   let s_24 = AdderSum[a.b24, b.b24, c_24] | 
   let c_25 = AdderCarry[a.b24, b.b24, c_24] | 
   let s_25 = AdderSum[a.b25, b.b25, c_25] | 
   let c_26 = AdderCarry[a.b25, b.b25, c_25] | 
   let s_26 = AdderSum[a.b26, b.b26, c_26] | 
   let c_27 = AdderCarry[a.b26, b.b26, c_26] | 
   let s_27 = AdderSum[a.b27, b.b27, c_27] | 
   let c_28 = AdderCarry[a.b27, b.b27, c_27] | 
   let s_28 = AdderSum[a.b28, b.b28, c_28] | 
   let c_29 = AdderCarry[a.b28, b.b28, c_28] | 
   let s_29 = AdderSum[a.b29, b.b29, c_29] | 
   let c_30 = AdderCarry[a.b29, b.b29, c_29] | 
   let s_30 = AdderSum[a.b30, b.b30, c_30] | 
   let c_31 = AdderCarry[a.b30, b.b30, c_30] | 
   let s_31 = AdderSum[a.b31, b.b31, c_31] | 
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
      result.b15 in s_15  and
      result.b16 in s_16  and
      result.b17 in s_17  and
      result.b18 in s_18  and
      result.b19 in s_19  and
      result.b20 in s_20  and
      result.b21 in s_21  and
      result.b22 in s_22  and
      result.b23 in s_23  and
      result.b24 in s_24  and
      result.b25 in s_25  and
      result.b26 in s_26  and
      result.b27 in s_27  and
      result.b28 in s_28  and
      result.b29 in s_29  and
      result.b30 in s_30  and
      result.b31 in s_31 
}



/** Auxiliar predicate to multiplies two numbers, the result is kept in result*/
pred predMul[a: Number32, b: Number32, result: Number32] {
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
   let c_16_0 = False | 
   let c_16_1 = AdderCarry[s_15_0,  And[a.b15, b.b00], c_15_0] | 
   let c_16_2 = AdderCarry[s_15_1,  And[a.b14, b.b01], c_15_1] | 
   let c_16_3 = AdderCarry[s_15_2,  And[a.b13, b.b02], c_15_2] | 
   let c_16_4 = AdderCarry[s_15_3,  And[a.b12, b.b03], c_15_3] | 
   let c_16_5 = AdderCarry[s_15_4,  And[a.b11, b.b04], c_15_4] | 
   let c_16_6 = AdderCarry[s_15_5,  And[a.b10, b.b05], c_15_5] | 
   let c_16_7 = AdderCarry[s_15_6,  And[a.b09, b.b06], c_15_6] | 
   let c_16_8 = AdderCarry[s_15_7,  And[a.b08, b.b07], c_15_7] | 
   let c_16_9 = AdderCarry[s_15_8,  And[a.b07, b.b08], c_15_8] | 
   let c_16_10 = AdderCarry[s_15_9,  And[a.b06, b.b09], c_15_9] | 
   let c_16_11 = AdderCarry[s_15_10,  And[a.b05, b.b10], c_15_10] | 
   let c_16_12 = AdderCarry[s_15_11,  And[a.b04, b.b11], c_15_11] | 
   let c_16_13 = AdderCarry[s_15_12,  And[a.b03, b.b12], c_15_12] | 
   let c_16_14 = AdderCarry[s_15_13,  And[a.b02, b.b13], c_15_13] | 
   let c_16_15 = AdderCarry[s_15_14,  And[a.b01, b.b14], c_15_14] | 
   let c_16_16 = AdderCarry[s_15_15,  And[a.b00, b.b15], c_15_15] | 
   let s_16_0 = False | 
   let s_16_1 = AdderSum  [s_16_0,  And[a.b16, b.b00], c_16_0] | 
   let s_16_2 = AdderSum  [s_16_1,  And[a.b15, b.b01], c_16_1] | 
   let s_16_3 = AdderSum  [s_16_2,  And[a.b14, b.b02], c_16_2] | 
   let s_16_4 = AdderSum  [s_16_3,  And[a.b13, b.b03], c_16_3] | 
   let s_16_5 = AdderSum  [s_16_4,  And[a.b12, b.b04], c_16_4] | 
   let s_16_6 = AdderSum  [s_16_5,  And[a.b11, b.b05], c_16_5] | 
   let s_16_7 = AdderSum  [s_16_6,  And[a.b10, b.b06], c_16_6] | 
   let s_16_8 = AdderSum  [s_16_7,  And[a.b09, b.b07], c_16_7] | 
   let s_16_9 = AdderSum  [s_16_8,  And[a.b08, b.b08], c_16_8] | 
   let s_16_10 = AdderSum  [s_16_9,  And[a.b07, b.b09], c_16_9] | 
   let s_16_11 = AdderSum  [s_16_10,  And[a.b06, b.b10], c_16_10] | 
   let s_16_12 = AdderSum  [s_16_11,  And[a.b05, b.b11], c_16_11] | 
   let s_16_13 = AdderSum  [s_16_12,  And[a.b04, b.b12], c_16_12] | 
   let s_16_14 = AdderSum  [s_16_13,  And[a.b03, b.b13], c_16_13] | 
   let s_16_15 = AdderSum  [s_16_14,  And[a.b02, b.b14], c_16_14] | 
   let s_16_16 = AdderSum  [s_16_15,  And[a.b01, b.b15], c_16_15] | 
   let s_16_17 = AdderSum  [s_16_16,  And[a.b00, b.b16], c_16_16] | 
   let c_17_0 = False | 
   let c_17_1 = AdderCarry[s_16_0,  And[a.b16, b.b00], c_16_0] | 
   let c_17_2 = AdderCarry[s_16_1,  And[a.b15, b.b01], c_16_1] | 
   let c_17_3 = AdderCarry[s_16_2,  And[a.b14, b.b02], c_16_2] | 
   let c_17_4 = AdderCarry[s_16_3,  And[a.b13, b.b03], c_16_3] | 
   let c_17_5 = AdderCarry[s_16_4,  And[a.b12, b.b04], c_16_4] | 
   let c_17_6 = AdderCarry[s_16_5,  And[a.b11, b.b05], c_16_5] | 
   let c_17_7 = AdderCarry[s_16_6,  And[a.b10, b.b06], c_16_6] | 
   let c_17_8 = AdderCarry[s_16_7,  And[a.b09, b.b07], c_16_7] | 
   let c_17_9 = AdderCarry[s_16_8,  And[a.b08, b.b08], c_16_8] | 
   let c_17_10 = AdderCarry[s_16_9,  And[a.b07, b.b09], c_16_9] | 
   let c_17_11 = AdderCarry[s_16_10,  And[a.b06, b.b10], c_16_10] | 
   let c_17_12 = AdderCarry[s_16_11,  And[a.b05, b.b11], c_16_11] | 
   let c_17_13 = AdderCarry[s_16_12,  And[a.b04, b.b12], c_16_12] | 
   let c_17_14 = AdderCarry[s_16_13,  And[a.b03, b.b13], c_16_13] | 
   let c_17_15 = AdderCarry[s_16_14,  And[a.b02, b.b14], c_16_14] | 
   let c_17_16 = AdderCarry[s_16_15,  And[a.b01, b.b15], c_16_15] | 
   let c_17_17 = AdderCarry[s_16_16,  And[a.b00, b.b16], c_16_16] | 
   let s_17_0 = False | 
   let s_17_1 = AdderSum  [s_17_0,  And[a.b17, b.b00], c_17_0] | 
   let s_17_2 = AdderSum  [s_17_1,  And[a.b16, b.b01], c_17_1] | 
   let s_17_3 = AdderSum  [s_17_2,  And[a.b15, b.b02], c_17_2] | 
   let s_17_4 = AdderSum  [s_17_3,  And[a.b14, b.b03], c_17_3] | 
   let s_17_5 = AdderSum  [s_17_4,  And[a.b13, b.b04], c_17_4] | 
   let s_17_6 = AdderSum  [s_17_5,  And[a.b12, b.b05], c_17_5] | 
   let s_17_7 = AdderSum  [s_17_6,  And[a.b11, b.b06], c_17_6] | 
   let s_17_8 = AdderSum  [s_17_7,  And[a.b10, b.b07], c_17_7] | 
   let s_17_9 = AdderSum  [s_17_8,  And[a.b09, b.b08], c_17_8] | 
   let s_17_10 = AdderSum  [s_17_9,  And[a.b08, b.b09], c_17_9] | 
   let s_17_11 = AdderSum  [s_17_10,  And[a.b07, b.b10], c_17_10] | 
   let s_17_12 = AdderSum  [s_17_11,  And[a.b06, b.b11], c_17_11] | 
   let s_17_13 = AdderSum  [s_17_12,  And[a.b05, b.b12], c_17_12] | 
   let s_17_14 = AdderSum  [s_17_13,  And[a.b04, b.b13], c_17_13] | 
   let s_17_15 = AdderSum  [s_17_14,  And[a.b03, b.b14], c_17_14] | 
   let s_17_16 = AdderSum  [s_17_15,  And[a.b02, b.b15], c_17_15] | 
   let s_17_17 = AdderSum  [s_17_16,  And[a.b01, b.b16], c_17_16] | 
   let s_17_18 = AdderSum  [s_17_17,  And[a.b00, b.b17], c_17_17] | 
   let c_18_0 = False | 
   let c_18_1 = AdderCarry[s_17_0,  And[a.b17, b.b00], c_17_0] | 
   let c_18_2 = AdderCarry[s_17_1,  And[a.b16, b.b01], c_17_1] | 
   let c_18_3 = AdderCarry[s_17_2,  And[a.b15, b.b02], c_17_2] | 
   let c_18_4 = AdderCarry[s_17_3,  And[a.b14, b.b03], c_17_3] | 
   let c_18_5 = AdderCarry[s_17_4,  And[a.b13, b.b04], c_17_4] | 
   let c_18_6 = AdderCarry[s_17_5,  And[a.b12, b.b05], c_17_5] | 
   let c_18_7 = AdderCarry[s_17_6,  And[a.b11, b.b06], c_17_6] | 
   let c_18_8 = AdderCarry[s_17_7,  And[a.b10, b.b07], c_17_7] | 
   let c_18_9 = AdderCarry[s_17_8,  And[a.b09, b.b08], c_17_8] | 
   let c_18_10 = AdderCarry[s_17_9,  And[a.b08, b.b09], c_17_9] | 
   let c_18_11 = AdderCarry[s_17_10,  And[a.b07, b.b10], c_17_10] | 
   let c_18_12 = AdderCarry[s_17_11,  And[a.b06, b.b11], c_17_11] | 
   let c_18_13 = AdderCarry[s_17_12,  And[a.b05, b.b12], c_17_12] | 
   let c_18_14 = AdderCarry[s_17_13,  And[a.b04, b.b13], c_17_13] | 
   let c_18_15 = AdderCarry[s_17_14,  And[a.b03, b.b14], c_17_14] | 
   let c_18_16 = AdderCarry[s_17_15,  And[a.b02, b.b15], c_17_15] | 
   let c_18_17 = AdderCarry[s_17_16,  And[a.b01, b.b16], c_17_16] | 
   let c_18_18 = AdderCarry[s_17_17,  And[a.b00, b.b17], c_17_17] | 
   let s_18_0 = False | 
   let s_18_1 = AdderSum  [s_18_0,  And[a.b18, b.b00], c_18_0] | 
   let s_18_2 = AdderSum  [s_18_1,  And[a.b17, b.b01], c_18_1] | 
   let s_18_3 = AdderSum  [s_18_2,  And[a.b16, b.b02], c_18_2] | 
   let s_18_4 = AdderSum  [s_18_3,  And[a.b15, b.b03], c_18_3] | 
   let s_18_5 = AdderSum  [s_18_4,  And[a.b14, b.b04], c_18_4] | 
   let s_18_6 = AdderSum  [s_18_5,  And[a.b13, b.b05], c_18_5] | 
   let s_18_7 = AdderSum  [s_18_6,  And[a.b12, b.b06], c_18_6] | 
   let s_18_8 = AdderSum  [s_18_7,  And[a.b11, b.b07], c_18_7] | 
   let s_18_9 = AdderSum  [s_18_8,  And[a.b10, b.b08], c_18_8] | 
   let s_18_10 = AdderSum  [s_18_9,  And[a.b09, b.b09], c_18_9] | 
   let s_18_11 = AdderSum  [s_18_10,  And[a.b08, b.b10], c_18_10] | 
   let s_18_12 = AdderSum  [s_18_11,  And[a.b07, b.b11], c_18_11] | 
   let s_18_13 = AdderSum  [s_18_12,  And[a.b06, b.b12], c_18_12] | 
   let s_18_14 = AdderSum  [s_18_13,  And[a.b05, b.b13], c_18_13] | 
   let s_18_15 = AdderSum  [s_18_14,  And[a.b04, b.b14], c_18_14] | 
   let s_18_16 = AdderSum  [s_18_15,  And[a.b03, b.b15], c_18_15] | 
   let s_18_17 = AdderSum  [s_18_16,  And[a.b02, b.b16], c_18_16] | 
   let s_18_18 = AdderSum  [s_18_17,  And[a.b01, b.b17], c_18_17] | 
   let s_18_19 = AdderSum  [s_18_18,  And[a.b00, b.b18], c_18_18] | 
   let c_19_0 = False | 
   let c_19_1 = AdderCarry[s_18_0,  And[a.b18, b.b00], c_18_0] | 
   let c_19_2 = AdderCarry[s_18_1,  And[a.b17, b.b01], c_18_1] | 
   let c_19_3 = AdderCarry[s_18_2,  And[a.b16, b.b02], c_18_2] | 
   let c_19_4 = AdderCarry[s_18_3,  And[a.b15, b.b03], c_18_3] | 
   let c_19_5 = AdderCarry[s_18_4,  And[a.b14, b.b04], c_18_4] | 
   let c_19_6 = AdderCarry[s_18_5,  And[a.b13, b.b05], c_18_5] | 
   let c_19_7 = AdderCarry[s_18_6,  And[a.b12, b.b06], c_18_6] | 
   let c_19_8 = AdderCarry[s_18_7,  And[a.b11, b.b07], c_18_7] | 
   let c_19_9 = AdderCarry[s_18_8,  And[a.b10, b.b08], c_18_8] | 
   let c_19_10 = AdderCarry[s_18_9,  And[a.b09, b.b09], c_18_9] | 
   let c_19_11 = AdderCarry[s_18_10,  And[a.b08, b.b10], c_18_10] | 
   let c_19_12 = AdderCarry[s_18_11,  And[a.b07, b.b11], c_18_11] | 
   let c_19_13 = AdderCarry[s_18_12,  And[a.b06, b.b12], c_18_12] | 
   let c_19_14 = AdderCarry[s_18_13,  And[a.b05, b.b13], c_18_13] | 
   let c_19_15 = AdderCarry[s_18_14,  And[a.b04, b.b14], c_18_14] | 
   let c_19_16 = AdderCarry[s_18_15,  And[a.b03, b.b15], c_18_15] | 
   let c_19_17 = AdderCarry[s_18_16,  And[a.b02, b.b16], c_18_16] | 
   let c_19_18 = AdderCarry[s_18_17,  And[a.b01, b.b17], c_18_17] | 
   let c_19_19 = AdderCarry[s_18_18,  And[a.b00, b.b18], c_18_18] | 
   let s_19_0 = False | 
   let s_19_1 = AdderSum  [s_19_0,  And[a.b19, b.b00], c_19_0] | 
   let s_19_2 = AdderSum  [s_19_1,  And[a.b18, b.b01], c_19_1] | 
   let s_19_3 = AdderSum  [s_19_2,  And[a.b17, b.b02], c_19_2] | 
   let s_19_4 = AdderSum  [s_19_3,  And[a.b16, b.b03], c_19_3] | 
   let s_19_5 = AdderSum  [s_19_4,  And[a.b15, b.b04], c_19_4] | 
   let s_19_6 = AdderSum  [s_19_5,  And[a.b14, b.b05], c_19_5] | 
   let s_19_7 = AdderSum  [s_19_6,  And[a.b13, b.b06], c_19_6] | 
   let s_19_8 = AdderSum  [s_19_7,  And[a.b12, b.b07], c_19_7] | 
   let s_19_9 = AdderSum  [s_19_8,  And[a.b11, b.b08], c_19_8] | 
   let s_19_10 = AdderSum  [s_19_9,  And[a.b10, b.b09], c_19_9] | 
   let s_19_11 = AdderSum  [s_19_10,  And[a.b09, b.b10], c_19_10] | 
   let s_19_12 = AdderSum  [s_19_11,  And[a.b08, b.b11], c_19_11] | 
   let s_19_13 = AdderSum  [s_19_12,  And[a.b07, b.b12], c_19_12] | 
   let s_19_14 = AdderSum  [s_19_13,  And[a.b06, b.b13], c_19_13] | 
   let s_19_15 = AdderSum  [s_19_14,  And[a.b05, b.b14], c_19_14] | 
   let s_19_16 = AdderSum  [s_19_15,  And[a.b04, b.b15], c_19_15] | 
   let s_19_17 = AdderSum  [s_19_16,  And[a.b03, b.b16], c_19_16] | 
   let s_19_18 = AdderSum  [s_19_17,  And[a.b02, b.b17], c_19_17] | 
   let s_19_19 = AdderSum  [s_19_18,  And[a.b01, b.b18], c_19_18] | 
   let s_19_20 = AdderSum  [s_19_19,  And[a.b00, b.b19], c_19_19] | 
   let c_20_0 = False | 
   let c_20_1 = AdderCarry[s_19_0,  And[a.b19, b.b00], c_19_0] | 
   let c_20_2 = AdderCarry[s_19_1,  And[a.b18, b.b01], c_19_1] | 
   let c_20_3 = AdderCarry[s_19_2,  And[a.b17, b.b02], c_19_2] | 
   let c_20_4 = AdderCarry[s_19_3,  And[a.b16, b.b03], c_19_3] | 
   let c_20_5 = AdderCarry[s_19_4,  And[a.b15, b.b04], c_19_4] | 
   let c_20_6 = AdderCarry[s_19_5,  And[a.b14, b.b05], c_19_5] | 
   let c_20_7 = AdderCarry[s_19_6,  And[a.b13, b.b06], c_19_6] | 
   let c_20_8 = AdderCarry[s_19_7,  And[a.b12, b.b07], c_19_7] | 
   let c_20_9 = AdderCarry[s_19_8,  And[a.b11, b.b08], c_19_8] | 
   let c_20_10 = AdderCarry[s_19_9,  And[a.b10, b.b09], c_19_9] | 
   let c_20_11 = AdderCarry[s_19_10,  And[a.b09, b.b10], c_19_10] | 
   let c_20_12 = AdderCarry[s_19_11,  And[a.b08, b.b11], c_19_11] | 
   let c_20_13 = AdderCarry[s_19_12,  And[a.b07, b.b12], c_19_12] | 
   let c_20_14 = AdderCarry[s_19_13,  And[a.b06, b.b13], c_19_13] | 
   let c_20_15 = AdderCarry[s_19_14,  And[a.b05, b.b14], c_19_14] | 
   let c_20_16 = AdderCarry[s_19_15,  And[a.b04, b.b15], c_19_15] | 
   let c_20_17 = AdderCarry[s_19_16,  And[a.b03, b.b16], c_19_16] | 
   let c_20_18 = AdderCarry[s_19_17,  And[a.b02, b.b17], c_19_17] | 
   let c_20_19 = AdderCarry[s_19_18,  And[a.b01, b.b18], c_19_18] | 
   let c_20_20 = AdderCarry[s_19_19,  And[a.b00, b.b19], c_19_19] | 
   let s_20_0 = False | 
   let s_20_1 = AdderSum  [s_20_0,  And[a.b20, b.b00], c_20_0] | 
   let s_20_2 = AdderSum  [s_20_1,  And[a.b19, b.b01], c_20_1] | 
   let s_20_3 = AdderSum  [s_20_2,  And[a.b18, b.b02], c_20_2] | 
   let s_20_4 = AdderSum  [s_20_3,  And[a.b17, b.b03], c_20_3] | 
   let s_20_5 = AdderSum  [s_20_4,  And[a.b16, b.b04], c_20_4] | 
   let s_20_6 = AdderSum  [s_20_5,  And[a.b15, b.b05], c_20_5] | 
   let s_20_7 = AdderSum  [s_20_6,  And[a.b14, b.b06], c_20_6] | 
   let s_20_8 = AdderSum  [s_20_7,  And[a.b13, b.b07], c_20_7] | 
   let s_20_9 = AdderSum  [s_20_8,  And[a.b12, b.b08], c_20_8] | 
   let s_20_10 = AdderSum  [s_20_9,  And[a.b11, b.b09], c_20_9] | 
   let s_20_11 = AdderSum  [s_20_10,  And[a.b10, b.b10], c_20_10] | 
   let s_20_12 = AdderSum  [s_20_11,  And[a.b09, b.b11], c_20_11] | 
   let s_20_13 = AdderSum  [s_20_12,  And[a.b08, b.b12], c_20_12] | 
   let s_20_14 = AdderSum  [s_20_13,  And[a.b07, b.b13], c_20_13] | 
   let s_20_15 = AdderSum  [s_20_14,  And[a.b06, b.b14], c_20_14] | 
   let s_20_16 = AdderSum  [s_20_15,  And[a.b05, b.b15], c_20_15] | 
   let s_20_17 = AdderSum  [s_20_16,  And[a.b04, b.b16], c_20_16] | 
   let s_20_18 = AdderSum  [s_20_17,  And[a.b03, b.b17], c_20_17] | 
   let s_20_19 = AdderSum  [s_20_18,  And[a.b02, b.b18], c_20_18] | 
   let s_20_20 = AdderSum  [s_20_19,  And[a.b01, b.b19], c_20_19] | 
   let s_20_21 = AdderSum  [s_20_20,  And[a.b00, b.b20], c_20_20] | 
   let c_21_0 = False | 
   let c_21_1 = AdderCarry[s_20_0,  And[a.b20, b.b00], c_20_0] | 
   let c_21_2 = AdderCarry[s_20_1,  And[a.b19, b.b01], c_20_1] | 
   let c_21_3 = AdderCarry[s_20_2,  And[a.b18, b.b02], c_20_2] | 
   let c_21_4 = AdderCarry[s_20_3,  And[a.b17, b.b03], c_20_3] | 
   let c_21_5 = AdderCarry[s_20_4,  And[a.b16, b.b04], c_20_4] | 
   let c_21_6 = AdderCarry[s_20_5,  And[a.b15, b.b05], c_20_5] | 
   let c_21_7 = AdderCarry[s_20_6,  And[a.b14, b.b06], c_20_6] | 
   let c_21_8 = AdderCarry[s_20_7,  And[a.b13, b.b07], c_20_7] | 
   let c_21_9 = AdderCarry[s_20_8,  And[a.b12, b.b08], c_20_8] | 
   let c_21_10 = AdderCarry[s_20_9,  And[a.b11, b.b09], c_20_9] | 
   let c_21_11 = AdderCarry[s_20_10,  And[a.b10, b.b10], c_20_10] | 
   let c_21_12 = AdderCarry[s_20_11,  And[a.b09, b.b11], c_20_11] | 
   let c_21_13 = AdderCarry[s_20_12,  And[a.b08, b.b12], c_20_12] | 
   let c_21_14 = AdderCarry[s_20_13,  And[a.b07, b.b13], c_20_13] | 
   let c_21_15 = AdderCarry[s_20_14,  And[a.b06, b.b14], c_20_14] | 
   let c_21_16 = AdderCarry[s_20_15,  And[a.b05, b.b15], c_20_15] | 
   let c_21_17 = AdderCarry[s_20_16,  And[a.b04, b.b16], c_20_16] | 
   let c_21_18 = AdderCarry[s_20_17,  And[a.b03, b.b17], c_20_17] | 
   let c_21_19 = AdderCarry[s_20_18,  And[a.b02, b.b18], c_20_18] | 
   let c_21_20 = AdderCarry[s_20_19,  And[a.b01, b.b19], c_20_19] | 
   let c_21_21 = AdderCarry[s_20_20,  And[a.b00, b.b20], c_20_20] | 
   let s_21_0 = False | 
   let s_21_1 = AdderSum  [s_21_0,  And[a.b21, b.b00], c_21_0] | 
   let s_21_2 = AdderSum  [s_21_1,  And[a.b20, b.b01], c_21_1] | 
   let s_21_3 = AdderSum  [s_21_2,  And[a.b19, b.b02], c_21_2] | 
   let s_21_4 = AdderSum  [s_21_3,  And[a.b18, b.b03], c_21_3] | 
   let s_21_5 = AdderSum  [s_21_4,  And[a.b17, b.b04], c_21_4] | 
   let s_21_6 = AdderSum  [s_21_5,  And[a.b16, b.b05], c_21_5] | 
   let s_21_7 = AdderSum  [s_21_6,  And[a.b15, b.b06], c_21_6] | 
   let s_21_8 = AdderSum  [s_21_7,  And[a.b14, b.b07], c_21_7] | 
   let s_21_9 = AdderSum  [s_21_8,  And[a.b13, b.b08], c_21_8] | 
   let s_21_10 = AdderSum  [s_21_9,  And[a.b12, b.b09], c_21_9] | 
   let s_21_11 = AdderSum  [s_21_10,  And[a.b11, b.b10], c_21_10] | 
   let s_21_12 = AdderSum  [s_21_11,  And[a.b10, b.b11], c_21_11] | 
   let s_21_13 = AdderSum  [s_21_12,  And[a.b09, b.b12], c_21_12] | 
   let s_21_14 = AdderSum  [s_21_13,  And[a.b08, b.b13], c_21_13] | 
   let s_21_15 = AdderSum  [s_21_14,  And[a.b07, b.b14], c_21_14] | 
   let s_21_16 = AdderSum  [s_21_15,  And[a.b06, b.b15], c_21_15] | 
   let s_21_17 = AdderSum  [s_21_16,  And[a.b05, b.b16], c_21_16] | 
   let s_21_18 = AdderSum  [s_21_17,  And[a.b04, b.b17], c_21_17] | 
   let s_21_19 = AdderSum  [s_21_18,  And[a.b03, b.b18], c_21_18] | 
   let s_21_20 = AdderSum  [s_21_19,  And[a.b02, b.b19], c_21_19] | 
   let s_21_21 = AdderSum  [s_21_20,  And[a.b01, b.b20], c_21_20] | 
   let s_21_22 = AdderSum  [s_21_21,  And[a.b00, b.b21], c_21_21] | 
   let c_22_0 = False | 
   let c_22_1 = AdderCarry[s_21_0,  And[a.b21, b.b00], c_21_0] | 
   let c_22_2 = AdderCarry[s_21_1,  And[a.b20, b.b01], c_21_1] | 
   let c_22_3 = AdderCarry[s_21_2,  And[a.b19, b.b02], c_21_2] | 
   let c_22_4 = AdderCarry[s_21_3,  And[a.b18, b.b03], c_21_3] | 
   let c_22_5 = AdderCarry[s_21_4,  And[a.b17, b.b04], c_21_4] | 
   let c_22_6 = AdderCarry[s_21_5,  And[a.b16, b.b05], c_21_5] | 
   let c_22_7 = AdderCarry[s_21_6,  And[a.b15, b.b06], c_21_6] | 
   let c_22_8 = AdderCarry[s_21_7,  And[a.b14, b.b07], c_21_7] | 
   let c_22_9 = AdderCarry[s_21_8,  And[a.b13, b.b08], c_21_8] | 
   let c_22_10 = AdderCarry[s_21_9,  And[a.b12, b.b09], c_21_9] | 
   let c_22_11 = AdderCarry[s_21_10,  And[a.b11, b.b10], c_21_10] | 
   let c_22_12 = AdderCarry[s_21_11,  And[a.b10, b.b11], c_21_11] | 
   let c_22_13 = AdderCarry[s_21_12,  And[a.b09, b.b12], c_21_12] | 
   let c_22_14 = AdderCarry[s_21_13,  And[a.b08, b.b13], c_21_13] | 
   let c_22_15 = AdderCarry[s_21_14,  And[a.b07, b.b14], c_21_14] | 
   let c_22_16 = AdderCarry[s_21_15,  And[a.b06, b.b15], c_21_15] | 
   let c_22_17 = AdderCarry[s_21_16,  And[a.b05, b.b16], c_21_16] | 
   let c_22_18 = AdderCarry[s_21_17,  And[a.b04, b.b17], c_21_17] | 
   let c_22_19 = AdderCarry[s_21_18,  And[a.b03, b.b18], c_21_18] | 
   let c_22_20 = AdderCarry[s_21_19,  And[a.b02, b.b19], c_21_19] | 
   let c_22_21 = AdderCarry[s_21_20,  And[a.b01, b.b20], c_21_20] | 
   let c_22_22 = AdderCarry[s_21_21,  And[a.b00, b.b21], c_21_21] | 
   let s_22_0 = False | 
   let s_22_1 = AdderSum  [s_22_0,  And[a.b22, b.b00], c_22_0] | 
   let s_22_2 = AdderSum  [s_22_1,  And[a.b21, b.b01], c_22_1] | 
   let s_22_3 = AdderSum  [s_22_2,  And[a.b20, b.b02], c_22_2] | 
   let s_22_4 = AdderSum  [s_22_3,  And[a.b19, b.b03], c_22_3] | 
   let s_22_5 = AdderSum  [s_22_4,  And[a.b18, b.b04], c_22_4] | 
   let s_22_6 = AdderSum  [s_22_5,  And[a.b17, b.b05], c_22_5] | 
   let s_22_7 = AdderSum  [s_22_6,  And[a.b16, b.b06], c_22_6] | 
   let s_22_8 = AdderSum  [s_22_7,  And[a.b15, b.b07], c_22_7] | 
   let s_22_9 = AdderSum  [s_22_8,  And[a.b14, b.b08], c_22_8] | 
   let s_22_10 = AdderSum  [s_22_9,  And[a.b13, b.b09], c_22_9] | 
   let s_22_11 = AdderSum  [s_22_10,  And[a.b12, b.b10], c_22_10] | 
   let s_22_12 = AdderSum  [s_22_11,  And[a.b11, b.b11], c_22_11] | 
   let s_22_13 = AdderSum  [s_22_12,  And[a.b10, b.b12], c_22_12] | 
   let s_22_14 = AdderSum  [s_22_13,  And[a.b09, b.b13], c_22_13] | 
   let s_22_15 = AdderSum  [s_22_14,  And[a.b08, b.b14], c_22_14] | 
   let s_22_16 = AdderSum  [s_22_15,  And[a.b07, b.b15], c_22_15] | 
   let s_22_17 = AdderSum  [s_22_16,  And[a.b06, b.b16], c_22_16] | 
   let s_22_18 = AdderSum  [s_22_17,  And[a.b05, b.b17], c_22_17] | 
   let s_22_19 = AdderSum  [s_22_18,  And[a.b04, b.b18], c_22_18] | 
   let s_22_20 = AdderSum  [s_22_19,  And[a.b03, b.b19], c_22_19] | 
   let s_22_21 = AdderSum  [s_22_20,  And[a.b02, b.b20], c_22_20] | 
   let s_22_22 = AdderSum  [s_22_21,  And[a.b01, b.b21], c_22_21] | 
   let s_22_23 = AdderSum  [s_22_22,  And[a.b00, b.b22], c_22_22] | 
   let c_23_0 = False | 
   let c_23_1 = AdderCarry[s_22_0,  And[a.b22, b.b00], c_22_0] | 
   let c_23_2 = AdderCarry[s_22_1,  And[a.b21, b.b01], c_22_1] | 
   let c_23_3 = AdderCarry[s_22_2,  And[a.b20, b.b02], c_22_2] | 
   let c_23_4 = AdderCarry[s_22_3,  And[a.b19, b.b03], c_22_3] | 
   let c_23_5 = AdderCarry[s_22_4,  And[a.b18, b.b04], c_22_4] | 
   let c_23_6 = AdderCarry[s_22_5,  And[a.b17, b.b05], c_22_5] | 
   let c_23_7 = AdderCarry[s_22_6,  And[a.b16, b.b06], c_22_6] | 
   let c_23_8 = AdderCarry[s_22_7,  And[a.b15, b.b07], c_22_7] | 
   let c_23_9 = AdderCarry[s_22_8,  And[a.b14, b.b08], c_22_8] | 
   let c_23_10 = AdderCarry[s_22_9,  And[a.b13, b.b09], c_22_9] | 
   let c_23_11 = AdderCarry[s_22_10,  And[a.b12, b.b10], c_22_10] | 
   let c_23_12 = AdderCarry[s_22_11,  And[a.b11, b.b11], c_22_11] | 
   let c_23_13 = AdderCarry[s_22_12,  And[a.b10, b.b12], c_22_12] | 
   let c_23_14 = AdderCarry[s_22_13,  And[a.b09, b.b13], c_22_13] | 
   let c_23_15 = AdderCarry[s_22_14,  And[a.b08, b.b14], c_22_14] | 
   let c_23_16 = AdderCarry[s_22_15,  And[a.b07, b.b15], c_22_15] | 
   let c_23_17 = AdderCarry[s_22_16,  And[a.b06, b.b16], c_22_16] | 
   let c_23_18 = AdderCarry[s_22_17,  And[a.b05, b.b17], c_22_17] | 
   let c_23_19 = AdderCarry[s_22_18,  And[a.b04, b.b18], c_22_18] | 
   let c_23_20 = AdderCarry[s_22_19,  And[a.b03, b.b19], c_22_19] | 
   let c_23_21 = AdderCarry[s_22_20,  And[a.b02, b.b20], c_22_20] | 
   let c_23_22 = AdderCarry[s_22_21,  And[a.b01, b.b21], c_22_21] | 
   let c_23_23 = AdderCarry[s_22_22,  And[a.b00, b.b22], c_22_22] | 
   let s_23_0 = False | 
   let s_23_1 = AdderSum  [s_23_0,  And[a.b23, b.b00], c_23_0] | 
   let s_23_2 = AdderSum  [s_23_1,  And[a.b22, b.b01], c_23_1] | 
   let s_23_3 = AdderSum  [s_23_2,  And[a.b21, b.b02], c_23_2] | 
   let s_23_4 = AdderSum  [s_23_3,  And[a.b20, b.b03], c_23_3] | 
   let s_23_5 = AdderSum  [s_23_4,  And[a.b19, b.b04], c_23_4] | 
   let s_23_6 = AdderSum  [s_23_5,  And[a.b18, b.b05], c_23_5] | 
   let s_23_7 = AdderSum  [s_23_6,  And[a.b17, b.b06], c_23_6] | 
   let s_23_8 = AdderSum  [s_23_7,  And[a.b16, b.b07], c_23_7] | 
   let s_23_9 = AdderSum  [s_23_8,  And[a.b15, b.b08], c_23_8] | 
   let s_23_10 = AdderSum  [s_23_9,  And[a.b14, b.b09], c_23_9] | 
   let s_23_11 = AdderSum  [s_23_10,  And[a.b13, b.b10], c_23_10] | 
   let s_23_12 = AdderSum  [s_23_11,  And[a.b12, b.b11], c_23_11] | 
   let s_23_13 = AdderSum  [s_23_12,  And[a.b11, b.b12], c_23_12] | 
   let s_23_14 = AdderSum  [s_23_13,  And[a.b10, b.b13], c_23_13] | 
   let s_23_15 = AdderSum  [s_23_14,  And[a.b09, b.b14], c_23_14] | 
   let s_23_16 = AdderSum  [s_23_15,  And[a.b08, b.b15], c_23_15] | 
   let s_23_17 = AdderSum  [s_23_16,  And[a.b07, b.b16], c_23_16] | 
   let s_23_18 = AdderSum  [s_23_17,  And[a.b06, b.b17], c_23_17] | 
   let s_23_19 = AdderSum  [s_23_18,  And[a.b05, b.b18], c_23_18] | 
   let s_23_20 = AdderSum  [s_23_19,  And[a.b04, b.b19], c_23_19] | 
   let s_23_21 = AdderSum  [s_23_20,  And[a.b03, b.b20], c_23_20] | 
   let s_23_22 = AdderSum  [s_23_21,  And[a.b02, b.b21], c_23_21] | 
   let s_23_23 = AdderSum  [s_23_22,  And[a.b01, b.b22], c_23_22] | 
   let s_23_24 = AdderSum  [s_23_23,  And[a.b00, b.b23], c_23_23] | 
   let c_24_0 = False | 
   let c_24_1 = AdderCarry[s_23_0,  And[a.b23, b.b00], c_23_0] | 
   let c_24_2 = AdderCarry[s_23_1,  And[a.b22, b.b01], c_23_1] | 
   let c_24_3 = AdderCarry[s_23_2,  And[a.b21, b.b02], c_23_2] | 
   let c_24_4 = AdderCarry[s_23_3,  And[a.b20, b.b03], c_23_3] | 
   let c_24_5 = AdderCarry[s_23_4,  And[a.b19, b.b04], c_23_4] | 
   let c_24_6 = AdderCarry[s_23_5,  And[a.b18, b.b05], c_23_5] | 
   let c_24_7 = AdderCarry[s_23_6,  And[a.b17, b.b06], c_23_6] | 
   let c_24_8 = AdderCarry[s_23_7,  And[a.b16, b.b07], c_23_7] | 
   let c_24_9 = AdderCarry[s_23_8,  And[a.b15, b.b08], c_23_8] | 
   let c_24_10 = AdderCarry[s_23_9,  And[a.b14, b.b09], c_23_9] | 
   let c_24_11 = AdderCarry[s_23_10,  And[a.b13, b.b10], c_23_10] | 
   let c_24_12 = AdderCarry[s_23_11,  And[a.b12, b.b11], c_23_11] | 
   let c_24_13 = AdderCarry[s_23_12,  And[a.b11, b.b12], c_23_12] | 
   let c_24_14 = AdderCarry[s_23_13,  And[a.b10, b.b13], c_23_13] | 
   let c_24_15 = AdderCarry[s_23_14,  And[a.b09, b.b14], c_23_14] | 
   let c_24_16 = AdderCarry[s_23_15,  And[a.b08, b.b15], c_23_15] | 
   let c_24_17 = AdderCarry[s_23_16,  And[a.b07, b.b16], c_23_16] | 
   let c_24_18 = AdderCarry[s_23_17,  And[a.b06, b.b17], c_23_17] | 
   let c_24_19 = AdderCarry[s_23_18,  And[a.b05, b.b18], c_23_18] | 
   let c_24_20 = AdderCarry[s_23_19,  And[a.b04, b.b19], c_23_19] | 
   let c_24_21 = AdderCarry[s_23_20,  And[a.b03, b.b20], c_23_20] | 
   let c_24_22 = AdderCarry[s_23_21,  And[a.b02, b.b21], c_23_21] | 
   let c_24_23 = AdderCarry[s_23_22,  And[a.b01, b.b22], c_23_22] | 
   let c_24_24 = AdderCarry[s_23_23,  And[a.b00, b.b23], c_23_23] | 
   let s_24_0 = False | 
   let s_24_1 = AdderSum  [s_24_0,  And[a.b24, b.b00], c_24_0] | 
   let s_24_2 = AdderSum  [s_24_1,  And[a.b23, b.b01], c_24_1] | 
   let s_24_3 = AdderSum  [s_24_2,  And[a.b22, b.b02], c_24_2] | 
   let s_24_4 = AdderSum  [s_24_3,  And[a.b21, b.b03], c_24_3] | 
   let s_24_5 = AdderSum  [s_24_4,  And[a.b20, b.b04], c_24_4] | 
   let s_24_6 = AdderSum  [s_24_5,  And[a.b19, b.b05], c_24_5] | 
   let s_24_7 = AdderSum  [s_24_6,  And[a.b18, b.b06], c_24_6] | 
   let s_24_8 = AdderSum  [s_24_7,  And[a.b17, b.b07], c_24_7] | 
   let s_24_9 = AdderSum  [s_24_8,  And[a.b16, b.b08], c_24_8] | 
   let s_24_10 = AdderSum  [s_24_9,  And[a.b15, b.b09], c_24_9] | 
   let s_24_11 = AdderSum  [s_24_10,  And[a.b14, b.b10], c_24_10] | 
   let s_24_12 = AdderSum  [s_24_11,  And[a.b13, b.b11], c_24_11] | 
   let s_24_13 = AdderSum  [s_24_12,  And[a.b12, b.b12], c_24_12] | 
   let s_24_14 = AdderSum  [s_24_13,  And[a.b11, b.b13], c_24_13] | 
   let s_24_15 = AdderSum  [s_24_14,  And[a.b10, b.b14], c_24_14] | 
   let s_24_16 = AdderSum  [s_24_15,  And[a.b09, b.b15], c_24_15] | 
   let s_24_17 = AdderSum  [s_24_16,  And[a.b08, b.b16], c_24_16] | 
   let s_24_18 = AdderSum  [s_24_17,  And[a.b07, b.b17], c_24_17] | 
   let s_24_19 = AdderSum  [s_24_18,  And[a.b06, b.b18], c_24_18] | 
   let s_24_20 = AdderSum  [s_24_19,  And[a.b05, b.b19], c_24_19] | 
   let s_24_21 = AdderSum  [s_24_20,  And[a.b04, b.b20], c_24_20] | 
   let s_24_22 = AdderSum  [s_24_21,  And[a.b03, b.b21], c_24_21] | 
   let s_24_23 = AdderSum  [s_24_22,  And[a.b02, b.b22], c_24_22] | 
   let s_24_24 = AdderSum  [s_24_23,  And[a.b01, b.b23], c_24_23] | 
   let s_24_25 = AdderSum  [s_24_24,  And[a.b00, b.b24], c_24_24] | 
   let c_25_0 = False | 
   let c_25_1 = AdderCarry[s_24_0,  And[a.b24, b.b00], c_24_0] | 
   let c_25_2 = AdderCarry[s_24_1,  And[a.b23, b.b01], c_24_1] | 
   let c_25_3 = AdderCarry[s_24_2,  And[a.b22, b.b02], c_24_2] | 
   let c_25_4 = AdderCarry[s_24_3,  And[a.b21, b.b03], c_24_3] | 
   let c_25_5 = AdderCarry[s_24_4,  And[a.b20, b.b04], c_24_4] | 
   let c_25_6 = AdderCarry[s_24_5,  And[a.b19, b.b05], c_24_5] | 
   let c_25_7 = AdderCarry[s_24_6,  And[a.b18, b.b06], c_24_6] | 
   let c_25_8 = AdderCarry[s_24_7,  And[a.b17, b.b07], c_24_7] | 
   let c_25_9 = AdderCarry[s_24_8,  And[a.b16, b.b08], c_24_8] | 
   let c_25_10 = AdderCarry[s_24_9,  And[a.b15, b.b09], c_24_9] | 
   let c_25_11 = AdderCarry[s_24_10,  And[a.b14, b.b10], c_24_10] | 
   let c_25_12 = AdderCarry[s_24_11,  And[a.b13, b.b11], c_24_11] | 
   let c_25_13 = AdderCarry[s_24_12,  And[a.b12, b.b12], c_24_12] | 
   let c_25_14 = AdderCarry[s_24_13,  And[a.b11, b.b13], c_24_13] | 
   let c_25_15 = AdderCarry[s_24_14,  And[a.b10, b.b14], c_24_14] | 
   let c_25_16 = AdderCarry[s_24_15,  And[a.b09, b.b15], c_24_15] | 
   let c_25_17 = AdderCarry[s_24_16,  And[a.b08, b.b16], c_24_16] | 
   let c_25_18 = AdderCarry[s_24_17,  And[a.b07, b.b17], c_24_17] | 
   let c_25_19 = AdderCarry[s_24_18,  And[a.b06, b.b18], c_24_18] | 
   let c_25_20 = AdderCarry[s_24_19,  And[a.b05, b.b19], c_24_19] | 
   let c_25_21 = AdderCarry[s_24_20,  And[a.b04, b.b20], c_24_20] | 
   let c_25_22 = AdderCarry[s_24_21,  And[a.b03, b.b21], c_24_21] | 
   let c_25_23 = AdderCarry[s_24_22,  And[a.b02, b.b22], c_24_22] | 
   let c_25_24 = AdderCarry[s_24_23,  And[a.b01, b.b23], c_24_23] | 
   let c_25_25 = AdderCarry[s_24_24,  And[a.b00, b.b24], c_24_24] | 
   let s_25_0 = False | 
   let s_25_1 = AdderSum  [s_25_0,  And[a.b25, b.b00], c_25_0] | 
   let s_25_2 = AdderSum  [s_25_1,  And[a.b24, b.b01], c_25_1] | 
   let s_25_3 = AdderSum  [s_25_2,  And[a.b23, b.b02], c_25_2] | 
   let s_25_4 = AdderSum  [s_25_3,  And[a.b22, b.b03], c_25_3] | 
   let s_25_5 = AdderSum  [s_25_4,  And[a.b21, b.b04], c_25_4] | 
   let s_25_6 = AdderSum  [s_25_5,  And[a.b20, b.b05], c_25_5] | 
   let s_25_7 = AdderSum  [s_25_6,  And[a.b19, b.b06], c_25_6] | 
   let s_25_8 = AdderSum  [s_25_7,  And[a.b18, b.b07], c_25_7] | 
   let s_25_9 = AdderSum  [s_25_8,  And[a.b17, b.b08], c_25_8] | 
   let s_25_10 = AdderSum  [s_25_9,  And[a.b16, b.b09], c_25_9] | 
   let s_25_11 = AdderSum  [s_25_10,  And[a.b15, b.b10], c_25_10] | 
   let s_25_12 = AdderSum  [s_25_11,  And[a.b14, b.b11], c_25_11] | 
   let s_25_13 = AdderSum  [s_25_12,  And[a.b13, b.b12], c_25_12] | 
   let s_25_14 = AdderSum  [s_25_13,  And[a.b12, b.b13], c_25_13] | 
   let s_25_15 = AdderSum  [s_25_14,  And[a.b11, b.b14], c_25_14] | 
   let s_25_16 = AdderSum  [s_25_15,  And[a.b10, b.b15], c_25_15] | 
   let s_25_17 = AdderSum  [s_25_16,  And[a.b09, b.b16], c_25_16] | 
   let s_25_18 = AdderSum  [s_25_17,  And[a.b08, b.b17], c_25_17] | 
   let s_25_19 = AdderSum  [s_25_18,  And[a.b07, b.b18], c_25_18] | 
   let s_25_20 = AdderSum  [s_25_19,  And[a.b06, b.b19], c_25_19] | 
   let s_25_21 = AdderSum  [s_25_20,  And[a.b05, b.b20], c_25_20] | 
   let s_25_22 = AdderSum  [s_25_21,  And[a.b04, b.b21], c_25_21] | 
   let s_25_23 = AdderSum  [s_25_22,  And[a.b03, b.b22], c_25_22] | 
   let s_25_24 = AdderSum  [s_25_23,  And[a.b02, b.b23], c_25_23] | 
   let s_25_25 = AdderSum  [s_25_24,  And[a.b01, b.b24], c_25_24] | 
   let s_25_26 = AdderSum  [s_25_25,  And[a.b00, b.b25], c_25_25] | 
   let c_26_0 = False | 
   let c_26_1 = AdderCarry[s_25_0,  And[a.b25, b.b00], c_25_0] | 
   let c_26_2 = AdderCarry[s_25_1,  And[a.b24, b.b01], c_25_1] | 
   let c_26_3 = AdderCarry[s_25_2,  And[a.b23, b.b02], c_25_2] | 
   let c_26_4 = AdderCarry[s_25_3,  And[a.b22, b.b03], c_25_3] | 
   let c_26_5 = AdderCarry[s_25_4,  And[a.b21, b.b04], c_25_4] | 
   let c_26_6 = AdderCarry[s_25_5,  And[a.b20, b.b05], c_25_5] | 
   let c_26_7 = AdderCarry[s_25_6,  And[a.b19, b.b06], c_25_6] | 
   let c_26_8 = AdderCarry[s_25_7,  And[a.b18, b.b07], c_25_7] | 
   let c_26_9 = AdderCarry[s_25_8,  And[a.b17, b.b08], c_25_8] | 
   let c_26_10 = AdderCarry[s_25_9,  And[a.b16, b.b09], c_25_9] | 
   let c_26_11 = AdderCarry[s_25_10,  And[a.b15, b.b10], c_25_10] | 
   let c_26_12 = AdderCarry[s_25_11,  And[a.b14, b.b11], c_25_11] | 
   let c_26_13 = AdderCarry[s_25_12,  And[a.b13, b.b12], c_25_12] | 
   let c_26_14 = AdderCarry[s_25_13,  And[a.b12, b.b13], c_25_13] | 
   let c_26_15 = AdderCarry[s_25_14,  And[a.b11, b.b14], c_25_14] | 
   let c_26_16 = AdderCarry[s_25_15,  And[a.b10, b.b15], c_25_15] | 
   let c_26_17 = AdderCarry[s_25_16,  And[a.b09, b.b16], c_25_16] | 
   let c_26_18 = AdderCarry[s_25_17,  And[a.b08, b.b17], c_25_17] | 
   let c_26_19 = AdderCarry[s_25_18,  And[a.b07, b.b18], c_25_18] | 
   let c_26_20 = AdderCarry[s_25_19,  And[a.b06, b.b19], c_25_19] | 
   let c_26_21 = AdderCarry[s_25_20,  And[a.b05, b.b20], c_25_20] | 
   let c_26_22 = AdderCarry[s_25_21,  And[a.b04, b.b21], c_25_21] | 
   let c_26_23 = AdderCarry[s_25_22,  And[a.b03, b.b22], c_25_22] | 
   let c_26_24 = AdderCarry[s_25_23,  And[a.b02, b.b23], c_25_23] | 
   let c_26_25 = AdderCarry[s_25_24,  And[a.b01, b.b24], c_25_24] | 
   let c_26_26 = AdderCarry[s_25_25,  And[a.b00, b.b25], c_25_25] | 
   let s_26_0 = False | 
   let s_26_1 = AdderSum  [s_26_0,  And[a.b26, b.b00], c_26_0] | 
   let s_26_2 = AdderSum  [s_26_1,  And[a.b25, b.b01], c_26_1] | 
   let s_26_3 = AdderSum  [s_26_2,  And[a.b24, b.b02], c_26_2] | 
   let s_26_4 = AdderSum  [s_26_3,  And[a.b23, b.b03], c_26_3] | 
   let s_26_5 = AdderSum  [s_26_4,  And[a.b22, b.b04], c_26_4] | 
   let s_26_6 = AdderSum  [s_26_5,  And[a.b21, b.b05], c_26_5] | 
   let s_26_7 = AdderSum  [s_26_6,  And[a.b20, b.b06], c_26_6] | 
   let s_26_8 = AdderSum  [s_26_7,  And[a.b19, b.b07], c_26_7] | 
   let s_26_9 = AdderSum  [s_26_8,  And[a.b18, b.b08], c_26_8] | 
   let s_26_10 = AdderSum  [s_26_9,  And[a.b17, b.b09], c_26_9] | 
   let s_26_11 = AdderSum  [s_26_10,  And[a.b16, b.b10], c_26_10] | 
   let s_26_12 = AdderSum  [s_26_11,  And[a.b15, b.b11], c_26_11] | 
   let s_26_13 = AdderSum  [s_26_12,  And[a.b14, b.b12], c_26_12] | 
   let s_26_14 = AdderSum  [s_26_13,  And[a.b13, b.b13], c_26_13] | 
   let s_26_15 = AdderSum  [s_26_14,  And[a.b12, b.b14], c_26_14] | 
   let s_26_16 = AdderSum  [s_26_15,  And[a.b11, b.b15], c_26_15] | 
   let s_26_17 = AdderSum  [s_26_16,  And[a.b10, b.b16], c_26_16] | 
   let s_26_18 = AdderSum  [s_26_17,  And[a.b09, b.b17], c_26_17] | 
   let s_26_19 = AdderSum  [s_26_18,  And[a.b08, b.b18], c_26_18] | 
   let s_26_20 = AdderSum  [s_26_19,  And[a.b07, b.b19], c_26_19] | 
   let s_26_21 = AdderSum  [s_26_20,  And[a.b06, b.b20], c_26_20] | 
   let s_26_22 = AdderSum  [s_26_21,  And[a.b05, b.b21], c_26_21] | 
   let s_26_23 = AdderSum  [s_26_22,  And[a.b04, b.b22], c_26_22] | 
   let s_26_24 = AdderSum  [s_26_23,  And[a.b03, b.b23], c_26_23] | 
   let s_26_25 = AdderSum  [s_26_24,  And[a.b02, b.b24], c_26_24] | 
   let s_26_26 = AdderSum  [s_26_25,  And[a.b01, b.b25], c_26_25] | 
   let s_26_27 = AdderSum  [s_26_26,  And[a.b00, b.b26], c_26_26] | 
   let c_27_0 = False | 
   let c_27_1 = AdderCarry[s_26_0,  And[a.b26, b.b00], c_26_0] | 
   let c_27_2 = AdderCarry[s_26_1,  And[a.b25, b.b01], c_26_1] | 
   let c_27_3 = AdderCarry[s_26_2,  And[a.b24, b.b02], c_26_2] | 
   let c_27_4 = AdderCarry[s_26_3,  And[a.b23, b.b03], c_26_3] | 
   let c_27_5 = AdderCarry[s_26_4,  And[a.b22, b.b04], c_26_4] | 
   let c_27_6 = AdderCarry[s_26_5,  And[a.b21, b.b05], c_26_5] | 
   let c_27_7 = AdderCarry[s_26_6,  And[a.b20, b.b06], c_26_6] | 
   let c_27_8 = AdderCarry[s_26_7,  And[a.b19, b.b07], c_26_7] | 
   let c_27_9 = AdderCarry[s_26_8,  And[a.b18, b.b08], c_26_8] | 
   let c_27_10 = AdderCarry[s_26_9,  And[a.b17, b.b09], c_26_9] | 
   let c_27_11 = AdderCarry[s_26_10,  And[a.b16, b.b10], c_26_10] | 
   let c_27_12 = AdderCarry[s_26_11,  And[a.b15, b.b11], c_26_11] | 
   let c_27_13 = AdderCarry[s_26_12,  And[a.b14, b.b12], c_26_12] | 
   let c_27_14 = AdderCarry[s_26_13,  And[a.b13, b.b13], c_26_13] | 
   let c_27_15 = AdderCarry[s_26_14,  And[a.b12, b.b14], c_26_14] | 
   let c_27_16 = AdderCarry[s_26_15,  And[a.b11, b.b15], c_26_15] | 
   let c_27_17 = AdderCarry[s_26_16,  And[a.b10, b.b16], c_26_16] | 
   let c_27_18 = AdderCarry[s_26_17,  And[a.b09, b.b17], c_26_17] | 
   let c_27_19 = AdderCarry[s_26_18,  And[a.b08, b.b18], c_26_18] | 
   let c_27_20 = AdderCarry[s_26_19,  And[a.b07, b.b19], c_26_19] | 
   let c_27_21 = AdderCarry[s_26_20,  And[a.b06, b.b20], c_26_20] | 
   let c_27_22 = AdderCarry[s_26_21,  And[a.b05, b.b21], c_26_21] | 
   let c_27_23 = AdderCarry[s_26_22,  And[a.b04, b.b22], c_26_22] | 
   let c_27_24 = AdderCarry[s_26_23,  And[a.b03, b.b23], c_26_23] | 
   let c_27_25 = AdderCarry[s_26_24,  And[a.b02, b.b24], c_26_24] | 
   let c_27_26 = AdderCarry[s_26_25,  And[a.b01, b.b25], c_26_25] | 
   let c_27_27 = AdderCarry[s_26_26,  And[a.b00, b.b26], c_26_26] | 
   let s_27_0 = False | 
   let s_27_1 = AdderSum  [s_27_0,  And[a.b27, b.b00], c_27_0] | 
   let s_27_2 = AdderSum  [s_27_1,  And[a.b26, b.b01], c_27_1] | 
   let s_27_3 = AdderSum  [s_27_2,  And[a.b25, b.b02], c_27_2] | 
   let s_27_4 = AdderSum  [s_27_3,  And[a.b24, b.b03], c_27_3] | 
   let s_27_5 = AdderSum  [s_27_4,  And[a.b23, b.b04], c_27_4] | 
   let s_27_6 = AdderSum  [s_27_5,  And[a.b22, b.b05], c_27_5] | 
   let s_27_7 = AdderSum  [s_27_6,  And[a.b21, b.b06], c_27_6] | 
   let s_27_8 = AdderSum  [s_27_7,  And[a.b20, b.b07], c_27_7] | 
   let s_27_9 = AdderSum  [s_27_8,  And[a.b19, b.b08], c_27_8] | 
   let s_27_10 = AdderSum  [s_27_9,  And[a.b18, b.b09], c_27_9] | 
   let s_27_11 = AdderSum  [s_27_10,  And[a.b17, b.b10], c_27_10] | 
   let s_27_12 = AdderSum  [s_27_11,  And[a.b16, b.b11], c_27_11] | 
   let s_27_13 = AdderSum  [s_27_12,  And[a.b15, b.b12], c_27_12] | 
   let s_27_14 = AdderSum  [s_27_13,  And[a.b14, b.b13], c_27_13] | 
   let s_27_15 = AdderSum  [s_27_14,  And[a.b13, b.b14], c_27_14] | 
   let s_27_16 = AdderSum  [s_27_15,  And[a.b12, b.b15], c_27_15] | 
   let s_27_17 = AdderSum  [s_27_16,  And[a.b11, b.b16], c_27_16] | 
   let s_27_18 = AdderSum  [s_27_17,  And[a.b10, b.b17], c_27_17] | 
   let s_27_19 = AdderSum  [s_27_18,  And[a.b09, b.b18], c_27_18] | 
   let s_27_20 = AdderSum  [s_27_19,  And[a.b08, b.b19], c_27_19] | 
   let s_27_21 = AdderSum  [s_27_20,  And[a.b07, b.b20], c_27_20] | 
   let s_27_22 = AdderSum  [s_27_21,  And[a.b06, b.b21], c_27_21] | 
   let s_27_23 = AdderSum  [s_27_22,  And[a.b05, b.b22], c_27_22] | 
   let s_27_24 = AdderSum  [s_27_23,  And[a.b04, b.b23], c_27_23] | 
   let s_27_25 = AdderSum  [s_27_24,  And[a.b03, b.b24], c_27_24] | 
   let s_27_26 = AdderSum  [s_27_25,  And[a.b02, b.b25], c_27_25] | 
   let s_27_27 = AdderSum  [s_27_26,  And[a.b01, b.b26], c_27_26] | 
   let s_27_28 = AdderSum  [s_27_27,  And[a.b00, b.b27], c_27_27] | 
   let c_28_0 = False | 
   let c_28_1 = AdderCarry[s_27_0,  And[a.b27, b.b00], c_27_0] | 
   let c_28_2 = AdderCarry[s_27_1,  And[a.b26, b.b01], c_27_1] | 
   let c_28_3 = AdderCarry[s_27_2,  And[a.b25, b.b02], c_27_2] | 
   let c_28_4 = AdderCarry[s_27_3,  And[a.b24, b.b03], c_27_3] | 
   let c_28_5 = AdderCarry[s_27_4,  And[a.b23, b.b04], c_27_4] | 
   let c_28_6 = AdderCarry[s_27_5,  And[a.b22, b.b05], c_27_5] | 
   let c_28_7 = AdderCarry[s_27_6,  And[a.b21, b.b06], c_27_6] | 
   let c_28_8 = AdderCarry[s_27_7,  And[a.b20, b.b07], c_27_7] | 
   let c_28_9 = AdderCarry[s_27_8,  And[a.b19, b.b08], c_27_8] | 
   let c_28_10 = AdderCarry[s_27_9,  And[a.b18, b.b09], c_27_9] | 
   let c_28_11 = AdderCarry[s_27_10,  And[a.b17, b.b10], c_27_10] | 
   let c_28_12 = AdderCarry[s_27_11,  And[a.b16, b.b11], c_27_11] | 
   let c_28_13 = AdderCarry[s_27_12,  And[a.b15, b.b12], c_27_12] | 
   let c_28_14 = AdderCarry[s_27_13,  And[a.b14, b.b13], c_27_13] | 
   let c_28_15 = AdderCarry[s_27_14,  And[a.b13, b.b14], c_27_14] | 
   let c_28_16 = AdderCarry[s_27_15,  And[a.b12, b.b15], c_27_15] | 
   let c_28_17 = AdderCarry[s_27_16,  And[a.b11, b.b16], c_27_16] | 
   let c_28_18 = AdderCarry[s_27_17,  And[a.b10, b.b17], c_27_17] | 
   let c_28_19 = AdderCarry[s_27_18,  And[a.b09, b.b18], c_27_18] | 
   let c_28_20 = AdderCarry[s_27_19,  And[a.b08, b.b19], c_27_19] | 
   let c_28_21 = AdderCarry[s_27_20,  And[a.b07, b.b20], c_27_20] | 
   let c_28_22 = AdderCarry[s_27_21,  And[a.b06, b.b21], c_27_21] | 
   let c_28_23 = AdderCarry[s_27_22,  And[a.b05, b.b22], c_27_22] | 
   let c_28_24 = AdderCarry[s_27_23,  And[a.b04, b.b23], c_27_23] | 
   let c_28_25 = AdderCarry[s_27_24,  And[a.b03, b.b24], c_27_24] | 
   let c_28_26 = AdderCarry[s_27_25,  And[a.b02, b.b25], c_27_25] | 
   let c_28_27 = AdderCarry[s_27_26,  And[a.b01, b.b26], c_27_26] | 
   let c_28_28 = AdderCarry[s_27_27,  And[a.b00, b.b27], c_27_27] | 
   let s_28_0 = False | 
   let s_28_1 = AdderSum  [s_28_0,  And[a.b28, b.b00], c_28_0] | 
   let s_28_2 = AdderSum  [s_28_1,  And[a.b27, b.b01], c_28_1] | 
   let s_28_3 = AdderSum  [s_28_2,  And[a.b26, b.b02], c_28_2] | 
   let s_28_4 = AdderSum  [s_28_3,  And[a.b25, b.b03], c_28_3] | 
   let s_28_5 = AdderSum  [s_28_4,  And[a.b24, b.b04], c_28_4] | 
   let s_28_6 = AdderSum  [s_28_5,  And[a.b23, b.b05], c_28_5] | 
   let s_28_7 = AdderSum  [s_28_6,  And[a.b22, b.b06], c_28_6] | 
   let s_28_8 = AdderSum  [s_28_7,  And[a.b21, b.b07], c_28_7] | 
   let s_28_9 = AdderSum  [s_28_8,  And[a.b20, b.b08], c_28_8] | 
   let s_28_10 = AdderSum  [s_28_9,  And[a.b19, b.b09], c_28_9] | 
   let s_28_11 = AdderSum  [s_28_10,  And[a.b18, b.b10], c_28_10] | 
   let s_28_12 = AdderSum  [s_28_11,  And[a.b17, b.b11], c_28_11] | 
   let s_28_13 = AdderSum  [s_28_12,  And[a.b16, b.b12], c_28_12] | 
   let s_28_14 = AdderSum  [s_28_13,  And[a.b15, b.b13], c_28_13] | 
   let s_28_15 = AdderSum  [s_28_14,  And[a.b14, b.b14], c_28_14] | 
   let s_28_16 = AdderSum  [s_28_15,  And[a.b13, b.b15], c_28_15] | 
   let s_28_17 = AdderSum  [s_28_16,  And[a.b12, b.b16], c_28_16] | 
   let s_28_18 = AdderSum  [s_28_17,  And[a.b11, b.b17], c_28_17] | 
   let s_28_19 = AdderSum  [s_28_18,  And[a.b10, b.b18], c_28_18] | 
   let s_28_20 = AdderSum  [s_28_19,  And[a.b09, b.b19], c_28_19] | 
   let s_28_21 = AdderSum  [s_28_20,  And[a.b08, b.b20], c_28_20] | 
   let s_28_22 = AdderSum  [s_28_21,  And[a.b07, b.b21], c_28_21] | 
   let s_28_23 = AdderSum  [s_28_22,  And[a.b06, b.b22], c_28_22] | 
   let s_28_24 = AdderSum  [s_28_23,  And[a.b05, b.b23], c_28_23] | 
   let s_28_25 = AdderSum  [s_28_24,  And[a.b04, b.b24], c_28_24] | 
   let s_28_26 = AdderSum  [s_28_25,  And[a.b03, b.b25], c_28_25] | 
   let s_28_27 = AdderSum  [s_28_26,  And[a.b02, b.b26], c_28_26] | 
   let s_28_28 = AdderSum  [s_28_27,  And[a.b01, b.b27], c_28_27] | 
   let s_28_29 = AdderSum  [s_28_28,  And[a.b00, b.b28], c_28_28] | 
   let c_29_0 = False | 
   let c_29_1 = AdderCarry[s_28_0,  And[a.b28, b.b00], c_28_0] | 
   let c_29_2 = AdderCarry[s_28_1,  And[a.b27, b.b01], c_28_1] | 
   let c_29_3 = AdderCarry[s_28_2,  And[a.b26, b.b02], c_28_2] | 
   let c_29_4 = AdderCarry[s_28_3,  And[a.b25, b.b03], c_28_3] | 
   let c_29_5 = AdderCarry[s_28_4,  And[a.b24, b.b04], c_28_4] | 
   let c_29_6 = AdderCarry[s_28_5,  And[a.b23, b.b05], c_28_5] | 
   let c_29_7 = AdderCarry[s_28_6,  And[a.b22, b.b06], c_28_6] | 
   let c_29_8 = AdderCarry[s_28_7,  And[a.b21, b.b07], c_28_7] | 
   let c_29_9 = AdderCarry[s_28_8,  And[a.b20, b.b08], c_28_8] | 
   let c_29_10 = AdderCarry[s_28_9,  And[a.b19, b.b09], c_28_9] | 
   let c_29_11 = AdderCarry[s_28_10,  And[a.b18, b.b10], c_28_10] | 
   let c_29_12 = AdderCarry[s_28_11,  And[a.b17, b.b11], c_28_11] | 
   let c_29_13 = AdderCarry[s_28_12,  And[a.b16, b.b12], c_28_12] | 
   let c_29_14 = AdderCarry[s_28_13,  And[a.b15, b.b13], c_28_13] | 
   let c_29_15 = AdderCarry[s_28_14,  And[a.b14, b.b14], c_28_14] | 
   let c_29_16 = AdderCarry[s_28_15,  And[a.b13, b.b15], c_28_15] | 
   let c_29_17 = AdderCarry[s_28_16,  And[a.b12, b.b16], c_28_16] | 
   let c_29_18 = AdderCarry[s_28_17,  And[a.b11, b.b17], c_28_17] | 
   let c_29_19 = AdderCarry[s_28_18,  And[a.b10, b.b18], c_28_18] | 
   let c_29_20 = AdderCarry[s_28_19,  And[a.b09, b.b19], c_28_19] | 
   let c_29_21 = AdderCarry[s_28_20,  And[a.b08, b.b20], c_28_20] | 
   let c_29_22 = AdderCarry[s_28_21,  And[a.b07, b.b21], c_28_21] | 
   let c_29_23 = AdderCarry[s_28_22,  And[a.b06, b.b22], c_28_22] | 
   let c_29_24 = AdderCarry[s_28_23,  And[a.b05, b.b23], c_28_23] | 
   let c_29_25 = AdderCarry[s_28_24,  And[a.b04, b.b24], c_28_24] | 
   let c_29_26 = AdderCarry[s_28_25,  And[a.b03, b.b25], c_28_25] | 
   let c_29_27 = AdderCarry[s_28_26,  And[a.b02, b.b26], c_28_26] | 
   let c_29_28 = AdderCarry[s_28_27,  And[a.b01, b.b27], c_28_27] | 
   let c_29_29 = AdderCarry[s_28_28,  And[a.b00, b.b28], c_28_28] | 
   let s_29_0 = False | 
   let s_29_1 = AdderSum  [s_29_0,  And[a.b29, b.b00], c_29_0] | 
   let s_29_2 = AdderSum  [s_29_1,  And[a.b28, b.b01], c_29_1] | 
   let s_29_3 = AdderSum  [s_29_2,  And[a.b27, b.b02], c_29_2] | 
   let s_29_4 = AdderSum  [s_29_3,  And[a.b26, b.b03], c_29_3] | 
   let s_29_5 = AdderSum  [s_29_4,  And[a.b25, b.b04], c_29_4] | 
   let s_29_6 = AdderSum  [s_29_5,  And[a.b24, b.b05], c_29_5] | 
   let s_29_7 = AdderSum  [s_29_6,  And[a.b23, b.b06], c_29_6] | 
   let s_29_8 = AdderSum  [s_29_7,  And[a.b22, b.b07], c_29_7] | 
   let s_29_9 = AdderSum  [s_29_8,  And[a.b21, b.b08], c_29_8] | 
   let s_29_10 = AdderSum  [s_29_9,  And[a.b20, b.b09], c_29_9] | 
   let s_29_11 = AdderSum  [s_29_10,  And[a.b19, b.b10], c_29_10] | 
   let s_29_12 = AdderSum  [s_29_11,  And[a.b18, b.b11], c_29_11] | 
   let s_29_13 = AdderSum  [s_29_12,  And[a.b17, b.b12], c_29_12] | 
   let s_29_14 = AdderSum  [s_29_13,  And[a.b16, b.b13], c_29_13] | 
   let s_29_15 = AdderSum  [s_29_14,  And[a.b15, b.b14], c_29_14] | 
   let s_29_16 = AdderSum  [s_29_15,  And[a.b14, b.b15], c_29_15] | 
   let s_29_17 = AdderSum  [s_29_16,  And[a.b13, b.b16], c_29_16] | 
   let s_29_18 = AdderSum  [s_29_17,  And[a.b12, b.b17], c_29_17] | 
   let s_29_19 = AdderSum  [s_29_18,  And[a.b11, b.b18], c_29_18] | 
   let s_29_20 = AdderSum  [s_29_19,  And[a.b10, b.b19], c_29_19] | 
   let s_29_21 = AdderSum  [s_29_20,  And[a.b09, b.b20], c_29_20] | 
   let s_29_22 = AdderSum  [s_29_21,  And[a.b08, b.b21], c_29_21] | 
   let s_29_23 = AdderSum  [s_29_22,  And[a.b07, b.b22], c_29_22] | 
   let s_29_24 = AdderSum  [s_29_23,  And[a.b06, b.b23], c_29_23] | 
   let s_29_25 = AdderSum  [s_29_24,  And[a.b05, b.b24], c_29_24] | 
   let s_29_26 = AdderSum  [s_29_25,  And[a.b04, b.b25], c_29_25] | 
   let s_29_27 = AdderSum  [s_29_26,  And[a.b03, b.b26], c_29_26] | 
   let s_29_28 = AdderSum  [s_29_27,  And[a.b02, b.b27], c_29_27] | 
   let s_29_29 = AdderSum  [s_29_28,  And[a.b01, b.b28], c_29_28] | 
   let s_29_30 = AdderSum  [s_29_29,  And[a.b00, b.b29], c_29_29] | 
   let c_30_0 = False | 
   let c_30_1 = AdderCarry[s_29_0,  And[a.b29, b.b00], c_29_0] | 
   let c_30_2 = AdderCarry[s_29_1,  And[a.b28, b.b01], c_29_1] | 
   let c_30_3 = AdderCarry[s_29_2,  And[a.b27, b.b02], c_29_2] | 
   let c_30_4 = AdderCarry[s_29_3,  And[a.b26, b.b03], c_29_3] | 
   let c_30_5 = AdderCarry[s_29_4,  And[a.b25, b.b04], c_29_4] | 
   let c_30_6 = AdderCarry[s_29_5,  And[a.b24, b.b05], c_29_5] | 
   let c_30_7 = AdderCarry[s_29_6,  And[a.b23, b.b06], c_29_6] | 
   let c_30_8 = AdderCarry[s_29_7,  And[a.b22, b.b07], c_29_7] | 
   let c_30_9 = AdderCarry[s_29_8,  And[a.b21, b.b08], c_29_8] | 
   let c_30_10 = AdderCarry[s_29_9,  And[a.b20, b.b09], c_29_9] | 
   let c_30_11 = AdderCarry[s_29_10,  And[a.b19, b.b10], c_29_10] | 
   let c_30_12 = AdderCarry[s_29_11,  And[a.b18, b.b11], c_29_11] | 
   let c_30_13 = AdderCarry[s_29_12,  And[a.b17, b.b12], c_29_12] | 
   let c_30_14 = AdderCarry[s_29_13,  And[a.b16, b.b13], c_29_13] | 
   let c_30_15 = AdderCarry[s_29_14,  And[a.b15, b.b14], c_29_14] | 
   let c_30_16 = AdderCarry[s_29_15,  And[a.b14, b.b15], c_29_15] | 
   let c_30_17 = AdderCarry[s_29_16,  And[a.b13, b.b16], c_29_16] | 
   let c_30_18 = AdderCarry[s_29_17,  And[a.b12, b.b17], c_29_17] | 
   let c_30_19 = AdderCarry[s_29_18,  And[a.b11, b.b18], c_29_18] | 
   let c_30_20 = AdderCarry[s_29_19,  And[a.b10, b.b19], c_29_19] | 
   let c_30_21 = AdderCarry[s_29_20,  And[a.b09, b.b20], c_29_20] | 
   let c_30_22 = AdderCarry[s_29_21,  And[a.b08, b.b21], c_29_21] | 
   let c_30_23 = AdderCarry[s_29_22,  And[a.b07, b.b22], c_29_22] | 
   let c_30_24 = AdderCarry[s_29_23,  And[a.b06, b.b23], c_29_23] | 
   let c_30_25 = AdderCarry[s_29_24,  And[a.b05, b.b24], c_29_24] | 
   let c_30_26 = AdderCarry[s_29_25,  And[a.b04, b.b25], c_29_25] | 
   let c_30_27 = AdderCarry[s_29_26,  And[a.b03, b.b26], c_29_26] | 
   let c_30_28 = AdderCarry[s_29_27,  And[a.b02, b.b27], c_29_27] | 
   let c_30_29 = AdderCarry[s_29_28,  And[a.b01, b.b28], c_29_28] | 
   let c_30_30 = AdderCarry[s_29_29,  And[a.b00, b.b29], c_29_29] | 
   let s_30_0 = False | 
   let s_30_1 = AdderSum  [s_30_0,  And[a.b30, b.b00], c_30_0] | 
   let s_30_2 = AdderSum  [s_30_1,  And[a.b29, b.b01], c_30_1] | 
   let s_30_3 = AdderSum  [s_30_2,  And[a.b28, b.b02], c_30_2] | 
   let s_30_4 = AdderSum  [s_30_3,  And[a.b27, b.b03], c_30_3] | 
   let s_30_5 = AdderSum  [s_30_4,  And[a.b26, b.b04], c_30_4] | 
   let s_30_6 = AdderSum  [s_30_5,  And[a.b25, b.b05], c_30_5] | 
   let s_30_7 = AdderSum  [s_30_6,  And[a.b24, b.b06], c_30_6] | 
   let s_30_8 = AdderSum  [s_30_7,  And[a.b23, b.b07], c_30_7] | 
   let s_30_9 = AdderSum  [s_30_8,  And[a.b22, b.b08], c_30_8] | 
   let s_30_10 = AdderSum  [s_30_9,  And[a.b21, b.b09], c_30_9] | 
   let s_30_11 = AdderSum  [s_30_10,  And[a.b20, b.b10], c_30_10] | 
   let s_30_12 = AdderSum  [s_30_11,  And[a.b19, b.b11], c_30_11] | 
   let s_30_13 = AdderSum  [s_30_12,  And[a.b18, b.b12], c_30_12] | 
   let s_30_14 = AdderSum  [s_30_13,  And[a.b17, b.b13], c_30_13] | 
   let s_30_15 = AdderSum  [s_30_14,  And[a.b16, b.b14], c_30_14] | 
   let s_30_16 = AdderSum  [s_30_15,  And[a.b15, b.b15], c_30_15] | 
   let s_30_17 = AdderSum  [s_30_16,  And[a.b14, b.b16], c_30_16] | 
   let s_30_18 = AdderSum  [s_30_17,  And[a.b13, b.b17], c_30_17] | 
   let s_30_19 = AdderSum  [s_30_18,  And[a.b12, b.b18], c_30_18] | 
   let s_30_20 = AdderSum  [s_30_19,  And[a.b11, b.b19], c_30_19] | 
   let s_30_21 = AdderSum  [s_30_20,  And[a.b10, b.b20], c_30_20] | 
   let s_30_22 = AdderSum  [s_30_21,  And[a.b09, b.b21], c_30_21] | 
   let s_30_23 = AdderSum  [s_30_22,  And[a.b08, b.b22], c_30_22] | 
   let s_30_24 = AdderSum  [s_30_23,  And[a.b07, b.b23], c_30_23] | 
   let s_30_25 = AdderSum  [s_30_24,  And[a.b06, b.b24], c_30_24] | 
   let s_30_26 = AdderSum  [s_30_25,  And[a.b05, b.b25], c_30_25] | 
   let s_30_27 = AdderSum  [s_30_26,  And[a.b04, b.b26], c_30_26] | 
   let s_30_28 = AdderSum  [s_30_27,  And[a.b03, b.b27], c_30_27] | 
   let s_30_29 = AdderSum  [s_30_28,  And[a.b02, b.b28], c_30_28] | 
   let s_30_30 = AdderSum  [s_30_29,  And[a.b01, b.b29], c_30_29] | 
   let s_30_31 = AdderSum  [s_30_30,  And[a.b00, b.b30], c_30_30] | 
   let c_31_0 = False | 
   let c_31_1 = AdderCarry[s_30_0,  And[a.b30, b.b00], c_30_0] | 
   let c_31_2 = AdderCarry[s_30_1,  And[a.b29, b.b01], c_30_1] | 
   let c_31_3 = AdderCarry[s_30_2,  And[a.b28, b.b02], c_30_2] | 
   let c_31_4 = AdderCarry[s_30_3,  And[a.b27, b.b03], c_30_3] | 
   let c_31_5 = AdderCarry[s_30_4,  And[a.b26, b.b04], c_30_4] | 
   let c_31_6 = AdderCarry[s_30_5,  And[a.b25, b.b05], c_30_5] | 
   let c_31_7 = AdderCarry[s_30_6,  And[a.b24, b.b06], c_30_6] | 
   let c_31_8 = AdderCarry[s_30_7,  And[a.b23, b.b07], c_30_7] | 
   let c_31_9 = AdderCarry[s_30_8,  And[a.b22, b.b08], c_30_8] | 
   let c_31_10 = AdderCarry[s_30_9,  And[a.b21, b.b09], c_30_9] | 
   let c_31_11 = AdderCarry[s_30_10,  And[a.b20, b.b10], c_30_10] | 
   let c_31_12 = AdderCarry[s_30_11,  And[a.b19, b.b11], c_30_11] | 
   let c_31_13 = AdderCarry[s_30_12,  And[a.b18, b.b12], c_30_12] | 
   let c_31_14 = AdderCarry[s_30_13,  And[a.b17, b.b13], c_30_13] | 
   let c_31_15 = AdderCarry[s_30_14,  And[a.b16, b.b14], c_30_14] | 
   let c_31_16 = AdderCarry[s_30_15,  And[a.b15, b.b15], c_30_15] | 
   let c_31_17 = AdderCarry[s_30_16,  And[a.b14, b.b16], c_30_16] | 
   let c_31_18 = AdderCarry[s_30_17,  And[a.b13, b.b17], c_30_17] | 
   let c_31_19 = AdderCarry[s_30_18,  And[a.b12, b.b18], c_30_18] | 
   let c_31_20 = AdderCarry[s_30_19,  And[a.b11, b.b19], c_30_19] | 
   let c_31_21 = AdderCarry[s_30_20,  And[a.b10, b.b20], c_30_20] | 
   let c_31_22 = AdderCarry[s_30_21,  And[a.b09, b.b21], c_30_21] | 
   let c_31_23 = AdderCarry[s_30_22,  And[a.b08, b.b22], c_30_22] | 
   let c_31_24 = AdderCarry[s_30_23,  And[a.b07, b.b23], c_30_23] | 
   let c_31_25 = AdderCarry[s_30_24,  And[a.b06, b.b24], c_30_24] | 
   let c_31_26 = AdderCarry[s_30_25,  And[a.b05, b.b25], c_30_25] | 
   let c_31_27 = AdderCarry[s_30_26,  And[a.b04, b.b26], c_30_26] | 
   let c_31_28 = AdderCarry[s_30_27,  And[a.b03, b.b27], c_30_27] | 
   let c_31_29 = AdderCarry[s_30_28,  And[a.b02, b.b28], c_30_28] | 
   let c_31_30 = AdderCarry[s_30_29,  And[a.b01, b.b29], c_30_29] | 
   let c_31_31 = AdderCarry[s_30_30,  And[a.b00, b.b30], c_30_30] | 
   let s_31_0 = False | 
   let s_31_1 = AdderSum  [s_31_0,  And[a.b31, b.b00], c_31_0] | 
   let s_31_2 = AdderSum  [s_31_1,  And[a.b30, b.b01], c_31_1] | 
   let s_31_3 = AdderSum  [s_31_2,  And[a.b29, b.b02], c_31_2] | 
   let s_31_4 = AdderSum  [s_31_3,  And[a.b28, b.b03], c_31_3] | 
   let s_31_5 = AdderSum  [s_31_4,  And[a.b27, b.b04], c_31_4] | 
   let s_31_6 = AdderSum  [s_31_5,  And[a.b26, b.b05], c_31_5] | 
   let s_31_7 = AdderSum  [s_31_6,  And[a.b25, b.b06], c_31_6] | 
   let s_31_8 = AdderSum  [s_31_7,  And[a.b24, b.b07], c_31_7] | 
   let s_31_9 = AdderSum  [s_31_8,  And[a.b23, b.b08], c_31_8] | 
   let s_31_10 = AdderSum  [s_31_9,  And[a.b22, b.b09], c_31_9] | 
   let s_31_11 = AdderSum  [s_31_10,  And[a.b21, b.b10], c_31_10] | 
   let s_31_12 = AdderSum  [s_31_11,  And[a.b20, b.b11], c_31_11] | 
   let s_31_13 = AdderSum  [s_31_12,  And[a.b19, b.b12], c_31_12] | 
   let s_31_14 = AdderSum  [s_31_13,  And[a.b18, b.b13], c_31_13] | 
   let s_31_15 = AdderSum  [s_31_14,  And[a.b17, b.b14], c_31_14] | 
   let s_31_16 = AdderSum  [s_31_15,  And[a.b16, b.b15], c_31_15] | 
   let s_31_17 = AdderSum  [s_31_16,  And[a.b15, b.b16], c_31_16] | 
   let s_31_18 = AdderSum  [s_31_17,  And[a.b14, b.b17], c_31_17] | 
   let s_31_19 = AdderSum  [s_31_18,  And[a.b13, b.b18], c_31_18] | 
   let s_31_20 = AdderSum  [s_31_19,  And[a.b12, b.b19], c_31_19] | 
   let s_31_21 = AdderSum  [s_31_20,  And[a.b11, b.b20], c_31_20] | 
   let s_31_22 = AdderSum  [s_31_21,  And[a.b10, b.b21], c_31_21] | 
   let s_31_23 = AdderSum  [s_31_22,  And[a.b09, b.b22], c_31_22] | 
   let s_31_24 = AdderSum  [s_31_23,  And[a.b08, b.b23], c_31_23] | 
   let s_31_25 = AdderSum  [s_31_24,  And[a.b07, b.b24], c_31_24] | 
   let s_31_26 = AdderSum  [s_31_25,  And[a.b06, b.b25], c_31_25] | 
   let s_31_27 = AdderSum  [s_31_26,  And[a.b05, b.b26], c_31_26] | 
   let s_31_28 = AdderSum  [s_31_27,  And[a.b04, b.b27], c_31_27] | 
   let s_31_29 = AdderSum  [s_31_28,  And[a.b03, b.b28], c_31_28] | 
   let s_31_30 = AdderSum  [s_31_29,  And[a.b02, b.b29], c_31_29] | 
   let s_31_31 = AdderSum  [s_31_30,  And[a.b01, b.b30], c_31_30] | 
   let s_31_32 = AdderSum  [s_31_31,  And[a.b00, b.b31], c_31_31] | 
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
      result.b15 = s_15_16  and
      result.b16 = s_16_17  and
      result.b17 = s_17_18  and
      result.b18 = s_18_19  and
      result.b19 = s_19_20  and
      result.b20 = s_20_21  and
      result.b21 = s_21_22  and
      result.b22 = s_22_23  and
      result.b23 = s_23_24  and
      result.b24 = s_24_25  and
      result.b25 = s_25_26  and
      result.b26 = s_26_27  and
      result.b27 = s_27_28  and
      result.b28 = s_28_29  and
      result.b29 = s_29_30  and
      result.b30 = s_30_31  and
      result.b31 = s_31_32 
}

//A simple example
/*
one sig N32_633333 extends Number32 {} {
	b00 in True
	b01 in False
	b02 in True
	b03 in False
	b04 in True
	b05 in True
	b06 in True
	b07 in True
	b08 in True
	b09 in False
	b10 in False
	b11 in True
	b12 in False
	b13 in True
	b14 in False
	b15 in True
	b16 in True
	b17 in False
	b18 in False
	b19 in True
	b20 in False
	b21 in False
	b22 in False
	b23 in False
	b24 in False
	b25 in False
	b26 in False
	b27 in False
	b28 in False
	b29 in False
	b30 in False
	b31 in False
}

one sig N32_0 extends Number32 {} {
	b00 in False
	b01 in False
	b02 in False
	b03 in False
	b04 in False
	b05 in False
	b06 in False
	b07 in False
	b08 in False
	b09 in False
	b10 in False
	b11 in False
	b12 in False
	b13 in False
	b14 in False
	b15 in False
	b16 in False
	b17 in False
	b18 in False
	b19 in False
	b20 in False
	b21 in False
	b22 in False
	b23 in False
	b24 in False
	b25 in False
	b26 in False
	b27 in False
	b28 in False
	b29 in False
	b30 in False
	b31 in False
}


one sig X {
	x1,x2,x3,x4,x5,x6,x7,x8,x9,x10 : Number32,
    t1, t2, t3, t4, t5, t6, t7, t8, t9, t10: Number32,
   s1,s2,s3,s4,s5,s6,s7,s8,s9: Number32
}


run {
	Mul[X.x1, X.x1, X.t1] 
	Mul[X.x2, X.x2, X.t2] 
	Mul[X.x3, X.x3, X.t3] 
	Mul[X.x4, X.x4, X.t4] 
	Mul[X.x5, X.x5, X.t5] 
	Mul[X.x6, X.x6, X.t6] 
	Mul[X.x7, X.x7, X.t7] 
	Mul[X.x8, X.x8, X.t8] 
	Mul[X.x9, X.x9, X.t9] 
	Mul[X.x10, X.x10, X.t10] 
	Sum[X.t1, X.t2, X.s1]
	Sum[X.t3, X.s1, X.s2]
	Sum[X.t4, X.s2, X.s3]
	Sum[X.t5, X.s3, X.s4]
	Sum[X.t6, X.s4, X.s5]
	Sum[X.t7, X.s5, X.s6]
	Sum[X.t8, X.s6, X.s7]
	Sum[X.t9, X.s7, X.s8]
	Sum[X.t10, X.s8, X.s9]
	eq[X.s9, N32_633333]
} for 30 Number32*/
