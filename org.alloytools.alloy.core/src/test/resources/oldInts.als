open util/int8bits

sig OldNum {
	field : Int
}

/*
pred prueba[a: A, b: A]{
	eq[a.field,b]
}
*/

pred prueba[a: OldNum, b: OldNum]{
    eq[a.field, b.field]
}

run prueba