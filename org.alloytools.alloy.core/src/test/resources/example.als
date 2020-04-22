open util/int8bits
sig account {
	balance: Number8
}

one sig ten extends Number8{
}{
	b00 = False and
	b01 = True and
	b02 = False and
	b03 = True and
	b04 = False and
	b05 = False and
	b06 = False and
	b07 = False
}

one sig fifty extends Number8{
}{
	b00 = False and
	b01 = True and
	b02 = False and
	b03 = False and
	b04 = True and
	b05 = True and
	b06 = False and
	b07 = False
}

one sig fourty extends Number8{
}{
	b00 = False and
	b01 = False and
	b02 = False and
	b03 = True and
	b04 = False and
	b05 = True and
	b06 = False and
	b07 = False
}


fact{
	all a : account | nonneg[a.balance]
}

/*sig Number{
	value : Int
}*/
/*
action withdraw [amount : Number8, a : account]{
	pre {gte[a.balance, amount]}
	post {a'.balance = minus[a.balance, amount]}
}
*/
pred withdraw [amount: Number8, a,a': account]{
gte[a.balance, amount] and a'.balance = minus[a.balance,amount]
}
/*
action deposit [amount : Number8, a : account]{
	pre {}
	post {a'.balance = plus[a.balance, amount]}
}

action transference [from, to : account, amount : Number8]{
	pre {gte[from.balance, amount]}
	post {from'.balance = minus[from.balance, amount] and
		 to'.balance = plus[to.balance, amount]}
}
*/
/*pred num10[a : Number8]{
	a.b00 = False and
	a.b01 = True and
	a.b02 = False and
	a.b03 = True and
	a.b04 = False and
	a.b05 = False and
	a.b06 = False and
	a.b07 = False
}*/

/*pred num50[a : Number8]{
	a.b00 = False and
	a.b01 = True and
	a.b02 = False and
	a.b03 = False and
	a.b04 = True and
	a.b05 = True and
	a.b06 = False and
	a.b07 = False
}*/

/*pred num40[a : Number8]{
	a.b00 = False and
	a.b01 = False and
	a.b02 = False and
	a.b03 = True and
	a.b04 = False and
	a.b05 = True and
	a.b06 = False and
	a.b07 = False
}*/
/*
assertCorrectness balanceDue [a: account, n1, n2, n3 : Number8]{
	pre{eq[a.balance, fifty]}
	program{
		withdraw[ten,a]
	}
	post{lt[a'.balance, a.balance] and eq[a'.balance, fourty]}
}
*/
assert balanceDue{
let a = account | let a' = account |
eq[a.balance, fifty] and withdraw[ten,a,a'] and lt[a'.balance, a.balance] and eq[a'.balance, fourty]
}

check balanceDue
/*
assertCorrectness prueba [a, b: account, n1, n2, n3, n4, n5, n6 : Number8]{
	pre{!eq[a.balance, b.balance]}
	program{
		(withdraw[n1,a] + withdraw[n2,b] +
		deposit[n3,a] + deposit[n4,b]+ 
		transference[a,b,n5] + transference[a,b,n6]
		)*
	}
	post{eq[a.balance, b.balance]}
}

check balanceDue for 4 Int
*/

//check prueba for 4 lurs 10
