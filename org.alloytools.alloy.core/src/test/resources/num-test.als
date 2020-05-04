open util/int8bits

sig A {
    tick : Int
}

sig B {
    field : Number8
}{
    field.b00 = True
}

pred prueba [a, b: Int]{
    eq[a,10]
}