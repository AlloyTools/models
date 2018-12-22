// Example of how to create basic boolean logic circuits. Starting with the
// definition of basic boolean operations we build a half-adder and then
// a 4-bit full adder using 4 registers: 2 summands, 1 sum, 1 carry

// https://dev.to/davidk01/some-more-fun-with-alloy-5d7h

// 0 or 1
let bits = { i: Int | 0 <= i && i <= 1 }

// Or
let bitOrTable = { i: bits, j: bits, k: sum[i + j] }

// And
let bitAndTable = { i: bits, j: bits, k: mul[i, j] }

// Not
let bitNotTable = { i: bits, j: minus[1, i] }

// Xor: https://en.wikipedia.org/wiki/Exclusive_or
let bitXorTable = {
  i: bits,
  j: bits,
  k: bitAndTable[bitOrTable[i, j], bitNotTable[bitAndTable[i, j]]]
}

// Half adder: https://en.wikipedia.org/wiki/Adder_(electronics)#Half_adder
pred halfAdder(m: Int, n: Int, s: Int, c: Int) {
  s = bitXorTable[m, n]
  c = bitAndTable[m, n]
}

// https://en.wikipedia.org/wiki/Adder_(electronics)#/media/File:Full-adder_logic_diagram.svg
pred fullAdder(m: Int, n: Int, c: Int, s: Int, carry: Int) {
  let xor = bitXorTable[m, n] {
    s = bitXorTable[xor, c]
    carry = bitOrTable[bitAndTable[m, n], bitAndTable[xor, c]]
  }
}

// BitVector consists of 4 bits
abstract sig BitVector {
  values: (0 + 1 + 2 + 3) -> one bits
}

// We want 4 vectors to perform a computation: 2 summands, sum, and carry
one sig A, B, C, S extends BitVector { }

// 4 bit adder with overflow
pred bitAddition(a: BitVector, b: BitVector, c: BitVector, s: BitVector) {
  fullAdder[a.values[0], b.values[0], 0, s.values[0], c.values[0]]
  fullAdder[a.values[1], b.values[1], c.values[0], s.values[1], c.values[1]]
  fullAdder[a.values[2], b.values[2], c.values[1], s.values[2], c.values[2]]
  fullAdder[a.values[3], b.values[3], c.values[2], s.values[3], c.values[3]]
}

// Run it to verify
run {
  bitAddition[A, B, C, S]
}
