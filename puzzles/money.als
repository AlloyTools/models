// https://dev.to/davidk01/fun-with-alloy-model-checker-2d9b
// SEND + MORE = MONEY

// Non-negative numbers
abstract sig Num { val: Int } { val >= 0 && val <= 9 }

// Digits
one sig S, E, N, D, M, O, R, Y extends Num { }

// Digits must all be different and in 0..9
fact {
  all m, n : Num | m !=n => n.val != m.val
}

// Function for computing the sum and the carry at the same time
fun sumCarry(a: Num, b: Num): (Int -> Int) {
  let s = a.val + b.val |
    s -> (s > 9 => 1 else 0)
}

fun fst(t: (Int -> Int)): Int {
  t.univ
}

fun snd(t: (Int -> Int)): Int {
  univ.t
}

fun val(a: (Int -> Int), b: (Int -> Int)): Int {
  rem[plus[fst[a], snd[b]], 10]
}

// Constraints for SEND + MORE = MONEY
fact {
  M.val > 0
  S.val > 0
  let YSumCarry = sumCarry[D, E], 
    ESumCarry = sumCarry[N, R],
    NSumCarry = sumCarry[E, O],
    OSumCarry = sumCarry[S, M] |
    Y.val = rem[fst[YSumCarry], 10] &&
    E.val = val[ESumCarry, YSumCarry] &&
    N.val = val[NSumCarry, ESumCarry] &&
    O.val = val[OSumCarry, NSumCarry] &&
    M.val = snd[OSumCarry]
}

run { } for 5 Int
