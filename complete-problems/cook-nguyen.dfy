predicate ValidStr(s : seq<bool>) {
  |s| == 0 || s[|s| - 1]
}

// B1. x + 1 != 0
lemma B1()
  ensures forall x : nat {:trigger x + 1} :: x + 1 != 0 {}

// B2. x + 1 = y + 1 => x = y
lemma B2()
  ensures forall x: nat {:trigger x + 1}, y: nat :: x + 1 == y + 1 ==> x == y {}

// B3. x + 0 = x
lemma B3()
  ensures forall x: nat :: x + 0 == x {}

// B4. x + (y + 1) = (x + y) + 1
lemma B4()
  ensures forall x: nat, y: nat :: x + (y + 1) == (x + y) + 1 {}

// B5. x * 0 = 0
lemma B5()
  ensures forall x: nat :: x * 0 == 0 {}

// B6. x * (y + 1) = (x * y) + x
lemma B6()
  ensures forall x: nat, y: nat :: x * (y + 1) == (x * y) + x {}

// B7. (x <= y /\ y <= x) => x = y
lemma B7()
  ensures forall x: nat, y: nat :: (x <= y && y <= x) ==> x == y {}

// B8. x <= x + y
lemma B8()
  ensures forall x: nat, y: nat :: x <= x + y {}

// B9. 0 <= x
lemma B9()
  ensures forall x: nat :: 0 <= x {}

// B10. x <= y \/ y <= x
lemma B10()
  ensures forall x: nat, y: nat :: (x <= y || y <= x) {}

// B11. x <= y <=> x < y + 1
lemma B11()
  ensures forall x: nat, y: nat :: (x <= y <==> x < y + 1) {}

// B12. x != 0 => exists y . y <= x & (y + 1 = x)
function B12'(x: nat) : nat
  requires x != 0
  ensures B12'(x) <= x && B12'(x) + 1 == x
{
  x - 1
}

lemma B12()
  ensures forall x : nat :: x != 0 ==> (exists y : nat :: y == B12'(x))
{
}



// // L1. X(y) => y < |X|
// // SMTLIB: (assert (forall ((X Str) (y Nat)) (=> (memb y X) (lt_nat y (card X)))))
// lemma L1()
//   requires forall X: seq<bool> :: ValidStr(X) // Assume all X of interest satisfy ValidStr
//   ensures forall X: seq<bool>, y: nat :: ValidStr(X) ==> (memb(X, y) ==> y < card(X))
// {
//   // Proof outline:
//   // Assume ValidStr(X) and memb(X,y).
//   // By definition of memb(X,y) (and ValidStr(X)), if memb(X,y) is true,
//   // then 0 <= y < |X| and X[y] is true.
//   // By definition of card(X), card(X) is |X|.
//   // So we need to show y < |X|, which is directly given by the precondition of `memb`.
// }

// // L2. y + 1 = |X| => X(y)
// // SMTLIB: (assert (forall ((X Str) (y Nat)) (=> (eq_nat (plus y one) (card X)) (memb y X))))
// lemma L2()
//   requires forall X: seq<bool> :: ValidStr(X) // Assume all X of interest satisfy ValidStr
//   ensures forall X: seq<bool>, y: nat :: ValidStr(X) ==> (y + 1 == card(X) ==> memb(X, y))
// {
//   // Proof outline:
//   // Assume ValidStr(X) and y + 1 == card(X).
//   // By definition of card(X), card(X) is |X|. So y + 1 == |X|.
//   // This implies y == |X| - 1.
//   // We need to show memb(X, y), which is `memb(X, |X| - 1)`.
//   // By definition of `memb`, this is `if 0 <= (|X|-1) < |X| then X[|X|-1] else false`.
//   // Since `|X| = y+1` and `y:nat`, `|X| >= 1`, so `0 <= (|X|-1) < |X|` is true.
//   // So we need to show `X[|X|-1]`.
//   // By the `ValidStr(X)` predicate, `|X| == 0 || X[|X|-1]`.
//   // Since `|X| >= 1`, it cannot be 0, so `X[|X|-1]` must be true.
//   // Thus, the lemma holds.
// }


// // SE. [|X| = |Y | ∧ ∀i < |X|(X(i) ↔ Y (i))] ⊃ X = Y
// // SMTLIB: (assert (forall ((X Str) (Y Str)) (=> (and (eq_nat (card X) (card Y)) (forall ((i Nat)) (=> (lt_nat i (card X)) (= (memb i X) (memb i Y))))) (eq_str X Y))))
// lemma SE()
//   requires forall X: seq<bool> :: ValidStr(X) // Assume all X of interest satisfy ValidStr
//   ensures forall X: seq<bool>, Y: seq<bool> ::
//     (ValidStr(X) && ValidStr(Y) &&
//      card(X) == card(Y) &&
//      (forall i: nat :: i < card(X) ==> (memb(X, i) <==> memb(Y, i))))
//     ==> X == Y // Dafny's `==` on sequences is structural equality
// {
//   // Proof outline:
//   // Assume ValidStr(X), ValidStr(Y).
//   // Assume card(X) == card(Y). Let N = card(X) = card(Y).
//   // So N = |X| = |Y|.
//   // Assume forall i: nat :: i < N ==> (memb(X, i) <==> memb(Y, i)).
//   // By definition of memb and ValidStr:
//   // For `i < N`, memb(X, i) is `X[i]`, which is true by ValidStr(X).
//   // For `i < N`, memb(Y, i) is `Y[i]`, which is true by ValidStr(Y).
//   // So `(true <==> true)` which is always true.
//   // This means the `forall i` clause adds no extra constraint on X and Y,
//   // beyond their lengths being equal and them being valid `Str`s.
//   // If `|X| == |Y|` (i.e., `N == N`), and both `X` and `Y` satisfy `ValidStr`.
//   // `ValidStr(X)` means `forall i: nat :: i < |X| ==> X[i]`.
//   // `ValidStr(Y)` means `forall i: nat :: i < |Y| ==> Y[i]`.
//   // Since `|X| == |Y|`, both `X` and `Y` must be sequences of length `N` where all elements are `true`.
//   // E.g., `X = seq(N, i => true)` and `Y = seq(N, i => true)`.
//   // Therefore, `X == Y` must hold.
// }






// // function empty (i : nat) : bool { false }
// const empty : seq<bool> := []

// // Safe bit access: returns false for out-of-bounds indices
// function bitWithDefault(X: seq<bool>, i: nat): bool
// {
//   if 0 <= i < |X| then X[i] else false
// }

// // XOR: true iff exactly one of a, b is true
// function xor(a: bool, b: bool): bool
// {
//   (a || b) && !(a && b)
// }

// // Majority of three bits: true if at least two are true
// function maj(p: bool, q: bool, r: bool): bool
// {
//   (p && q) || (p && r) || (q && r)
// }

// // Original definition from Example V.4.17
// function Carry(i: nat, X: seq<bool>, Y: seq<bool>): bool
// {
//   exists k :: 0 <= k < i &&
//               bitWithDefault(X, k) && bitWithDefault(Y, k) &&
//               forall j :: j < i ==> (k < j ==> (bitWithDefault(X, j) || bitWithDefault(Y, j)))
// }

// lemma exV_4_18()
//   ensures forall X :: forall Y :: !Carry(0, X, Y)
//   ensures forall X :: forall Y :: forall i : nat ::
//     Carry(i + 1, X, Y) <==>  maj(Carry(i, X, Y), bitWithDefault(X, i), bitWithDefault(Y, i))
// {
// }


// function Succ(X: seq<bool>): seq<bool>
// {
//   seq (|X| + 1, i =>
//     0 <= i <= |X| && (
//       (bitWithDefault(X, i) && (exists j :: 0 <= j < i && !bitWithDefault(X, j)))
//       || (!bitWithDefault(X, i) && (forall j :: 0 <= j < i ==> !bitWithDefault(X, j)))
//     )
//     )
// }

// function Add(X: seq<bool>, Y: seq<bool>): seq<bool>
// {
//   seq (|X| + |Y|, i =>
//     0 <= i < |X| + |Y| && (
//       xor(
//         xor(
//           bitWithDefault(X, i),
//           bitWithDefault(Y, i)
//         ),
//         Carry(i, X, Y)
//       )
//     )
//     )
// }

// lemma ex_V_4_19_a()
//   ensures forall X :: forall i :: bitWithDefault(Add(X, empty), i) == bitWithDefault(X, i)
// {}

// lemma ex_V_4_19_b()
//   ensures forall X :: forall Y :: forall i :: bitWithDefault(Add(X, Succ(Y)), i) == bitWithDefault(Succ(Add(X, Y)), i)
// {

// }

// lemma ex_V_4_19_c()
//   ensures forall X :: forall Y :: forall i :: bitWithDefault(Add(X, Y), i) == bitWithDefault(Add(Y, X), i)
// {}

// lemma ex_V_4_19_d()
//   ensures forall X :: forall Y :: forall Z :: forall i ::
//                                                 bitWithDefault(Add(Add(X, Y), Z), i) == bitWithDefault(Add(X, Add(Y, Z)), i)
// {}

// // Example V.4.20; IDelta0 term
// function Pair(x : nat, y : nat) : nat { (x + y) * (x + y + 1) + 2 * y }

// // Exercise V.4.21 (provable in IDelta0)
// // first show that LHS implies x1 + y1 == x2 + y2
// lemma PairInjective()
//   ensures forall x1 :: forall y1 :: forall x2 :: forall y2 ::
//                                                    Pair(x1, y1) == Pair(x2, y2) ==> (x1 == x2 && y1 == y2)
// {}

