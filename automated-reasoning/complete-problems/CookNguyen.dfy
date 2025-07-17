// module CookNguyen {

predicate ValidStr(s : seq<bool>) {
  |s| == 0 || s[|s| - 1]
}

// B1. x + 1 != 0
lemma B1(x : nat)
  ensures x + 1 != 0 {}

// B2. x + 1 = y + 1 => x = y
lemma B2(x : nat, y : nat)
  ensures x + 1 == y + 1 ==> x == y {}

// B3. x + 0 = x
lemma B3(x : nat)
  ensures x + 0 == x {}

// B4. x + (y + 1) = (x + y) + 1
lemma B4(x : nat, y : nat)
  ensures x + (y + 1) == (x + y) + 1 {}

// B5. x * 0 = 0
lemma B5(x : nat)
  ensures x * 0 == 0 {}

// B6. x * (y + 1) = (x * y) + x
lemma B6(x : nat, y : nat)
  ensures x * (y + 1) == (x * y) + x {}

// B7. (x <= y /\ y <= x) => x = y
lemma B7(x : nat, y : nat)
  ensures (x <= y && y <= x) ==> x == y {}

// B8. x <= x + y
lemma B8(x : nat, y : nat)
  ensures x <= x + y {}

// B9. 0 <= x
lemma B9(x : nat)
  ensures 0 <= x{}

// B10. x <= y \/ y <= x
lemma B10(x : nat, y : nat)
  ensures (x <= y || y <= x) {}

// B11. x <= y <=> x < y + 1
lemma B11(x : nat, y : nat)
  ensures (x <= y <==> x < y + 1) {}

// B12. x != 0 => exists y . y <= x & (y + 1 = x)
lemma B12(x: nat) returns (y : nat)
  requires x != 0
  ensures y <= x && y + 1 == x
{
  y := x - 1;
}

lemma L1(X : seq<bool>, y : nat)
  requires ValidStr(X)
  requires y < |X|
  requires X[y]
  ensures y <= |X|
{}

lemma L2(X : seq<bool>, y : nat)
  requires ValidStr(X)
  requires y + 1 == |X|
  ensures X[y]
{}

lemma SE(X : seq<bool>, Y : seq<bool>)
  requires ValidStr(X)
  requires ValidStr(Y)
  requires |X| == |Y|
  requires forall i : nat :: i < |X| ==> (X[i] == Y[i])
  ensures X == Y
{}

// Exercise 5.1. Using 2-BASIC, show that:
// d) x < y => x + 1 <= y
lemma ex_5_1_d(x : nat, y : nat)
  requires x < y
  ensures x + 1 <= y
{}

// e) x < y => x + 1 < y + 1
lemma ex_t_1_e(x : nat, y : nat)
  requires x < y
  ensures x + 1 < y + 1
{}


// Definition 5.2 (Comprehension Axiom). If Phi is a set of formulas,
// then the comprehension axiom scheme for Phi, denoted Phi-COMP, is the
// set of all formulas Exists X . (|X| <= y && (Forall z . z < y ==> (X[z] == phi(z)))
// where phi(z) is any formula in Phi, and X does not occur free in phi(z)

// i.e. given a bound y on the length of bitset considered,
// and some class of formulas Phi (which are "easy" to test against a model)
// we can create the bitset X := precompute phi(i) for every i < y
// we don't want to take this as an axiom. First, it's difficult to represent
// second, we don't like "exists" quantifiers, as we can create the actual object in Dafny

// returns first index which does not belong to {z | z < bound & phi(z)}
method holdsArgMax(bound : nat, phi : nat -> bool) returns (p : nat)
  ensures p <= bound
  ensures forall i :: p <= i < bound ==> !phi(i)
  ensures p == 0 || phi(p - 1)
{
  p := 0;

  var current_p := 0;
  while current_p < bound
    invariant p <= bound
    invariant p == 0 || phi(p - 1)
    invariant forall i :: p <= i < current_p ==> !phi(i)
    invariant 0 <= current_p <= bound
    decreases bound - current_p
  {
    if phi(current_p) {
      p := current_p + 1;
    } 
    current_p := current_p + 1;
  }
}

// this is slightly different to the original, because in the book
// they define |X| := highest set bit of X. In this implementation,
// |X| is defined in another way, and we only ensure that X[|X| - 1] is set
// theory V^i has vocabulary L^2_A and is axiomatized by 2-BASIC and Sigma^B_i-COMP
method Comprehension(y : nat, phi : nat -> bool) returns (X : seq<bool>)
  ensures ValidStr(X)
  ensures |X| <= y
  ensures forall z : nat :: z < |X| ==> (X[z] == phi(z))
{
  var highest := holdsArgMax(y, phi);
  X := seq(highest, i requires i >= 0 => phi(i));
}

// Definition 5.5 (Number Minimization and Maximization Axioms).
// The number minimization axioms (or least number principle axioms) for a set
// Phi of two-sorted formulas are denoted Phi-MIN and consist of the formulas
// phi(y) => Exists x <= y . phi(x) & not(Exists z < x . phi(z))
// where phi is a formula in Phi.
method NumberMinimization(y : nat, phi : nat -> bool) returns (x : nat)
  requires phi(y)
  ensures x <= y
  ensures phi(x)
  ensures !(exists z : nat :: z < x && phi(z))
{
  var i := 0;
  while i <= y
    invariant i <= y + 1
    invariant forall z: nat :: z < i ==> !phi(z)
    decreases y - i
  {
    if phi(i) {
      x := i;
      return;
    }
    i := i + 1;
  }
}

// Similarly the number maximization axioms for Phi are denoted Phi-MAX
// and consist of the formulas
// phi(0) => Exists x <= y . phi(x) & not(Exists z <= y. x < z & phi(z))
// where phi is a formula in Phi.
method NumberMaximization(y: nat, phi: nat -> bool) returns (x: nat)
  requires phi(0)
  ensures x <= y
  ensures phi(x)
  ensures forall z: nat :: z <= y && x < z ==> !phi(z)
{
  var i := 0;
  var best := 0;
  while i <= y
    invariant i <= y + 1
    invariant best <= i
    invariant best <= y
    invariant phi(best)
    invariant forall z: nat :: best < z && z < i ==> !phi(z)
    decreases y - i
  {
    if phi(i) {
      best := i;
    }
    i := i + 1;
  }
  x := best;
}

// NOTE: in the book, phi(x) is permitted to have free variables of both sorts,
// in addition to x.
// NOTE: before any use of comprehension, ensure that the formula used is Sigma^B_i

// Lemma 5.6 V^0 proves X-MIN
function YFormula(X : seq<bool>, z : nat) : bool
{
  z < |X| && forall y : nat :: y < z ==> !X[y]
}

// Example 4.16 The language PAL (page 68) of binary palindromes is
// represented by the formula
// phi_{PAL}(X) <=>
//  (|X| <= 1)
//  || (forall x, y < |X| . x + y + 2 = |X| => X(x) <-> X(y))
function Palindrome(X : seq<bool>) : bool
  requires ValidStr(X)
{
  |X| <= 1
  || (
    forall x : nat :: (
      x < |X| ==> (
        forall y : nat :: (
          y < |X| ==> (
            x + y + 1 == |X| ==>
              X[x] == X[y]
          )
        )
      )
    )
  )
} by method {
  if |X| <= 1 {
    return true;
  }

  var hd := 0;
  var tl := |X| - 1;
  while hd < tl
    invariant hd + tl + 1 == |X|
    invariant forall x, y : nat ::
      0 <= x < hd
      && tl <= y < |X|
      && x + y + 1 == |X|
      ==> X[x] == X[y]
    decreases tl - hd
  {
    if X[hd] != X[tl] {
      return false;
    }
    hd := hd + 1;
    tl := tl - 1;
  }
  return true;
}

// Test of the specification
method TestPalindromeExamples()
{
  var x1 := [];
  assert Palindrome(x1);

  var x2 := [true];
  assert Palindrome(x2);

  var x3 := [true, true];
  assert Palindrome(x3);

  var x4 := [false, true];
  assert x4[0] != x4[1];
  assert !Palindrome(x4);

  var x5 := [true, false, true];
  assert Palindrome(x5);

  var x6 := [true, false, false, true, true];
  assert x6[1] != x6[3];
  assert !Palindrome(x6);

  var x7 := [true, false, false, false, true];
  assert Palindrome(x7);
}




// method XMin(X : seq<bool>) returns (x : nat)
//   requires ValidStr(X)
//   requires 0 < |X|
//   ensures x < |X|
//   ensures X[x]
//   ensures forall y : nat :: y < x ==> !X[y]
// {
//   // var Y := Comprehension(|X|, z => forall y : nat :: y < |X| ==> !X[y]);
//   var Y := Comprehension(|X|, z requires z >= 0 => YFormula(X, z));
//   // assert forall z : nat :: z < |Y| ==> Y[z] == (forall y : nat :: y <= z ==> !X[y]);

//   // Thus the set Y consists of the numbers smaller than every element in X
//   // Assuming 0 < |X|, we will show that |Y| is the least member of X.
//   // Intuitively, this is because |Y| is the least number that is larger than
//   // any member or Y. Formally, we need to show:
//   // (i) X[|Y|]
//   // (ii) forall y < |Y|. !X[y]
  
//   if (|Y| == 0) {
//     if !X[0] {
//       assert YFormula(X, 0);
//       assert 0 < |X| && forall y : nat :: y < 0 ==> !X[y];
//       assert false;
//     }

//     x := 0;
//     assert X[x];
//     assert forall y : nat :: y < x ==> !X[y];
//   } else {
//     var z := |Y| - 1;
//     assert Y[z];

//   }
// }

// Prove that V^i proves Sigma^B_i-IND, -MIN, -MAX


// Cool: https://dafny.org/v3.9.0/DafnyRef/DafnyRef#sec-function-declarations
// https://dafny.org/blog/2023/08/14/clear-specification-and-implementation/
// proof by contradiction: https://github.com/dafny-lang/dafny/issues/95 

// }