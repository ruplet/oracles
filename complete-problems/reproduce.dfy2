predicate ValidStr(s : seq<bool>) {
  |s| == 0 || s[|s| - 1]
}

// B1. x + 1 != 0
lemma B1()
  ensures forall x : nat {:trigger x + 1} :: x + 1 != 0 {}

// B2. x + 1 = y + 1 => x = y
lemma B2()
  ensures forall x: nat {:trigger x + 1}, y: nat :: x + 1 == y + 1 ==> x == y {}
