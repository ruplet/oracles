function sum(a: seq<nat>) : (result: nat)
{
    if |a| == 0 then 0 else a[0] + sum(a[1..])
}

lemma sumTest1() ensures sum([]) == 0 {}
lemma sumTest2() ensures sum([1, 2, 3]) == 6 {}
lemma sumTest3() ensures sum([1, 2, 3, 4]) == 10 {}

function sum2(a: seq<nat>) : seq<nat>
{
    seq(|a|, i => if 0 <= i < |a| then a[i] else 0)
}