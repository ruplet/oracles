// note: https://github.com/dafny-lang/dafny/tree/master/Source/DafnyStandardLibraries/src/Std

type Tape = seq<bv1>

datatype Tapes = Tapes(
    input: Tape,
    work: Tape,
    output: Tape,
    inputIndex: nat,
    workIndex: nat,
    outputIndex: nat 
)

predicate TapesValid(a: Tapes)
{
    0 <= a.inputIndex < |a.input| &&
    0 <= a.workIndex < |a.work| &&
    0 <= a.outputIndex < |a.output|
}

function exp(n: nat) : nat
{
    Std.Arithmetic.Power2.Pow2(n)
}


lemma expTest1() ensures exp(0) == 1 {}
lemma expTest2() ensures exp(1) == 2 {}
lemma expTest3() ensures exp(2) == 4 {}
lemma expTest4() ensures exp(3) == 8 {}
lemma expTest5() ensures exp(4) == 16 {}
lemma expTest6() ensures exp(5) == 32 {}
lemma expTest7() ensures exp(6) == 64 {}
lemma expTest8()
    ensures forall a: nat :: exp(a + 1) == exp(a) * 2 {}
lemma expTest9()
    ensures forall a: nat :: exp(a + 5) == exp(a) * 32
{
    forall a: nat ensures exp(a + 5) == exp(a) * 32 {
        Std.Arithmetic.Power2.LemmaPow2Auto();
        assert exp(a + 5) == Std.Arithmetic.Power2.Pow2(a + 5);
        Std.Arithmetic.Power.LemmaPowAddsAuto();
        assert exp(5) == 32;
    }
}
lemma expTest10()
    ensures forall a:nat, b: nat :: exp(a + b) == exp(a) * exp(b) 
{
    forall a:nat, b: nat ensures exp(a + b) == exp(a) * exp(b) {
        Std.Arithmetic.Power.LemmaPowAddsAuto();
    }
}

lemma expTest11()
    ensures exp(100) == 1267650600228229401496703205376
{
    assert exp(100) == exp(64) * exp(36) by {
        expTest10(); 
    }
    Std.Arithmetic.Power2.Lemma2To64();
}


predicate TapesLogspace(a: Tapes)
{
    exp(|a.work|) <= |a.input|
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

method maxTest()
{
    assert max(1, 2) == 2;
    assert max(2, 1) == 2;
    assert max(1, 1) == 1;
    assert max(-1, -2) == -1;
    assert max(-2, -1) == -1;
    var big: int := 42342342243234242342342342888812131313123131231231231231231123;
    assert max(big, big) == big;
    assert max(big, 1) == big;
    assert max(big, big + 1) == big + 1;
}

type LittleEndian = a: seq<bv1> | |a| == 0 || a[|a| - 1] == 1

predicate isLittleEndian(a: seq<bv1>)
{
    |a| == 0 || a[|a| - 1] == 1
}

function littleEndianToNat(a: LittleEndian) : nat
{
    if |a| == 0 then 0 else (a[0] as nat) + 2 * littleEndianToNat(a[1..])
}

function sum(a: seq<nat>) : nat
{
    if |a| == 0 then 0 else a[0] + sum(a[1..])
}

lemma sumTest1() ensures sum([]) == 0 {}
lemma sumTest2() ensures sum([1]) == 1 {}
lemma sumTest3() ensures sum([1, 2, 3]) == 6 {}
lemma sumTest4() ensures sum([1, 2, 3, 4]) == 10 {}

function Map<T, R>(f: T ~> R, xs: seq<T>): (result: seq<R>)
    requires forall i :: 0 <= i < |xs| ==> f.requires(xs[i])
    ensures |result| == |xs|
    ensures forall i {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
{
    if |xs| == 0 then []
    else [f(xs[0])] + Map(f, xs[1..])
}

lemma MapTest1() ensures Map((x: nat) => x + 1, []) == [] {
    assert forall xs: seq<nat> :: |xs| == 0 ==> xs == [];
    var f : (nat -> nat) := (x: nat) => x + 1;
    assert forall f: (nat -> nat) :: Map(f, []) == [];
    assert Map(f, []) == [];
    calc {
        Map((x: nat) => x + 1, []);
        ==
        { assert forall y:nat :: ((x: nat => x + 1)(y)) == f(y); }
        Map(f, []);
        ==
        [];
    }
}
lemma MapTest2() ensures Map((x: nat) => x + 1, [1]) == [2] {}
lemma MapTest3() ensures
    forall xs: seq<bv1> :: |Map((i: bv1) => i as nat, xs)| == |xs| {}

function OfBits(a: seq<bv1>) : (result : seq<nat>)
    ensures |a| == |result|
{
    Map((i: bv1) => i as nat, a)
}

module BinaryConversion refines Std.Arithmetic.LittleEndianNat {
    function BASE(): nat { 2 }
}

function binToNat(a: seq<bv1>) : (result: nat)
{
    BinaryConversion.ToNatRight(OfBits(a))
}

// lemma trivialSeq()
//     ensures forall f:(nat->nat) {:trigger seq(0, f)} :: seq(0, f) == []
// {}

lemma binToNatTest1() ensures binToNat([]) == 0 {}
lemma binToNatTest2() ensures binToNat([0]) == 0 {}
lemma binToNatTest3() ensures binToNat([1]) == 1 {}
lemma binToNatTest4() ensures binToNat([1, 0]) == 1 {}
lemma binToNatTest5() ensures forall l:seq<bv1> :: binToNat(l + [1]) == binToNat(l) + exp(|l|) {}
lemma binToNatTest6() ensures binToNat([1, 0, 1]) == 5 {
    assert exp(|[1, 0]|) == 4;
    binToNatTest5();
}
lemma binToNatTest77()
    ensures forall x:bv1 :: binToNat([x]) == x as nat
{
    forall x:bv1 ensures binToNat([x]) == x as nat {
        BinaryConversion.LemmaSeqLen1(OfBits([x]));
    }
}
lemma binToNatTest7(ls: seq<bv1>)
    ensures ls == [] ==> binToNat(ls) == 0
    ensures ls != [] ==> binToNat(ls) == ls[0] as nat + 2 * binToNat(ls[1..])
    decreases |ls|
{
    if ls == [] { }
    else {
        var c := ls[0] as nat;
        assert binToNat(ls[1..]) == ls[1] as nat + 2 * binToNat(ls[2..]);
        assert binToNat(ls) == c + 2 * binToNat(ls[1..]);
        assert binToNat(ls) == c + 2 * (ls[1] as nat + 2 * binToNat(ls[2..]));
        assert binToNat(ls) == c + 2 * ls[1] as nat + 4 * binToNat(ls[2..]);
    }
}
lemma binToNatTest8() ensures binToNat([1, 0, 1, 1]) == 13 {
    assert exp(|[1, 0, 1]|) == 8;
    binToNatTest5();
}
// lemma {:only} binToNatTest7() ensures binToNat([1, 0, 1, 1]) == 13 {
//     calc {
//         binToNat([1, 0, 1, 1]);
//         ==
//         calc {[1, 0, 1] + [1] == [1, 0, 1, 1];}
//         calc {
//             binToNat([1, 0, 1] + ([1] + []));
//             ==
//             { Std.Collections.Seq.LemmaConcatIsAssociative([1, 0, 1], [1], []); }
//             binToNat([1, 0, 1, 1] + []);
//         }
//         binToNat([1, 0, 1] + [1]);
//         ==
//         binToNat([1, 0, 1]) + exp(|[1, 0, 1]|);
//         ==
//         binToNat([1, 0, 1]) + exp(3);
//         ==
//         5 + 8;
//     }
// }

method littleEndianToNatTest()
{
    var a: LittleEndian := [1, 0, 1];
    var b: LittleEndian := [];
    var c: LittleEndian := [0, 1, 1];
    assert littleEndianToNat(a) == 5;
    assert littleEndianToNat(b) == 0;
    assert littleEndianToNat(c) == 6;
}

function getLeadingOnes(a: Tape) : (result: nat)
    requires |a| > 0
    requires 0 in a
    ensures result < |a|
    ensures a[0..result] == seq(result, i => 1) && a[result] == 0
    ensures (forall i: nat :: i < |a| && a[..i] == seq(i, j => 1) ==> result >= i)
    ensures (forall i: nat :: i < |a| && a[i] == 0 ==> result <= i)
{
    if a[0] == 0 then 0
    else 1 + getLeadingOnes(a[1..])
}

method getLeadingOnesTest()
{
    var a: Tape := [1, 1, 0, 1, 1];
    var b: Tape := [0, 1, 1, 0, 1];
    var c: Tape := [1, 1, 1, 0];
    assert getLeadingOnes(a) == 2;
    assert getLeadingOnes(b) == 0;
    assert getLeadingOnes(c) == 3;
}

predicate encodesPair(a: Tape)
{
    if 0 !in a then false else
    var lenFirst: nat := getLeadingOnes(a);
    assert a[..lenFirst] == seq(lenFirst, i => 1);
    assert a[lenFirst] == 0;
    if |a| < lenFirst * 2 + 1 then false else
    if 0 !in a[lenFirst * 2 + 1..] then false else
    var lenSecond: nat := getLeadingOnes(a[lenFirst * 2 + 1..]);
    assert a[lenFirst * 2 + 1..lenFirst * 2 + 1 + lenSecond] == seq(lenSecond, i => 1);
    assert a[lenFirst * 2 + 1 + lenSecond] == 0;
    |a| == lenFirst * 2 + lenSecond * 2 + 2
}

method encodesPairTest()
{
    var a: Tape := [1, 1] + [0] + [0, 1] + [1, 1, 1] + [0] + [0, 0, 0];
    assert encodesPair(a) by {
        assert |a| == 12;
        var lenFirst: nat := getLeadingOnes(a);
        assert a[2] == 0;
        assert a[8] == 0;
        var lenSecond: nat := getLeadingOnes(a[lenFirst * 2 + 1..]);
        assert a[lenFirst * 2 + 1..lenFirst * 2 + 1 + lenSecond] == seq(lenSecond, i => 1);
        assert a[lenFirst * 2 + 1 + lenSecond] == 0;
        assert |a| == lenFirst * 2 + lenSecond * 2 + 2;
    }
    
    assert !encodesPair([]);
    assert !encodesPair([0]);
    assert !encodesPair([1]);
    assert encodesPair([0, 0]);
    assert !encodesPair([0, 1]);
}

function twoNumsToInputTape(a: LittleEndian, b: LittleEndian) : Tape
{
    seq(|a|, i => 1) + [0] + a + seq(|b|, i => 1) + [0] + b
}

predicate encodesTwoNums(a: Tape)
{
    if !encodesPair(a) then false else
    var lenFirst: nat := getLeadingOnes(a);
    var lenSecond: nat := getLeadingOnes(a[lenFirst * 2 + 1..]);
    var aFirst: seq<bv1> := a[lenFirst + 1..lenFirst * 2 + 1];
    var aSecond: seq<bv1> := a[lenFirst * 2 + 1 + lenSecond + 1..];
    assert |aFirst| == lenFirst;
    assert |aSecond| == lenSecond;
    isLittleEndian(aFirst) && isLittleEndian(aSecond)
}

function inputTapeToTwoNums(input: Tape) : (LittleEndian, LittleEndian)
    requires encodesTwoNums(input)
{
    var lenFirst: int := getLeadingOnes(input);
    var lenSecond: int := getLeadingOnes(input[lenFirst * 2 + 1..]);
    var a: LittleEndian := input[lenFirst + 1..lenFirst * 2 + 1];
    var b: LittleEndian := input[lenFirst * 2 + 1 + lenSecond + 1..];
    (a, b)
}

function sumOfTwoNumsOnInput(input: Tape) : nat
    requires encodesTwoNums(input)
{
    var a: (LittleEndian, LittleEndian) := inputTapeToTwoNums(input);
    littleEndianToNat(a.0) + littleEndianToNat(a.1)
}

// method Plus(a:nat, b:nat) returns (result: nat, a': nat, b': nat)
//     ensures result == a + b
//     ensures a' == a 
//     ensures b' == b
// {
//     return a + b, a, b;
// }

// method Times(a:nat, b:nat) returns (result': nat)
// {
//     var result: nat := 0;
//     var a': nat := a;
//     while (a' > 0)
//         decreases a'
//         invariant result == a * b - a' * b
//     {
//         var result', a'', b' := Plus(result, b);
//         result := result';
//         a' := a' - 1;
//     }
//     return result;
// }

method addRaw(pointerNum1Start: nat, pointerNum1End: nat, pointerNum2Start: nat, pointerNum2End: nat, input: Tape)
    returns (result: Tape, pointerNum1Final: nat, pointerNum2Final: nat, carry': bv1)
    requires pointerNum1Start <= pointerNum1End && pointerNum2Start <= pointerNum2End
    requires pointerNum1End < |input| && pointerNum2End < |input|

{
    var pointerNum1: nat := pointerNum1Start;
    var pointerNum2: nat := pointerNum2Start;
    var output: Tape := [];
    var carry: bv1 := 0;
    
    while (pointerNum1 <= pointerNum1End && pointerNum2 <= pointerNum2End)
        decreases pointerNum1End - pointerNum1 + pointerNum2End - pointerNum2
        invariant pointerNum1 - pointerNum1Start == pointerNum2 - pointerNum2Start
    {
        var bit1: bv1 := input[pointerNum1];
        var bit2: bv1 := input[pointerNum2];
        var outputBit : bv1 := bit1 + bit2 + carry;
        assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) & 1 == (outputBit as bv2);

        if carry == 1 {
            assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) >> 1 == ((bit1 | bit2) as bv2);
            carry := bit1 | bit2;
        } else {
            assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) >> 1 == ((bit1 & bit2) as bv2);
            carry := bit1 & bit2;
        }

        output := output + [outputBit];
        assert binToNat(input[pointerNum1Start..pointerNum1]) + 
            binToNat(input[pointerNum2Start..pointerNum2]) == binToNat(output + [carry]);
        pointerNum1 := pointerNum1 + 1;
        pointerNum2 := pointerNum2 + 1;
    }
    // // now finish the remaining one
    // while (pointerNum1 <= pointerNum1End)
    //     decreases pointerNum1End - pointerNum1
    //     invariant pointerNum1 - startA == pointerNum2 - startB
    // {
    //     var bit1: bv1 := input[pointerNum1];
    //     output := output + [bit1 + carry];
    //     carry := bit1 & carry;
    //     pointerNum1 := pointerNum1 + 1;
    // }
    // while (pointerNum2 <= pointerNum2End)
    //     decreases pointerNum2End - pointerNum2
    //     invariant pointerNum1 - startA == pointerNum2 - startB
    // {
    //     var bit2: bv1 := input[pointerNum2];
    //     output := output + [bit2 + carry];
    //     carry := bit2 & carry;
    //     pointerNum2 := pointerNum2 + 1;
    // }
    // // now finish the carry
    // if carry == 1 {
    //     output := output + [1];
    // }
    return output, pointerNum1, pointerNum2, carry;
}

// // logspace TM = k-head finite automata
// method add(input: Tape) returns (result: Tape)
//     requires encodesTwoNums(input)
//     // ensures isLittleEndian(result)
//     // ensures sumOfTwoNumsOnInput(input) == littleEndianToNat(result)
// {
//     var tmp: nat := 0;
//     var pointerNum1: nat := 0;
//     var pointerNum1End: nat := 0;
//     var pointerNum2: nat := 0;
//     var pointerNum2End: nat := 0;
//     var output: Tape := [];
//     // traverse the first sequence of 1s
//     while (input[pointerNum1] == 1)
//         decreases |input| - pointerNum1
//         invariant pointerNum1 <= getLeadingOnes(input)
//     {
//         // we take incrementation as a subroutine
//         pointerNum1 := pointerNum1 + 1;
//     }
//     assert input[pointerNum1] == 0;
//     tmp := pointerNum1;
//     pointerNum1End := pointerNum1;
//     pointerNum1 := pointerNum1 + 1;
//     assert pointerNum1 == getLeadingOnes(input) + 1;
//     // traverse the first number
//     while (tmp > 0)
//         decreases tmp
//         invariant pointerNum1End == (pointerNum1 - 1) * 2 - tmp
//     {
//         pointerNum1End := pointerNum1End + 1;
//         tmp := tmp - 1;
//     }
//     assert pointerNum1End == getLeadingOnes(input) * 2;
//     // now [pointerNum1, pointerNum1End] is the first number

//     ghost var lenFirst: nat := getLeadingOnes(input);
//     ghost var lenSecond: nat := getLeadingOnes(input[lenFirst * 2 + 1..]);
//     assert lenFirst * 2 + 1 + lenSecond * 2 + 1 == |input|;
    
//     pointerNum2 := pointerNum1End + 1;
//     // traverse the second sequence of 1s
//     while (input[pointerNum2] == 1)
//         decreases |input| - pointerNum2
//         invariant pointerNum1End <= pointerNum2 
//         invariant pointerNum2 <= pointerNum1End + lenSecond + 1
//     {
//         // we take incrementation as a subroutine
//         pointerNum2 := pointerNum2 + 1;
//     }
//     assert input[pointerNum2] == 0;
//     tmp := pointerNum2;
//     pointerNum2End := pointerNum2;
//     pointerNum2 := pointerNum2 + 1;
//     assert pointerNum2 == lenFirst * 2 + 1 + lenSecond + 1;
//     assert pointerNum2End == lenFirst * 2 + 1 + lenSecond;
//     // traverse the second number
//     while (tmp > pointerNum1End + 1)
//         decreases tmp
//         invariant tmp >= pointerNum1End + 1
//         invariant pointerNum2End == lenFirst * 2 + 1 + lenSecond + (pointerNum2 - 1 - tmp)
//     {
//         pointerNum2End := pointerNum2End + 1;
//         tmp := tmp - 1;
//     }
//     assert pointerNum2End == lenFirst * 2 + 1 + lenSecond * 2;
//     // now [pointerNum2, pointerNum2End] is the second number
//     // now we can add the two numbers
//     // var carry: bv1 := 0;
//     assert pointerNum1 == getLeadingOnes(input) + 1;
//     assert pointerNum2 == getLeadingOnes(input[lenFirst * 2 + 1..]) + 1;
//     assert pointerNum1End < |input| && pointerNum2End < |input|;
//     var (output':Tape, pointerNum1Start:nat, pointerNum2Start:nat, carry':bv1) := addRaw(pointerNum1, pointerNum1End, pointerNum2, pointerNum2End, input);
//     // assert pointerNum1 == lenFirst + 1;
//     // assert pointerNum2 == lenFirst * 2 + 1 + lenSecond + 1;
//     // assert pointerNum1End < |input| && pointerNum2End < |input|;
//     // // assert binToNat(input[lenFirst + 1..pointerNum1]) == 0;
//     // // assert binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2]) == 0;
//     // // assert binToNat(output + [carry]) == 0;
//     // while (pointerNum1 <= pointerNum1End && pointerNum2 <= pointerNum2End)
//     //     decreases pointerNum1End - pointerNum1 + pointerNum2End - pointerNum2
//     //     invariant pointerNum1 - (lenFirst + 1) == pointerNum2 - (lenFirst * 2 + 1 + lenSecond + 1)
//     //     // invariant binToNat(input[lenFirst + 1..pointerNum1]) + 
//     //     //     binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2]) >= 0
//     //     // invariant (binToNat(input[lenFirst + 2..pointerNum1]) + 
//     //     //     binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2])) % 4 == binToNat(output)
//     // {
//     //     var bit1: bv1 := input[pointerNum1];
//     //     var bit2: bv1 := input[pointerNum2];
//     //     var outputBit : bv1 := bit1 + bit2 + carry;
//     //     assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) & 1 == (outputBit as bv2);

//     //     if carry == 1 {
//     //         assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) >> 1 == ((bit1 | bit2) as bv2);
//     //         carry := bit1 | bit2;
//     //     } else {
//     //         assert ((bit1 as bv2) + (bit2 as bv2) + (carry as bv2)) >> 1 == ((bit1 & bit2) as bv2);
//     //         carry := bit1 & bit2;
//     //     }

//     //     output := output + [outputBit];
//     //     assert binToNat(output + [carry]) == 
//     //         binToNat(input[lenFirst + 1..pointerNum1]) + 
//     //         binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2]);
            
//     //     pointerNum1 := pointerNum1 + 1;
//     //     pointerNum2 := pointerNum2 + 1;
//     // }
//     // now finish the remaining one
//     while (pointerNum1 <= pointerNum1End)
//         decreases pointerNum1End - pointerNum1
//     {
//         var bit1: bv1 := input[pointerNum1];
//         output := output + [bit1 + carry];
//         carry := bit1 & carry;
//         pointerNum1 := pointerNum1 + 1;
//     }
//     while (pointerNum2 <= pointerNum2End)
//         decreases pointerNum2End - pointerNum2
//     {
//         var bit2: bv1 := input[pointerNum2];
//         output := output + [bit2 + carry];
//         carry := bit2 & carry;
//         pointerNum2 := pointerNum2 + 1;
//     }
//     // now finish the carry
//     if carry == 1 {
//         output := output + [1];
//     }
//     return output;
// }