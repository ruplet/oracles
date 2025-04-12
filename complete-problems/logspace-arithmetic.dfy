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
    if n == 0 then 1 else 2 * exp(n - 1) 
}

method expTest()
{
    assert exp(0) == 1;
    assert exp(1) == 2;
    assert exp(2) == 4;
    assert exp(3) == 8;
    assert exp(4) == 16;
    assert exp(5) == 32;
    assert exp(6) == 64;
    // this doesn't check
    // assert exp(100) == 1267650600228229401496703205376 by {
    //     var i: int := 0;
    //     var result: int := 1;
    //     while (i < 100)
    //         decreases 100 - i
    //         invariant result == exp(i)
    //     {
    //         result := result * 2;
    //         i := i + 1;
    //     }
    //     assert result == exp(100);
    // }
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

function binToNat(a: seq<bv1>) : nat
{
    if |a| == 0 then 0 else (a[0] as nat) + 2 * binToNat(a[1..])
}

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

// this method should be convertible to a Turing machine, so it cannot use
// any Dafny tools nor the previously defined functions
method add(input: Tape) returns (result: Tape)
    requires encodesTwoNums(input)
    ensures isLittleEndian(result)
    ensures sumOfTwoNumsOnInput(input) == littleEndianToNat(result)
{
    var tmp: nat := 0;
    var pointerNum1: nat := 0;
    var pointerNum1End: nat := 0;
    var pointerNum2: nat := 0;
    var pointerNum2End: nat := 0;
    var output: Tape := [];
    // traverse the first sequence of 1s
    while (input[pointerNum1] == 1)
        decreases |input| - pointerNum1
        invariant pointerNum1 <= getLeadingOnes(input)
    {
        // we take incrementation as a subroutine
        pointerNum1 := pointerNum1 + 1;
    }
    assert input[pointerNum1] == 0;
    tmp := pointerNum1;
    pointerNum1End := pointerNum1;
    pointerNum1 := pointerNum1 + 1;
    assert pointerNum1 == getLeadingOnes(input) + 1;
    // traverse the first number
    while (tmp > 0)
        decreases tmp
        invariant pointerNum1End == (pointerNum1 - 1) * 2 - tmp
    {
        pointerNum1End := pointerNum1End + 1;
        tmp := tmp - 1;
    }
    assert pointerNum1End == getLeadingOnes(input) * 2;
    // now [pointerNum1, pointerNum1End] is the first number

    ghost var lenFirst: nat := getLeadingOnes(input);
    ghost var lenSecond: nat := getLeadingOnes(input[lenFirst * 2 + 1..]);
    assert lenFirst * 2 + 1 + lenSecond * 2 + 1 == |input|;
    
    pointerNum2 := pointerNum1End + 1;
    // traverse the second sequence of 1s
    while (input[pointerNum2] == 1)
        decreases |input| - pointerNum2
        invariant pointerNum1End <= pointerNum2 
        invariant pointerNum2 <= pointerNum1End + lenSecond + 1
    {
        // we take incrementation as a subroutine
        pointerNum2 := pointerNum2 + 1;
    }
    assert input[pointerNum2] == 0;
    tmp := pointerNum2;
    pointerNum2End := pointerNum2;
    pointerNum2 := pointerNum2 + 1;
    assert pointerNum2 == lenFirst * 2 + 1 + lenSecond + 1;
    assert pointerNum2End == lenFirst * 2 + 1 + lenSecond;
    // traverse the second number
    while (tmp > pointerNum1End + 1)
        decreases tmp
        invariant tmp >= pointerNum1End + 1
        invariant pointerNum2End == lenFirst * 2 + 1 + lenSecond + (pointerNum2 - 1 - tmp)
    {
        pointerNum2End := pointerNum2End + 1;
        tmp := tmp - 1;
    }
    assert pointerNum2End == lenFirst * 2 + 1 + lenSecond * 2;
    // now [pointerNum2, pointerNum2End] is the second number
    // now we can add the two numbers
    var carry: bv1 := 0;
    assert pointerNum1 == lenFirst + 1;
    assert pointerNum2 == lenFirst * 2 + 1 + lenSecond + 1;
    assert pointerNum1End < |input| && pointerNum2End < |input|;
    while (pointerNum1 <= pointerNum1End && pointerNum2 <= pointerNum2End)
        decreases pointerNum1End - pointerNum1 + pointerNum2End - pointerNum2
        invariant pointerNum1 - (lenFirst + 1) == pointerNum2 - (lenFirst * 2 + 1 + lenSecond + 1)
        invariant binToNat(input[lenFirst + 1..pointerNum1]) + 
            binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2]) >= 0
        // invariant (binToNat(input[lenFirst + 2..pointerNum1]) + 
        //     binToNat(input[lenFirst * 2 + 1 + lenSecond + 1..pointerNum2])) % 4 == binToNat(output)
    {
        var bit1: bv1 := input[pointerNum1];
        var bit2: bv1 := input[pointerNum2];
        output := output + [bit1 + bit2 + carry];
        carry := (carry & (bit1 | bit2)) | (bit1 & bit2);
        pointerNum1 := pointerNum1 + 1;
        pointerNum2 := pointerNum2 + 1;
    }
    // now finish the remaining one
    while (pointerNum1 <= pointerNum1End)
        decreases pointerNum1End - pointerNum1
    {
        var bit1: bv1 := input[pointerNum1];
        output := output + [bit1 + carry];
        carry := bit1 & carry;
        pointerNum1 := pointerNum1 + 1;
    }
    while (pointerNum2 <= pointerNum2End)
        decreases pointerNum2End - pointerNum2
    {
        var bit2: bv1 := input[pointerNum2];
        output := output + [bit2 + carry];
        carry := bit2 & carry;
        pointerNum2 := pointerNum2 + 1;
    }
    // now finish the carry
    if carry == 1 {
        output := output + [1];
    }
    return output;
}
