// import opened CookNguyen
include "CookNguyen.dfy"
// $ dafny run Main.dfy 11101011010111

// module Main {

method Main(args: seq<string>)
{
  if |args| < 2 {
    print "Usage: please provide a binary string as argument.\n";
    return;
  }

  var input := args[1];

  // Convert input string to seq<bool>
  var X := [];
  var isValid := true;

  // Parse each character
  var i := 0;
  while i < |input|
    invariant 0 <= i <= |input|
    invariant |X| == i
    decreases |input| - i
  {
    if input[i] == '0' {
      X := X + [false];
    } else if input[i] == '1' {
      X := X + [true];
    } else {
      isValid := false;
      break;
    }
    i := i + 1;
  }

  // Check ValidStr
  if !isValid || !ValidStr(X) {
    print "Invalid input: must be a binary string (only 0s and 1s).\n";
    return;
  }

  // Run the palindrome check
  var result := Palindrome(X);
  if result {
    print "Palindrome\n";
  } else {
    print "Not a palindrome\n";
  }
}
// }