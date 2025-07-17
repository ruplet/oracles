predicate isSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

method binSearch(a: array<int>, key: int)
    returns (index: int)
    requires isSorted(a)
    ensures index >= 0 ==> (0 <= index < a.Length && a[index] == key)
    ensures index < 0 ==> (forall i :: 0 <= i < a.Length ==> a[i] != key)
{
  var lo: nat := 0;
  var hi: nat := a.Length;
  while (lo < hi)
    decreases hi - lo
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i : nat :: 0 <= i < a.Length && !(lo <= i < hi) ==> a[i] != key
  {
    var mid: nat := (lo + hi) / 2;
    if (a[mid] < key) {
      lo := mid + 1;
    } else if (a[mid] > key) {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}
