// MergeSort.dfy

method Main()
{
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 6, 0, 2, 4, 8, 1, 9, 7, 5, 3;
  assert a[..] == [6, 0, 2, 4, 8, 1, 9, 7, 5, 3];
  print "original: ", a[..], "\n";
  Sort(a);
  assert a[..] == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
  print "sorted  : ", a[..], "\n";
}

method Sort(a: array<int>)
  requires a != null;
  modifies a;
  ensures  sorted(a);
  ensures  permutation(a[..], old(a[..]));
{
  MergeSort(a);  
}

method MergeSort(a: array<int>)
  requires a != null;
  modifies a;
  ensures  sorted(a);
  ensures  permutation(a[..], old(a[..]));
{
  if a.Length == 0 {
    return;
  }
  
  DoMergeSort(a, 0, a.Length);
  
  // We need these but I'm not sure why
  assert a[..] == a[0..a.Length];
  assert old(a[..]) == old(a[0..a.Length]);
}

method DoMergeSort(a: array<int>, l: int, r: int)
  requires a != null;
  modifies a;
  requires 0 <= l < r <= a.Length;
  ensures  sortedFromTo(a, l, r);
  ensures  permutation(a[l..r], old(a[l..r]));
  ensures  forall i :: 0 <= i < l ==> a[i] == old(a[i]);
  ensures  forall i :: r <= i < a.Length ==> a[i] == old(a[i]);
  decreases r - l;
{
  if l == r - 1 {
    return;
  }

  var m := (l + r) / 2;

  DoMergeSort(a, l, m);
  assert a[..l] == old(a[..l]); // subarray to left of l unchanged
  assert sortedFromTo(a, l, m); // subarray from l to m sorted
  assert permutation(a[l..m], old(a[l..m]));
  assert a[m..r] == old(a[m..r]); // subarray from m to r unchanged
  assert a[r..] == old(a[r..]); // subarray to right of r unchanged

  ////////////////////////////////////////////////////////////////////////////

  ghost var g1 := a[..];
  DoMergeSort(a, m, r);
  assert a[l..m] == g1[l..m];

  assert a[l..m] + a[m..r] == a[l..r];
  assert old(a[l..m]) + old(a[m..r]) == old(a[l..r]);

  Merge(a, l, m, r);
}

method Merge(a: array<int>, l: int, m: int, r: int)
  requires a != null;
  modifies a;
  requires 0 <= l < m < r <= a.Length;
  requires sortedFromTo(a, l, m);
  requires sortedFromTo(a, m, r);
  ensures  sortedFromTo(a, l, r);
  ensures  permutation(a[l..r], old(a[l..r]));
  ensures  forall i :: 0 <= i < l ==> a[i] == old(a[i]);
  ensures  forall i :: r <= i < a.Length ==> a[i] == old(a[i]);
{
  var b := new int[a.Length];
  var i := l;
  var j := m;
  var k := l;

  while i < m || j < r
    decreases m - i + r - j;
    invariant l <= i <= m && m <= j <= r;
    invariant k == l + (i - l) + (j - m);
    invariant sortedFromTo(b, l, k);
    invariant k > l && i < m ==> b[k - 1] <= a[i];
    invariant k > l && j < r ==> b[k - 1] <= a[j];
    invariant permutation(b[l..k], a[l..i] + a[m..j]);
    invariant forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]);
  {
    if i == m {
      b[k] := a[j];
      j := j + 1;
    } else if j == r {
      b[k] := a[i];
      i := i + 1;
    } else if a[i] <= a[j] {
      b[k] := a[i];
      i := i + 1;
    } else {
      b[k] := a[j];
      j := j + 1;
    }
    k := k + 1;
  }

  // We need these but I'm not sure why
  assert a[l..r] == a[l..m] + a[m..r];
  assert sortedFromTo(b, l, r);
  ghost var c := a[..];
  ghost var d := b[..];

  // Copy sorted items from b back to a
  i := l;
  while i < r
    decreases r - i;
    invariant l <= i <= r;
    invariant forall j :: l <= j < i ==> a[j] == b[j];
    invariant forall j :: 0 <= j < l ==> a[j] == c[j];
    invariant forall j :: r <= j < a.Length ==> a[j] == c[j];
    invariant b[..] == d;
  {
    a[i] := b[i];
    i := i + 1;
  }

  assert a[l..r] == b[l..r];
  assert sortedFromTo(b, l, r);
}

predicate sorted(a: array<int>)
  requires a != null;
  reads a;
{
  sortedFromTo(a, 0, a.Length)
}

predicate sortedFromTo(a: array<int>, l: int, r: int)
  requires a != null;
  requires 0 <= l <= r <= a.Length;
  reads a;
{
  forall i, j :: l <= i < j < r ==> a[i] <= a[j]
}

predicate permutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}
