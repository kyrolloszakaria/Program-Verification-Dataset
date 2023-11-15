/*
 * Merge sort
 * Merge sorts an array of integers
 * Verification time: ~10 seconds
 * Verified on CSE Dafny 1.9.7
 */

method Main()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 3, 4, 2, 5, 1;
    assert a[..] == [3, 4, 2, 5, 1];
    print "original: ", a[..], "\n";
    MergeSort(a);
    assert a[..] == [1, 2, 3, 4, 5];
    print "sorted  : ", a[..], "\n";
}

method MergeSort(a: array<int>)
    modifies a;
    requires a != null;
    ensures  sorted(a);
    ensures  permutation(a[..], old(a[..]));
{
    if a.Length == 0 {
        return;
    }

    DoMergeSort(a, 0, a.Length);

    assert a[..] == a[0..a.Length];
    assert old(a[..]) == old(a[0..a.Length]);
}

method DoMergeSort(a: array<int>, l: int, r: int)
    modifies  a;
    requires  a != null;
    requires  0 <= l < r <= a.Length;
    ensures   sortedFromTo(a, l, r);
    ensures   permutation(a[l..r], old(a[l..r]));
    ensures   a[..l] == old(a[..l]);
    ensures   a[r..] == old(a[r..]);
    decreases r - l;
{
    if l == r - 1 {
        return;
    }

    var m := (l + r) / 2;

    DoMergeSort(a, l, m);
    assert sortedFromTo(a, l, m); // subarray from l to m sorted
    assert permutation(a[l..m], old(a[l..m]));
    assert a[m..r] == old(a[m..r]); // subarray from m to r unchanged

    DoMergeSort(a, m, r);

    assert a[l..m] + a[m..r] == a[l..r];
    assert old(a[l..m]) + old(a[m..r]) == old(a[l..r]);

    Merge(a, l, m, r);
}

method Merge(a: array<int>, l: int, m: int, r: int)
    modifies a;
    requires a != null;
    requires 0 <= l < m < r <= a.Length;
    requires sortedFromTo(a, l, m);
    requires sortedFromTo(a, m, r);
    ensures  sortedFromTo(a, l, r);
    ensures  permutation(a[l..r], old(a[l..r]));
    ensures  a[..l] == old(a[..l]);
    ensures  a[r..] == old(a[r..]);
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
        invariant a[..] == old(a[..]);
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

    assert a[l..r] == a[l..m] + a[m..r];

    forall i | l <= i < r
    {
        a[i] := b[i];
    }

    assert a[l..r] == b[l..r];
}

predicate sorted(a: array<int>)
    reads a;
    requires a != null;
{
    sortedFromTo(a, 0, a.Length)
}

predicate sortedFromTo(a: array<int>, l: int, r: int)
    reads a;
    requires a != null;
    requires 0 <= l <= r <= a.Length;
{
    forall i, j :: l <= i < j < r ==> a[i] <= a[j]
}

predicate permutation(a: seq<int>, b: seq<int>)
{
    multiset(a) == multiset(b)
}
