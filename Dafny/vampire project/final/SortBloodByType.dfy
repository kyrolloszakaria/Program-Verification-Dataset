/* 
 * Merge sorts an array of Blood objects by type
 * Verification time: ~35 seconds 
 * Verified on CSE Dafny 1.9.7
 */

include "Blood.dfy"

method Main()
{
    var a := new Blood[3];
    var b1 := new Blood(AP, "Amy", 21, "Hospital", true);
    var b2 := new Blood(OM, "Bob",  8, "Hospital", true);
    var b3 := new Blood(AM, "Cal", 13, "Hospital", true);
    
    a[0], a[1], a[2] := b1, b2, b3;
    assert a[..] == [b1, b2, b3];
    print "Original:\n";
    PrintBloodArray(a);
    SortBloodByType(a);
    print "Sorted:\n";
    assert a[..] == [b1, b3, b2];
    PrintBloodArray(a);
}

method SortBloodByType(a: array<Blood>)
    modifies a;
    requires a != null;
    requires forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
    ensures  forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
    ensures  sorted(a);
    ensures  permutation(a[..], old(a[..]));
{
    MergeSort(a);
}

method MergeSort(a: array<Blood>)
    modifies a;
    requires a != null;
    requires forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
    ensures  forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
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

method DoMergeSort(a: array<Blood>, l: int, r: int)
    modifies  a;
    requires  a != null;
    requires  forall i | 0 <= i < a.Length ::
                         a[i] != null &&
                         a[i].Valid();
    requires  0 <= l < r <= a.Length;
    ensures   forall i | 0 <= i < a.Length ::
                         a[i] != null &&
                         a[i].Valid();
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

method Merge(a: array<Blood>, l: int, m: int, r: int)
    modifies a;
    requires a != null;
    requires forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
    requires 0 <= l < m < r <= a.Length;
    requires sortedFromTo(a, l, m);
    requires sortedFromTo(a, m, r);
    ensures  forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
    ensures  sortedFromTo(a, l, r);
    ensures  permutation(a[l..r], old(a[l..r]));
    ensures  a[..l] == old(a[..l]);
    ensures  a[r..] == old(a[r..]);
{
    var b := new Blood[a.Length];
    var i := l;
    var j := m;
    var k := l;

    while i < m || j < r
        decreases m - i + r - j;
        invariant l <= i <= m && m <= j <= r;
        invariant k == l + (i - l) + (j - m);
        invariant a[..] == old(a[..]);
        invariant forall x | 0 <= x < a.Length ::
                             a[x] != null &&
                             a[x].Valid();
        invariant forall x | l <= x < k ::
                             b[x] != null &&
                             b[x].Valid();
        invariant sortedFromTo(b, l, k);
        invariant k > l && i < m ==> bloodTypeLeq(b[k - 1], a[i]);
        invariant k > l && j < r ==> bloodTypeLeq(b[k - 1], a[j]);
        invariant permutation(b[l..k], a[l..i] + a[m..j]);
    {
        if i == m {
            b[k] := a[j];
            j := j + 1;
        } else if j == r {
            b[k] := a[i];
            i := i + 1;
        } else if bloodTypeLeq(a[i], a[j]) {
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

predicate sorted(a: array<Blood>)
    reads a;
    reads set i | 0 <= i < a.Length :: a[i];
    requires a != null;
    requires forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
{
    sortedFromTo(a, 0, a.Length)
}

predicate sortedFromTo(a: array<Blood>, l: int, r: int)
    reads a;
    reads set i | 0 <= i < a.Length :: a[i];
    requires a != null;
    requires 0 <= l <= r <= a.Length;
    requires forall i | l <= i < r ::
                        a[i] != null &&
                        a[i].Valid();
{
    forall i, j :: l <= i < j < r ==> bloodTypeLeq(a[i], a[j])
}

predicate method bloodTypeLeq(a: Blood, b: Blood)
    reads a;
    reads b;
    requires a != null && a.Valid();
    requires b != null && b.Valid();
{
    bloodTypeToValue(a.GetBloodType()) <= bloodTypeToValue(b.GetBloodType())
}

function method bloodTypeToValue(t: BloodType): int
{
    match t {
        case AP  => 1
        case AM  => 2
        case ABP => 3
        case ABM => 4
        case BP  => 5
        case BM  => 6
        case OP  => 7
        case OM  => 8
    }
}

predicate permutation(a: seq<Blood>, b: seq<Blood>)
{
    multiset(a) == multiset(b)
}
