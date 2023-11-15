/*
 * Dafny program verifier version 1.9.7.30401, Copyright (c) 2003-2016, Microsoft.
 *
 * Dafny program verifier finished with 21 verified, 0 errors
 * Program compiled successfully
 * Running...
 *
 * BloodItem.BloodItem(BloodType.APlus, 123), BloodItem.BloodItem(BloodType.AMinus, 456)
 * BloodItem.BloodItem(BloodType.APlus, 123), BloodItem.BloodItem(BloodType.AMinus, 456)
 * BloodItem.BloodItem(BloodType.ABPlus, 1), BloodItem.BloodItem(BloodType.BMinus, 9)
 * BloodItem.BloodItem(BloodType.BMinus, 9), BloodItem.BloodItem(BloodType.ABPlus, 1)
 */

/**
 * Datatype to model blood types.
 */
datatype BloodType = APlus | AMinus
        | BPlus | BMinus
        | OPlus | OMinus
        | ABPlus | ABMinus

/**
 * Refine the blood type to an integer to introduce
 * ordering.
 */
function method refineBloodType(a: BloodType): int
{
    match a {
        case APlus   => 0
        case AMinus  => 1
        case BPlus   => 2
        case BMinus  => 3
        case ABPlus  => 4
        case ABMinus => 5
        case OPlus   => 6
        case OMinus  => 7
    }
}

/**
 * Blood type comparator.
 *
 * Returns true if a is (strictly) less than b.
 */
function method compareBloodTypeLt(a: BloodType, b: BloodType): bool
{
    refineBloodType(a) < refineBloodType(b)
}

/**
 * Datatype to model an instance of blood.
 *
 * An instance of blood has various data attached to it.
 */
datatype BloodItem = BloodItem(bloodType: BloodType, timeProduced: nat)

/**
 * BloodItem comparator specified according to the following ruleset.
 *
 * - Blood types come first, according to compareBloodType().
 *   (e.g. A+ < A- < B < AB < O)
 * - Each blood in the group is sorted by donation time, oldest first.
 *   (e.g. lowest donation time comes first)
 *
 * This means that picking the first occurence of each blood type
 * guarantees oldest-first semantics.
 */
function method compareBloodItemLt(a: BloodItem, b: BloodItem): bool
{
    if compareBloodTypeLt(a.bloodType, b.bloodType) then true
    else (
        // Check whether we can establish equivalency
        if compareBloodTypeLt(b.bloodType, a.bloodType)
        // Not equivalent, b < a.
        then false
        // Indeterminate (equivalent), compare time.
        else a.timeProduced < b.timeProduced
    )
}

/**
 * Less than or equals version of compareBloodItemLt().
 */
function method compareBloodItemLe(a: BloodItem, b: BloodItem): bool
{
    // Either less-than relation
    compareBloodItemLt(a, b)
    || (
        // Or equivalency relation
           !compareBloodItemLt(a, b)
        && !compareBloodItemLt(b, a)
    )
}

/**
 * Predicate that the inventory is sorted according to
 * compareBloodItemLt().
 *
 * NOTE: Cannot be compiled under Dafny 1.9.7.
 */
predicate sortedGroupBloodInventory(inv: array<BloodItem>)
    reads inv
    requires inv != null
{
    forall i: nat, j: nat
    :: i < j < inv.Length
    ==> compareBloodItemLe(inv[i], inv[j])
}

/**
 * Predicate that the two inventories are permutations of each other.
 */
predicate permutationBloodInventory(xs: array<BloodItem>, ys: array<BloodItem>)
    reads xs, ys
    requires xs != null && ys != null
    requires xs.Length == ys.Length
{
    multiset(xs[..]) == multiset(ys[..])
    &&
    // Ensures that an equivalent item exists for every item, bidirectionally
    // Necessary because multiset doesn't see "into" the data :(
    // (i.e. multiset does not establish equality of fields)
    // TODO: Does not detect corruption of duplicates yet
    forall i: nat
    :: i < xs.Length
    ==> exists j: nat
        :: j < xs.Length
        && xs[j] == ys[i]
    &&
    forall i: nat
    :: i < xs.Length
    ==> exists j: nat
        :: j < xs.Length
        && ys[j] == xs[i]
}

/**
 * Sort the blood inventory according to bloodGroupSorted()
 * semantics.
 *
 * The expectation being that this method is called before blood
 * is popped from the inventory.
 */
method BloodInventorySort(inv: array<BloodItem>)
    modifies inv
    requires inv != null
    ensures permutationBloodInventory(inv, old(inv))
    ensures sortedGroupBloodInventory(inv)
{
    // assume permutationBloodInventory(inv, old(inv));
    // assume sortedGroupBloodInventory(inv);
    MergeSort(inv);
}

method Main()
{
    TestBloodInventorySortEnsuresStrength();
}

/* ---------------------------------------------------------- */
/* - MergeSort.dfy copied and modified below - synchronise! - */
/* - Changed items:                                         - */
/* -     array<int> to array<BloodItem>                     - */
/* -     comparison <= to compare function                  - */
/* ---------------------------------------------------------- */

method MergeSort(a: array<BloodItem>)
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

method DoMergeSort(a: array<BloodItem>, l: int, r: int)
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

  ghost var g1 := a[..];
  DoMergeSort(a, m, r);
  assert a[l..m] == g1[l..m];

  assert a[l..m] + a[m..r] == a[l..r];
  assert old(a[l..m]) + old(a[m..r]) == old(a[l..r]);

  Merge(a, l, m, r);
}

method Merge(a: array<BloodItem>, l: int, m: int, r: int)
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
  var b := new BloodItem[a.Length];
  var i := l;
  var j := m;
  var k := l;

  while i < m || j < r
    decreases m - i + r - j;
    invariant l <= i <= m && m <= j <= r;
    invariant k == l + (i - l) + (j - m);
    invariant sortedFromTo(b, l, k);
    invariant k > l && i < m ==> compareBloodItemLe(b[k - 1], a[i]);
    invariant k > l && j < r ==> compareBloodItemLe(b[k - 1], a[j]);
    invariant permutation(b[l..k], a[l..i] + a[m..j]);
    invariant forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]);
  {
    if i == m {
      b[k] := a[j];
      j := j + 1;
    } else if j == r {
      b[k] := a[i];
      i := i + 1;
    } else if compareBloodItemLe(a[i], a[j]) {
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

predicate sorted(a: array<BloodItem>)
  requires a != null;
  reads a;
{
  sortedFromTo(a, 0, a.Length)
}


predicate sortedFromTo(a: array<BloodItem>, l: int, r: int)
    reads a
    requires a != null
    requires 0 <= l <= r <= a.Length
{
    forall i, j :: l <= i < j < r ==> compareBloodItemLe(a[i], a[j])
}

predicate permutation(a: seq<BloodItem>, b: seq<BloodItem>)
{
  multiset(a) == multiset(b)
}

/* ---------------------------------------------------------- */
/* - This method must come at the very end for some reason  - */
/* ---------------------------------------------------------- */

/**
 * Test that the postcondition of BloodInventorySort()
 * is strong enough for Dafny to infer that picking the
 * first item is indeed the oldest item.
 */
method TestBloodInventorySortEnsuresStrength()
{
    var inv := new BloodItem[2];
    inv[0] := BloodItem(APlus, 123);
    inv[1] := BloodItem(AMinus, 456);
    print inv[0], ", ";
    print inv[1], "\n";

    BloodInventorySort(inv);
    print inv[0], ", ";
    print inv[1], "\n";
    assert inv[0].bloodType.APlus?;
    assert inv[0].timeProduced == 123;
    assert inv[0].timeProduced != 456;
    assert inv[1].bloodType.AMinus?;
    assert inv[1].timeProduced == 456;
    assert inv[1].timeProduced != 123;

    inv[0] := BloodItem(ABPlus, 1);
    inv[1] := BloodItem(BMinus, 9);
    print inv[0], ", ";
    print inv[1], "\n";

    BloodInventorySort(inv);
    print inv[0], ", ";
    print inv[1], "\n";
    assert inv[0].bloodType.BMinus?;
    assert inv[0].timeProduced == 9;
    assert inv[0].timeProduced != 1;
    assert inv[1].bloodType.ABPlus?;
    assert inv[1].timeProduced == 1;
    assert inv[1].timeProduced != 9;
}
