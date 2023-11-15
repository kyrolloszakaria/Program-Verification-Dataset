function  filter<T(!new)>(xs: seq<T>, p: (T) -> bool): seq<T>
    ensures forall x: T :: x in xs && p(x) ==> x in filter(xs, p)
    ensures forall x: T :: x !in xs && p(x) ==> x !in filter(xs, p)
    ensures forall x: T :: x in filter(xs, p) ==> p(x)
    ensures forall x: T :: x in filter(xs, p) ==> x in xs[0..|xs|]
    ensures forall x: T :: x in filter(xs, p) ==> x in xs
    ensures forall x: T :: x in xs && !p(x) ==> x !in filter(xs, p)
    // ensures forall i: nat :: i < |filter(xs, p)| ==> filter(xs, p)[i] in xs
    decreases xs
{
    if xs == [] then [] else if p(xs[0]) then assert xs == [xs[0]] + xs[1..]; [xs[0]] + filter(xs[1..], p) else assert xs == [xs[0]] + xs[1..]; filter(xs[1..], p)
}

lemma filterSplit<T(!new)>(s: seq<T>, p: T -> bool, idx: nat)
  requires 0 <= idx <= |s|
  ensures filter(s, p) == filter(s[..idx], p) + filter(s[idx..], p)
{
  if idx == 0 {
  }
  else {
    filterSplit(s[1..], p, idx-1);
    assert filter(s[1..], p) == filter(s[1..][..(idx-1)], p) + filter(s[1..][(idx-1)..], p);
    if p(s[0]) {
      calc {
        filter(s, p);
        [s[0]] + filter(s[1..], p);
        [s[0]] + filter(s[1..][..(idx-1)], p) + filter(s[1..][(idx-1)..], p);
        {
          assert s[..idx] == [s[0]] + s[1..idx];
          assert s[1..idx] == s[1..][..(idx-1)];
        }
        filter(s[..idx], p) + filter(s[1..][(idx-1)..], p);
        {
          assert s[1..][(idx-1)..] == s[idx..];
        }
        filter(s[..idx], p) + filter(s[idx..], p);
      }
    }
    else {}
  }
}

lemma filterMultiSetSlice<T(!new)>(s: seq<T>, slice: seq<T>,  p:  T -> bool) 
  requires |s| > 0
  requires s == [s[0]] + slice
  ensures multiset(filter(slice, p)) < multiset(s)
{
  assert s == [s[0]] + slice;
  assert multiset(s) == multiset{s[0]} + multiset(slice);
  if p(s[0]) {
    filterLemmaSizes(s[1..], filter(s[1..], p), p);
    if s[0] in multiset(s[1..]) {

    }else{
      assert s[0] !in filter(s[1..], p);
      assert multiset(filter(slice, p))[s[0]] < multiset(s)[s[0]];
    }
  }else{
    filterLemmaSizes(s[1..], filter(s[1..], p), p);
    assert !p(s[0]);
    assert s[0] in multiset(s);
    assert s[0] !in filter(slice, p);
    assert multiset(filter(slice, p))[s[0]] < multiset(s)[s[0]];
  }
  // assert multiset(slice) == multiset(s) - multiset{s[0]};
  // assert multiset(slice)[s[0]] < multiset(s)[s[0]];
}
lemma filterLemmaSizes<T(!new)>(xs: seq<T>, fxs: seq<T>, p: (T) -> bool)
    requires fxs == filter(xs, p)
    ensures forall x: T :: x in xs && p(x) ==> multiset(xs)[x] == multiset(fxs)[x]
{
  if xs == [] {

  } else {
    assert xs == [xs[0]] + xs[1..];
    filterLemmaSizes(xs[1..], filter(xs[1..], p), p);
    if p(xs[0]) {
      // assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
      // assert multiset(xs)[xs[0]] == multiset{xs[0]}[xs[0]] + multiset(xs[1..])[xs[0]];
      // assert multiset(filter(xs, p)) == multiset{xs[0]} + multiset(filter(xs[1..], p));
      // filterSplit(xs, p, 1);
      // assert filter(xs, p) == filter(xs[..1], p) + filter(xs[1..], p);
      // assert multiset(filter(xs, p))[xs[0]] == multiset(filter(xs[..1], p))[xs[0]] + multiset(filter(xs[1..], p))[xs[0]];
      // assert xs[..1] == [xs[0]];
      calc {
        multiset(fxs)[xs[0]];
        ==
        multiset(filter(xs[..1], p))[xs[0]] + multiset(filter(xs[1..], p))[xs[0]];
        ==
        multiset(filter([xs[0]], p))[xs[0]] + multiset(filter(xs[1..], p))[xs[0]];
        ==
        multiset([xs[0]])[xs[0]] + multiset(filter(xs[1..], p))[xs[0]];
        ==
        1 + multiset(filter(xs[1..], p))[xs[0]];
        ==
        multiset{xs[0]}[xs[0]] + multiset(xs[1..])[xs[0]];
        ==
        multiset(xs)[xs[0]];
      }
    } else{
      assert xs[0] !in filter(xs, p);
    }
  }
}

lemma multisetAndSeqs<T(!new)>(xs: seq<T>)
    ensures |multiset(xs)| == |xs|
{
}

predicate isNegatedBooleanFn<T(!new)>(xs: seq<T>, ms: multiset<T>, p: (T) -> bool, q: (T) -> bool) {
    (forall x: T :: p(x) ==> q(x) == false) && (forall x: T :: !p(x) ==> q(x) == true)
}

function filter_mset<T(!new)>(ms: multiset<T>, p: (T) -> bool): multiset<T> 
    ensures forall x :: x in ms && p(x) ==> x in filter_mset(ms, p) && ms[x] == filter_mset(ms, p)[x]
    ensures forall x :: x in filter_mset(ms, p) ==> p(x)
    ensures forall x :: x in filter_mset(ms, p) ==> x in ms
    ensures forall x: T :: x !in ms && p(x) ==> x !in filter_mset(ms, p)
{
    if ms == multiset{} then multiset{} else
   var x :| x in ms; if p(x) then var result := multiset{}; result[x := ms[x]] + filter_mset(ms[x := 0], p) else filter_mset(ms[x := 0], p)

}

lemma filterMS<T(!new)>(xs: seq<T>, p: (T) -> bool)
 ensures exists q: (T) -> bool :: isNegatedBooleanFn(xs, multiset(xs), p, q)
{
  var q: (T) -> bool := y => !p(y);
  forall x | x in xs
    ensures x in xs && p(x) ==> !q(x)
  {
    if p(x) {
        assert !q(x);
    }
  }
  assert isNegatedBooleanFn(xs,multiset(xs), p, q);
//   assert forall x: T :: x in xs && p(x) ==> !q(x);
  
}
lemma filterMsetAndSum<T(!new)>(xs: seq<T>, ms: multiset<T>, p: (T) -> bool)
    requires ms == multiset(xs)
    ensures exists Q: (T) -> bool :: isNegatedBooleanFn(xs, ms, p, Q) && (filter_mset(ms, p) + filter_mset(ms, Q)) == ms
{
    // filterMS(xs, p);
    // var Q :| isNegatedBooleanFn(xs, p, Q);
    var Q := (y) => !p(y);
    var sum_ms := filter_mset(ms, p) + filter_mset(ms, Q);
    forall x | x in ms 
        ensures ms[x] == sum_ms[x]
    {
        if p(x) {
            assert x in filter_mset(ms, p);
            assert filter_mset(ms, p)[x] == ms[x];
            assert x in sum_ms;
            assert sum_ms[x] == ms[x];
        }else {
            assert x in filter_mset(ms, Q);
            assert filter_mset(ms, Q)[x] == ms[x];
            assert x in sum_ms;
            assert sum_ms[x] == ms[x];
        }
    }
    assert sum_ms == ms;
}

lemma filterMultiSetThings<T(!new)>(xs: seq<T>, ms: multiset<T>,  p: (T) -> bool, q: (T) -> bool)
    requires ms == multiset(xs)
    requires isNegatedBooleanFn(xs, ms, p, q)
    ensures (filter_mset(ms, p) + filter_mset(ms, q)) == ms
{
    var sum_ms := filter_mset(ms, p) + filter_mset(ms, q);
    assert forall x :: x in xs ==> x in ms;
    forall x | x in ms 
        ensures ms[x] == sum_ms[x]
    {
        if p(x) {
            assert x in filter_mset(ms, p);
            assert filter_mset(ms, p)[x] == ms[x];
            assert x in sum_ms;
            assert sum_ms[x] == ms[x];
        }else if !p(x) {
            assert x in xs && x in ms && !p(x);
            assert q(x); 
            assert x in filter_mset(ms, q);
            assert filter_mset(ms, q)[x] == ms[x];
            assert x in sum_ms;
            assert sum_ms[x] == ms[x];
        }
    }
    assert sum_ms == ms;
}

method TestNegated(xs: seq<int> )
requires |xs| > 0
{
  assert isNegatedBooleanFn(xs, multiset(xs), p => p < xs[0], q => q >= xs[0]);
}

lemma filterPreservesMultiset(xs: seq<int>)
  requires |xs| > 0
  // ensures multiset(xs) == multiset(filter(xs[1..], y => y < xs[0]) + [xs[0]] + filter(xs[1..], y => y >= xs[0]))
  ensures multiset(xs) == multiset(filter(xs[1..], lessThanFirst(xs)) + [xs[0]] + filter(xs[1..], greaterOrEqualFirst(xs)))
{
  assert xs == [xs[0]] + xs[1..];
  assert multiset(xs) == multiset([xs[0]]) + multiset(xs[1..]);
  filterAndFilterMset(xs, lessThanFirst(xs));
  filterAndFilterMset(xs, greaterOrEqualFirst(xs));
  // assert isNegatedBooleanFn(xs[1..], multiset(xs[1..]), y => y < xs[0], y => y >= xs[0]);
  // calc {
  //   multiset(xs[1..]);
  //   ==
  //   multiset(filter(xs[1..], y => y < xs[0])  + filter(xs[1..], y => y >= xs[0]));
  // }
}


lemma filterAndFilterMset<T(!new)>(ms: seq<T>, p: (T) -> bool)
    ensures multiset(filter(ms, p)) == filter_mset(multiset(ms), p)
{
    // assert forall x :: x in filter(ms, p) ==> x in multiset(filter(ms, p)) && p(x);
    // assert forall x :: x in filter(ms, p) ==> x in filter_mset(multiset(ms), p);
    // assert forall x :: x in filter_mset(multiset(ms), p) ==> x in filter(ms, p);
    filterLemmaSizes(ms, filter(ms, p), p);
    // assert forall x :: x in filter(ms, p) ==> multiset(filter(ms, p))[x] == filter_mset(multiset(ms), p)[x];
}

predicate sortedRec(list: seq<int>) {
    if list == [] then true else (forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..])
}
predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}


lemma sortedConcat(xs: seq<int>, ys: seq<int>)
  requires sortedRec(xs)
  requires sortedRec(ys)
  requires listPartition(xs,ys)
  ensures sortedRec(xs + ys)
{
  if xs == [] || ys == [] {
    if xs == [] {
      assert xs + ys == ys;
      assert sortedRec(xs + ys);
    } else if ys == [] {
      assert xs + ys == xs;
      assert sortedRec(xs+ys);
    }
  }else{
    assert sortedRec([xs[0]]);
    assert sortedRec([ys[0]]);
    var sum := xs + ys;
    assert xs == [xs[0]] + xs[1..];
    assert ys == [ys[0]] + ys[1..];

    assert xs[0] in xs;
    assert forall y :: y in ys ==> xs[0] <= y;
    assert forall xz :: xz in xs[1..] ==> xz in xs && forall y :: y in ys ==> xz <= y;
    sortedConcat(xs[1..], ys);
    assert xs+ys == [xs[0]] + (xs[1..]+ys);
    assert sortedRec(xs + ys );
  }
}



function lessThanFirst(xs: seq<int>): (int) -> bool
  requires |xs| > 0
{
  y => y < xs[0]
}

function greaterOrEqualFirst(xs: seq<int>): (int) -> bool
  requires |xs| > 0
{
  y => y >= xs[0]
}

function {:opaque} quicksort(xs: seq<int>): seq<int>
  // ensures sortedRec(quicksort(xs))
  ensures multiset(xs) == multiset(quicksort(xs))
  ensures xs == [] ==> quicksort(xs) == []
  ensures xs == [] ==> quicksort(xs) == []
  decreases multiset(xs)
{
   if xs == [] then [] else 
    assert xs == [xs[0]] + xs[1..]; 
    filterPreservesMultiset(xs);
    // var ln := y => y < xs[0];
    // var gn := y => y >= xs[0];
    var ln := lessThanFirst(xs);
    var gn := greaterOrEqualFirst(xs);
    filterMultiSetSlice(xs, xs[1..], ln);
    filterMultiSetSlice(xs, xs[1..], gn);
    quicksort(filter(xs[1..], ln)) + [xs[0]] + quicksort(filter(xs[1..], gn))
}



predicate listPartition(xs: seq<int>, ys: seq<int>)
{
  forall x :: x in xs ==> forall y :: y in ys ==> x <= y
}

lemma quicksortPreservesRelations(xs: seq<int>, ys: seq<int>)
  requires listPartition(xs, ys)
  ensures listPartition(quicksort(xs), ys)
  // ensures forall x :: x in quicksort(xs) ==> forall y :: y in ys ==> x <= y
{
  assert multiset(xs) == multiset(quicksort(xs));
  assert forall x :: x in multiset(quicksort(xs)) ==> x in quicksort(xs) && x in xs;
}


lemma quicksortDef(xs: seq<int>)
  requires |xs| > 0
  ensures quicksort(xs) == quicksort(filter(xs[1..], lessThanFirst(xs))) + [xs[0]] + quicksort(filter(xs[1..], greaterOrEqualFirst(xs)))
{
  reveal quicksort();
}

lemma quicksortBreakdown(xs: seq<int>)
  requires |xs| > 0
{

    assert xs == [xs[0]] + xs[1..]; 
    var ln := lessThanFirst(xs);
    var gn := greaterOrEqualFirst(xs);
    var lessThan := filter(xs[1..], ln);
    var greaterThan := filter(xs[1..], gn);

    var sortedLt := quicksort(lessThan);
    var sortedGt := quicksort(greaterThan);
    quicksortDef(xs);
    assert quicksort(xs) == quicksort(lessThan) + [xs[0]] + quicksort(greaterThan);
    assert sortedLt == quicksort(lessThan);
    assert sortedGt == quicksort(greaterThan);
    assert quicksort(xs) == sortedLt + [xs[0]] + sortedGt;
}

lemma quicksortSorted(xs: seq<int>)
  ensures sortedRec(quicksort(xs))
  decreases multiset(xs)
{
  if xs == [] {
    assert quicksort(xs) == [];
    assert sortedRec(quicksort(xs));
  }else{
    assert xs == [xs[0]] + xs[1..]; 
    var ln := lessThanFirst(xs);
    var gn := greaterOrEqualFirst(xs);
    if xs[1..] == [] {
      assert xs == [xs[0]];
      assert sortedRec([xs[0]]);
    }else{
      // filterPreservesMultiset(xs[1..]);
      filterMultiSetSlice(xs, xs[1..], ln);
      filterMultiSetSlice(xs, xs[1..], gn);
      var lessThan := filter(xs[1..], ln);
      var greaterThan := filter(xs[1..], gn);

      var sortedLt := quicksort(lessThan);
      var sortedGt := quicksort(greaterThan);
      // assert multiset(lessThan) == multiset(sortedLt);
      assert multiset(greaterThan) == multiset(sortedGt);
      assert forall y :: y in multiset(sortedGt) ==> y in multiset(greaterThan) && y in sortedGt && y in greaterThan;

      assert listPartition(lessThan, [xs[0]]);
      quicksortPreservesRelations(lessThan, [xs[0]]);
      assert listPartition(sortedLt, [xs[0]]);
      assert forall x :: x in sortedLt ==> forall y :: y in [xs[0]] ==> x < y ==> x < xs[0];
   

      forall x | x in sortedLt + [xs[0]] 
        ensures forall y :: y in sortedGt ==> x <= y
      {
        forall y | y in sortedGt 
          ensures x <= y
        {
          assert y in greaterThan;
          assert y >= xs[0];
          if x in sortedLt {
            assert forall z :: z in [xs[0]] ==> x < z ==> x < xs[0];
          }else if x in [xs[0]] {
            assert x == xs[0];
            assert y >= xs[0];
          }

        }
      }
      quicksortSorted(lessThan);
      quicksortSorted(greaterThan);
      assert listPartition(sortedLt + [xs[0]], sortedGt);
      // assert sortedRec(sortedLt);
      // assert sortedRec(sortedGt);
      sortedConcat(sortedLt, [xs[0]]);
      assert sortedRec(sortedLt+[xs[0]]);
      sortedConcat(sortedLt + [xs[0]], sortedGt);
      assert sortedRec((sortedLt + [xs[0]]) + sortedGt);
      quicksortDef(xs);
      assert quicksort(xs) == sortedLt + [xs[0]] + sortedGt;
      assert sortedRec(quicksort(xs));
    }
  }
}

// /*
//    // forall x | x in quicksort(lessThan) + [xs[0]] 
//       //   ensures forall y :: y in quicksort(greaterThan) ==> x <= y
//       // {
//       //   forall y | y in quicksort(greaterThan) 
//       //     ensures x <= y
//       //   {
//       //     assert y in greaterThan;
//       //     assert y >= xs[0];
//       //     if x in quicksort(lessThan) {
//       //       assert forall z :: z in [xs[0]] ==> x < z ==> x < xs[0];
//       //     }
//       //   }
//       // }
//       // assert forall x :: x in sortedLt + [xs[0]]  ==> forall y :: y in quicksort(filter(xs[1..], y => y >= xs[0])) ==> y >=  x;
//       // quicksortPreservesRelations(quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]], quicksort(filter(xs[1..], y => y >= xs[0])));
// k
//       // assert sortedRec(quicksort(filter(xs[1..], y => y < xs[0])));
//       p
//       // assert forall x :: x in quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]]  ==> forall y :: y in quicksort(filter(xs[1..], y => y >= xs[0])) ==> y >=  x;
//       // sortedConcat(quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]], quicksort(filter(xs[1..], y => y >= xs[0])));
      // assert listPartition(quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]], quicksort(filter(xs[1..], y => y >= xs[0])));
      // assert sortedRec((quicksort(lessThan) + [xs[0]]) + quicksort(greaterThan));
      // assert sortedRec(quicksort(xs));
      // assert sortedRec(sortedLt + [xs[0]]);
      // assume sortedRec(sortedLt);
      // assume sortedRec(sortedGt);
      // // assert y in quicksort(greaterThan) ==> y in greaterThan;
      // assert forall y :: y in [xs[0]] ==> forall x :: x in greaterThan ==> x >= y;
// */