// lemma filterLemmaIndicies<T>(xs: seq<T>, p: (T) -> bool, i: nat, fxs: seq<T>, j: nat)
//     requires i < |xs|
//     requires fxs == filter(xs[0..i], p)
//     requires j == |fxs|
//     ensures p(xs[i]) ==> |filter(xs[0..i+1], p)| == j + 1

//     // the ith entry of filter(xs, p) == ith entry of xs such that p(x)
//     // ensures forall i: nat :: i < |xs| ==> |multiset(filter(xs, p))|
//     // ensures forall i: nat :: i < |filter(xs, p)| ==> exists j: nat :: j <= |xs| && |filter_mset(multiset(xs[0..j]), p)| == i
// {

//     // if xs == [] {

//     // } else if |xs| == 1 && p(xs[0]) {
//     //     assert filter_mset(multiset(xs[0..1])) == multiset{xs[0]};

//     // } else if |xs| == 1 && !p(xs[0]) {

//     // }
// }




// lemma filterLemmaSizes<T>(xs: seq<T>, fxs: seq<T>, p: (T) -> bool)
//     requires fxs == filter(xs, p)
//     ensures forall x: T :: x in xs && p(x) ==> multiset(xs)[x] == multiset(fxs)[x]
//     {

//     }
// {
//     forall x | x in xs && p(x) 
//         ensures multiset(xs)[x] == multiset(fxs)[x]
//     {
//         assert x in multiset(xs);
//         assert x in xs[0..|xs|];
//         assert x in multiset(fxs);
//         assert x in fxs[0..|fxs|];
//         if multiset(xs)[x] != multiset(fxs)[x] && multiset(xs)[x] < multiset(filter(xs, p))[x] {


//         } else if multiset(xs)[x] != multiset(fxs)[x] && multiset(xs)[x] > multiset(filter(xs, p))[x] {

//         }

        // if xs != [] && p(xs[0]) && x == xs[0] {
        //     assert xs == [xs[0]] + xs[1..];
        //     assert multiset(xs) == multiset{xs[0]} + multiset(xs[1..]);
        //     assert multiset(xs)[x] == multiset{xs[0]}[x] + multiset(xs[1..])[x];
        //     assert multiset(xs)[x] == multiset{xs[0]}[x] + multiset(xs[1..])[x];
        //     assert xs[0] == fxs[0];
        //     assert multiset(fxs) == multiset{xs[0]} + multiset(filter(xs[1..],p));
        //     assert x in xs;
        //     if x in xs[1..] {
        //         calc {
        //             multiset(xs)[x];
        //             ==
        //             multiset{x}[x] + multiset(xs[1..])[x];
        //             == {assert 1 == multiset{xs[0]}[x];}
        //             1 + multiset(xs[1..])[x];
        //             == { filterLemmaSizes(xs[1..], filter(xs[1..],p), p); }
        //             1 + multiset(filter(xs[1..], p))[x];
        //             ==
        //             multiset{xs[0]}[x] + multiset(filter(xs[1..],p))[x];
        //             ==
        //             multiset(fxs)[x];
        //         }
        //     } else{
        //         assert multiset(xs[1..])[x] == 0;
        //         assert multiset(filter(xs[1..], p))[x] == 0;
        //     }
        //     assert multiset(xs)[xs[0]] == multiset(fxs)[xs[0]];
        // } else if xs != [] && x != xs[0] {
        //     assert xs[0] == fxs[0];

        // } else{

        // }
//     }

// }


// lemma filterAndFilterMset<T>(ms: seq<T>, p: (T) -> bool)
//     ensures multiset(filter(ms, p)) == filter_mset(multiset(ms), p)
// {
//     assert forall x :: x in filter(ms, p) ==> x in multiset(filter(ms, p)) && p(x);
//     assert forall x :: x in filter(ms, p) ==> x in filter_mset(multiset(ms), p);
//     assert forall x :: x in filter_mset(multiset(ms), p) ==> x in filter(ms, p);
//     filterLemmaSizes(ms, filter(ms, p), p);
//     assert forall x :: x in filter(ms, p) ==> multiset(filter(ms, p))[x] == filter_mset(multiset(ms), p)[x];
// }

lemma qsMaintainsFilterLower(xs: seq<int>, x: int)
  requires forall y :: y in xs ==> y <= x 
  ensures forall sortFn: (seq<int>) -> seq<int> :: multiset(xs) == multiset(sortFn(xs)) ==> forall y :: y in sortFn(xs) ==> y <= x
{
  forall sortFn: (seq<int>) -> seq<int> | multiset(xs) == multiset(sortFn(xs)) 
    ensures forall y :: y in sortFn(xs) ==> y <= x
  {
    assert forall y :: y in multiset(xs) ==> y in xs;
    assert forall y :: y in sortFn(xs) ==> y in xs;
  }
}

lemma multiSetSlice<T(!new)>(s: seq<T>, slice: seq<T>,  p:  T -> bool) 
  requires |s| > 0
  requires s == [s[0]] + slice
  ensures multiset(slice) < multiset(s)
{
  assert s == [s[0]] + slice;
  assert multiset(s) == multiset{s[0]} + multiset(slice);
  assert multiset(slice) == multiset(s) - multiset{s[0]};
  assert multiset(slice)[s[0]] < multiset(s)[s[0]];
}

method fooTesT(xs: seq<int>)
  requires |xs| > 0
{
  // assert |filter(xs[1..], x => x < xs[0])| <= |xs|;
  assert [1,2] < [1,2,3];
  assert multiset([1,2]) < multiset([1,2,3]);
  assert multiset([1,2]) < multiset([1,2,2]);
  assert multiset([1,2]) <= multiset([1,2,3]);
  assert multiset([1,2]) <= multiset([1,2,2]);

}

lemma filterMultiSet<T(!new)>(s: seq<T>, p:  T -> bool)
  ensures multiset(filter(s, p)) <= multiset(s)
{
  if s == [] {
  }
  else {
    filterMultiSet(s[1..], p);
    calc <= {
      multiset(filter(s, p));
      multiset([s[0]]) + multiset(filter(s[1..], p));
      multiset([s[0]]) + multiset(s[1..]);
      {
        assert s == [s[0]] + s[1..];
      }
      multiset(s);
    }
  }
}

/*

    // filterMultiSet(xs[1..], ln);
    // filterMultiSet(xs[1..], gn);
    // assert multiset(xs) == multiset(filter(xs[1..], ln)) + multiset{xs[0]} + multiset(filter(xs[1..], gn));
    // assert multiset(filter(xs[1..], ln)) <= multiset(xs[1..]);
    // assert |filter(xs[1..], ln)| <= |xs[1..]| < |xs|;
    // assert multiset(xs) == multiset(filter(xs[1..], ln) + [xs[0]] + filter(xs[1..], gn));
    // assert (multiset(xs)  - multiset([xs[0]])) - multiset(filter(xs[1..], gn)) == multiset(filter(xs[1..], ln));
    // assert (multiset(xs)  - multiset([xs[0]])) - multiset(filter(xs[1..], ln)) == multiset(filter(xs[1..], gn));
    // assert |filter(xs[1..], ln)| <= |xs[1..]| < |xs|;
    // assert multiset(filter(xs[1..], ln)) < multiset(xs);
    // quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]] + quicksort(filter(xs[1..], y => y >= xs[0]))
    // var lessThanX := filter(xs[1..], y => y < xs[0]);
    // var greaterThanX := filter(xs[1..], y => y >= xs[0]); 
    // qsMaintainsFilterLower(filter(xs[1..], y => y < xs[0]), xs[0]);
    // qsMaintainsFilterLower(lessThanX, xs[0]);

    // sortedConcat(quicksort(filter(xs[1..], y => y < xs[0])) , [xs[0]]);
    // sortedConcat(quicksort(filter(xs[1..], y => y < xs[0])) + [xs[0]], quicksort(filter(xs[1..], y => y >= xs[0])));
*/