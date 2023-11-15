
predicate sorted(list: seq<int>)
{
    forall i,j :: 0 <= i < j < |list| ==> list[i] <= list[j]
}

predicate sortedRec(list: seq<int>) {
    if list == [] then true else (forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..])
}

lemma sortedDefsAreEquivalent(list: seq<int>)
    ensures sortedRec(list) <==> sorted(list)
{
    if list == [] {

    }
    if sortedRec(list) == false && sortedRec(list[1..]) == false && forall y :: y in list[1..] ==> list[0] <= y {

    }else if sortedRec(list) == false && !(forall y :: y in list[1..] ==> list[0] <= y) && sortedRec(list[1..]) {
        assert exists x, k :: x in list[1..] && x < list[0] && 0 <= k < |list| && list[k] == x;
        assert !sorted(list);
    }else if !sorted(list) {
        // assert exists i,j :: 0 <= i < j < |list| ==> list[i] > list[j] && list == list[0..i] + list[i..] && list[j] in list[1..] && !sortedRec(list[1..]);
        // assert exists i,j :: 0 <= i < j < |list| ==> list[i] > list[j];
        if j, i :| 0 <= i < j < |list| && list[i] > list[j] {
            // assert j > i;
            // assert list == list[0..i] + list[i..];
            // assert list[i] > list[j];

            // assert list[i] == list[i..][0];
            // var bigger := list[i];
            // assert bigger > list[j];
            var slice := list[i..];
            // assert slice != [];
            // assert list[i] in slice;
            // assert list[j] in slice;
            assert list[j] in slice[1..];
            // assert !sortedRec(slice);
        }
    }
}

function method insort(a: int, list: seq<int>): seq<int>
    requires sortedRec(list)
    ensures a in insort(a, list)
    ensures forall x :: x in list ==> x in insort(a, list)
{
    if list == [] then [a] else if a <= list[0] then [a] + list else [list[0]] + insort(a, list[1..])
}


lemma insortPreservesMultiset(a: int, list: seq<int>) 
    requires sortedRec(list)
    ensures multiset(insort(a,list)) == multiset{a} + multiset(list)
{
    if list == [] {
        // assert multiset(list) == multiset{};
        // assert multiset([a]) == multiset{a};
        // assert multiset(insort(a, list)) == multiset{a} + multiset(list);
    } else if a <= list[0] {
        // assert insort(a, list) == [a] + list;
        // assert multiset(insort(a, list)) == multiset{a} + multiset(list);
    } else {
        // assert insort(a, list) == [list[0]] + insort(a, list[1..]);
        assert list == [list[0]] + list[1..];
        // assert multiset(list[1..]) == multiset(list) - multiset{list[0]};
        assert multiset(insort(a, list)) == multiset{a} + multiset(list);
    }
}

lemma insortPreservesSorted(a: int, list: seq<int>)
    requires sortedRec(list)
    ensures sortedRec(insort(a, list))
{
    if list == [] {

    } else if a <= list[0] {
        assert list == [list[0]] + list[1..];
        assert sortedRec(list);
        assert insort(a, list) == [a] + list;
    } else {
        // assert list == [list[0]] + list[1..];
        // assert sortedRec(list[1..]);
        // assert insort(a, list) == [list[0]] + insort(a, list[1..]);
        // assert forall x :: x in list[1..] ==> list[0] <= x;
        // assert list[0] < a;
        // assert a in insort(a, list[1..]);
        insortPreservesMultiset(a, list[1..]);
        // assert multiset(insort(a,list[1..])) == multiset{a} + multiset(list[1..]);
        // assert forall x :: x in multiset(insort(a, list[1..])) ==> x in multiset(list[1..]) || x in multiset{a};
        // assert forall x :: x in multiset(insort(a, list[1..])) ==> x in insort(a, list[1..]);
        assert forall x :: x in insort(a, list[1..]) ==> x in multiset(insort(a, list[1..])) ==> x in multiset(list[1..]) || x in multiset{a};
        assert forall x :: x in insort(a, list[1..]) ==> x in list[1..] || x in {a};
        // assert forall x :: x in insort(a, list[1..]) ==> list[0] <= x;
    }
}

lemma insortProperties(a: int, list: seq<int>) 
    requires sortedRec(list)
    ensures multiset(insort(a,list)) == multiset{a} + multiset(list)
    ensures sortedRec(insort(a, list))
{
    insortPreservesMultiset(a, list);
    insortPreservesSorted(a, list);
}

function method isort(list: seq<int>): seq<int>
    ensures multiset(list) == multiset(isort(list))
    ensures sortedRec(isort(list))
    ensures forall x :: x in list ==> x in isort(list)
{
    if list == [] then [] else var rest := isort(list[1..]); assert list == [list[0]] + list[1..]; insortProperties(list[0], rest); insort(list[0], rest)
}

lemma isortProperties(list: seq<int>) 
    ensures forall x :: x in isort(list) ==> x in list
{
    assert multiset(list) == multiset(isort(list));
    forall x | x in isort(list) 
        ensures x in list
    {
        assert x in multiset(isort(list)) && x in multiset(list);
    }
}

method test() {
    var foo := isort([4,3,2,1]);
    assert foo == [1,2,3,4];
    // assert sortedRec(foo);
    // assert sorted(foo);
}

lemma emptySortedList(list: seq<int>, fn: (seq<int>) -> seq<int>) 
    requires multiset(list) == multiset(fn(list))
    requires sortedRec(fn(list))
    requires list == [];
    ensures fn(list) == []
{
    if x: seq<int> :| fn(list) == x && x != [] {
        var y := x[0];
        assert y !in multiset(list);
        assert y in multiset(fn(list));
        assert multiset(list) != multiset(fn(list));
        assert false;
    }
}

lemma nonEmptySortedList(list: seq<int>, fn: (seq<int>) -> seq<int>) 
    requires multiset(list) == multiset(fn(list))
    requires sortedRec(fn(list))
    requires list != [];
    ensures |fn(list)| == |list|
{
    assert |multiset(list)| == |list|;
}

lemma firstAreEqual(fn: (seq<int>) -> seq<int>) 
    requires forall list : seq<int> :: true ==> multiset(list) == multiset(fn(list)) && |list| == |fn(list)| && sortedRec(fn(list))
    ensures forall list : seq<int> :: list != [] && |list| > 0 ==>  fn(list)[0] == isort(list)[0]
{
    forall list : seq<int> | list != []
        ensures fn(list)[0] == isort(list)[0] 
    {
        var fnresult := fn(list);
        // isortProperties(list);
        // assert sortedRec(fnresult);
        var it := isort(list);
        // assert sortedRec(it);

        assert fnresult == [fnresult[0]] + fnresult[1..];
        assert sortedRec(fnresult[1..]);
        assert it == [it[0]] + it[1..];
        assert sortedRec(it[1..]);

        // assert multiset(it) == multiset(fnresult);
        // assert it[0] in list;
        assert it[0] in multiset(it);
        assert it[0] in fn(list);
        assert fnresult[0] in multiset(fnresult) && fnresult[0] in multiset(it);
        assert fnresult[0] in it;

        // if fnresult[0] != it[0] {
        //     // assert fnresult[0] in multiset(list);
        //     // assert it[0] in multiset(list);
        //     // if x :| x in multiset(it) && x == fsmallest && fsmallest < smallest {
        //     if fnresult[0] < it[0] {
        //         // assert fnresult[0] != it[0];
        //         // assert !sortedRec(it);
        //         // assert false;
        //     } else if it[0] > fnresult[0] {
        //         // assert !sortedRec(fnresult);
        //         // assert false;
        //     }
        // }
        assert fnresult[0] == it[0];
    }
}
lemma firstAreEqualList(fn: (seq<int>) -> seq<int>, alist: seq<int>) 
    requires alist != [];
    requires forall list : seq<int> :: true ==> multiset(list) == multiset(fn(list)) && |list| == |fn(list)| && sortedRec(fn(list))
    ensures fn(alist)[0] == isort(alist)[0]
{

    var fnresult := fn(alist);
    var it := isort(alist);

    assert fnresult == [fnresult[0]] + fnresult[1..];
    assert sortedRec(fnresult[1..]);
    assert it == [it[0]] + it[1..];
    assert sortedRec(it[1..]);

    assert multiset(it) == multiset(fnresult);
    assert it[0] in multiset(it);
    assert it[0] in fn(alist);
    assert fnresult[0] in multiset(it);
    assert fnresult[0] in it;
    assert fnresult[0] == it[0];
}

lemma sortedAndMultiEqual(alist: seq<int>, blist: seq<int>)
    requires |alist| >= 1
    requires |alist| == |blist|
    requires multiset(alist) == multiset(blist)
    requires sortedRec(alist) && sortedRec(blist)
    ensures alist[0] == blist[0]
{

    assert alist == [alist[0]] + alist[1..];
    assert blist == [blist[0]] + blist[1..];
    assert alist[0] in multiset(blist);
    assert blist[0] in multiset(alist);

    if !(alist[0] == blist[0]) {
        if alist[0] < blist[0] {
            assert alist[0] != blist[0];
            assert alist[0] in blist;
            assert !sortedRec(blist);
            assert false;
        } else {
            // assert blist[0] < alist[0];
            assert blist[0] in alist;
            assert !sortedRec(alist);
            assert false;
        }
    }
    // assert alist[0] == blist[0];
}

/* extra assertions 
    // assert sortedRec(alist);
    // assert sortedRec(blist);
    // assert sortedRec(alist[1..]);
    // assert sortedRec(blist[1..]);
    // assert alist[0] in multiset(alist);
    // assert blist[0] in multiset(blist);
    // assert |alist[1..]| == |blist[1..]|;
    // assert multiset(alist) == multiset(blist);
    // assert multiset(alist[1..]) == multiset(alist) - multiset{alist[0]};
    // assert multiset(blist[1..]) == multiset(blist) - multiset{blist[0]};

*/

lemma restAreEqual(fn: (seq<int>) -> seq<int>, initlist: seq<int>, prefix: seq<int>, alist: seq<int>, blist: seq<int>)
    requires forall list : seq<int> :: true ==> multiset(list) == multiset(fn(list)) && |list| == |fn(list)| && sortedRec(fn(list))
    requires |alist| == |blist|
    requires multiset(alist) == multiset(blist)
    requires sortedRec(alist) && sortedRec(blist)
    requires fn(initlist) == prefix + alist 
    requires isort(initlist) == prefix + blist 
    decreases alist
    ensures alist == blist
{
    if alist == [] && blist == [] {
    }else{
        assert alist == [alist[0]] + alist[1..];
        assert blist == [blist[0]] + blist[1..];
        assert multiset(alist[1..]) == multiset(alist) - multiset{alist[0]};
        assert multiset(blist[1..]) == multiset(blist) - multiset{blist[0]};

        sortedAndMultiEqual(alist, blist);
        restAreEqual(fn, initlist, prefix + [alist[0]], alist[1..], blist[1..]);
    }
}

/* Extra assertions

    // var fnresult: seq<int> := fn(initlist);
    // assert fnresult == prefix + alist;
    // var it := isort(initlist);
    // assert it == prefix + blist;
    // assert sortedRec(alist);
    // assert sortedRec(blist);
    // assert sortedRec(alist[1..]);
    // assert sortedRec(blist[1..]);

    // assert alist[0] in multiset(blist);
    // assert blist[0] in multiset(alist);
    // assert |alist[1..]| == |blist[1..]|;

    // assert multiset(alist) == multiset(blist);
    // assert alist[0] == blist[0];
    // assert alist == blist;
*/


lemma Excercise223(fn: (seq<int>) -> seq<int>) 
    requires forall list : seq<int> :: true ==> multiset(list) == multiset(fn(list)) && |list| == |fn(list)| && sortedRec(fn(list))
    ensures forall list : seq<int> :: fn(list) == isort(list)
{
    forall list: seq<int> | true 
        ensures fn(list) == isort(list)
    {
        if list == [] {
            emptySortedList(list, fn);
            assert fn(list) == [];
            assert isort(list) == [];
        }else{
            var fnresult: seq<int> := fn(list);
            var it: seq<int> := isort(list);
            restAreEqual(fn, list, [], fnresult, it);
        }

        /*

            // assert sortedRec(fnresult);
            // firstAreEqualList(fn, list);

            // var fsmallest := fnresult[0];
            // assert fnresult == [fnresult[0]] + fnresult[1..];
            // var smallest := it[0];
            // assert multiset(it[1..]) == multiset(list) - multiset{smallest};
            // assert multiset(it[1..]) == multiset(fnresult[1..]);
            // assert |fnresult[1..]| == |it[1..]|;
            // restAreEqual(fn, list, [it[0]], fnresult[1..], it[1..]);
            // assert it[1..] == fnresult[1..];
            // assert fsmallest == smallest;
            // assert sortedRec(fnresult[1..]);
            // assert sortedRec(it[1..]);
            // assert multiset(it) == multiset(list);
            // assert multiset(fnresult) == multiset(list);
            // assert multiset(fnresult[1..]) == multiset(list) - multiset{fsmallest};
            // assert |fnresult| == |list|;
            // assert |it| == |list|;
        */
    }
}