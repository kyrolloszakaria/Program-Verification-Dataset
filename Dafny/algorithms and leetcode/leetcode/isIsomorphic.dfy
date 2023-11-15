/*
https://leetcode.com/problems/isomorphic-strings/
Given two strings s and t, determine if they are isomorphic.

Two strings s and t are isomorphic if the characters in s can be replaced to get t.

All occurrences of a character must be replaced with another character while preserving the order of characters. No two characters may map to the same character, but a character may map to itself.

ways to express this:
there exists a map such that 
there exist a function f, such that forall  i | 0 <= i < |s| ==> f(s[i]) == t[i]
requires that f be an injective function
*/
predicate Injective(f: char -> char)
{
    forall x, y :: x != y ==> f(x) != f(y)
}

predicate InjectiveMap<T,U>(f: map<T, U>)
{
    forall x, y :: x in f && y in f && x != y ==> f[x] != f[y]
}

// function method applyMapSeq<T,U>(s: seq<T>, smap: map<T, U>): seq<U>
//     requires forall x :: x in s ==> x in smap
//     ensures if |s| == 0 then applyMapSeq(s, smap) == [] else applyMapSeq(s, smap) == [smap[s[0]]] + applyMapSeq(s[1..], smap)
// {
//     if |s| == 0 then [] else [smap[s[0]]] + applyMapSeq(s[1..], smap)
// }

function method aps<T,U>(s: seq<T>, smap: map<T,U>): seq<U>
    requires forall x :: x in s ==> x in smap
{
    seq(|s|, i requires 0 <= i < |s| => smap[s[i]])
}

method Test() {
    var test_s: string := "adda";
    var sMap: map<char, nat> := map['a' := 1, 'd' := 2];
    assert test_s[0..2] == "ad";
    assert aps(test_s[0..2], sMap) == [1,2];
}

function intsLessThan(n: nat): set<nat>
    ensures intsLessThan(n) == set x | 0 <= x < n
{
    if n == 0 then {} else {n-1} + intsLessThan(n-1)
}

method isIsomorphic(s: string, t: string) returns (answer: bool) 
    requires 1 <= |s|
    requires |t| == |s|
    // ensures answer ==> exists fn: (char) -> char :: Injective(fn) && forall i :: 1 <= i < |s| <= |t| ==> fn(s[i]) == t[i]
    ensures answer ==> exists fn: map<char,char> :: InjectiveMap(fn) && forall i :: 1 <= i < |s| <= |t| ==> s[i] in fn && fn[s[i]] == t[i]
    ensures answer ==> exists gn: map<char,char> :: InjectiveMap(gn) && forall i :: 1 <= i < |s| <= |t| ==> t[i] in gn && gn[t[i]] == s[i]
{
    var sMap: map<char, nat> := map[];
    var sTransform: seq<nat> := [];

    var tMap: map<char, nat> := map[];
    var tTransform: seq<nat> := [];

    var sIndex: nat := 0;
    // ghost var gsIndex: nat := 0;
    ghost var sIndices: set<nat> := {};
    var tIndex: nat := 0;
    for i := 0 to |s| 
        invariant forall j :: 0 <= j < i ==> s[j] in sMap
        invariant sIndices == intsLessThan(sIndex)
        invariant sIndex == |sMap|
        invariant sMap.Values == sIndices
        invariant InjectiveMap(sMap)
        invariant sTransform == aps(s[0..i], sMap)
    {
        if s[i] !in sMap {
            ghost var oldsMap := sMap;
            assert sIndex !in sIndices;
            assert sIndex !in sMap.Values;
            sMap := sMap[s[i] := sIndex];
            assert sMap == oldsMap + map[s[i] := sIndex];

            // assert forall z :: z in sMap && z != s[i] ==> sMap[z] != sIndex;
            sIndices := sIndices + {sIndex};
            assert sIndex in sMap.Values && sIndex in sIndices;
            sIndex := sIndex + 1;
        }
        sTransform := sTransform + [sMap[s[i]]];
    }
    
    ghost var tIndices: set<nat> := {};
    for i := 0 to |t| 
        invariant forall j :: 0 <= j < i ==> t[j] in tMap
        invariant tIndices == intsLessThan(tIndex)
        invariant tIndex == |tMap|
        invariant tMap.Values == tIndices
        invariant InjectiveMap(tMap)
        invariant tTransform == aps(t[0..i], tMap)
    {
        if t[i] !in tMap {
            ghost var tOld := tMap;
            assert tIndex !in tIndices;
            assert tIndex !in tMap.Values;
            tMap := tMap[(t[i]) := tIndex];
            assert tMap == tOld + map[t[i] := tIndex];
            tIndices := tIndices + {tIndex};
            assert tIndex in tMap.Values && tIndex in tIndices;
            tIndex := tIndex + 1;
        }
        tTransform := tTransform + [tMap[t[i]]];
    }
    assert sTransform == aps(s, sMap);
    assert tTransform == aps(t, tMap);
    if sMap.Values == tMap.Values && sTransform == tTransform {
        injectiveMapCanBeMade(sMap, tMap, s, t, sTransform, tTransform);
        return true;
    }else{
        return false;
    }
}

function createMap(lmap: map<char,nat>, rmap: map<char, nat>): map<char, char>
    requires InjectiveMap(lmap)
    requires InjectiveMap(rmap)
    requires rmap.Values == lmap.Values
    ensures forall x :: x in lmap ==> x in createMap(lmap, rmap)
    ensures InjectiveMap(createMap(lmap, rmap))
{
    map xs : char | xs in lmap :: injectiveMapHasKey(rmap, lmap[xs]); var rkey :| rkey in rmap && rmap[rkey] == lmap[xs]; rkey
}

lemma injectiveMapHasKey<T,U>(lmap: map<T, U>, value: U)
    requires InjectiveMap(lmap)
    requires value in lmap.Values
    ensures exists t :: t in lmap && lmap[t] == value
{

}

lemma createMapHasAllTheValues(lmap: map<char,nat>, rmap: map<char, nat>, s: string, t: string, smapped: seq<nat>, tmapped: seq<nat>)
    requires InjectiveMap(lmap)
    requires InjectiveMap(rmap)
    requires forall j :: 0 <= j < |s| ==> s[j] in lmap
    requires forall j :: 0 <= j < |t| ==> t[j] in rmap
    requires smapped == aps(s, lmap)
    requires tmapped == aps(t, rmap)
    requires smapped == tmapped
    requires rmap.Values == lmap.Values
    ensures createMap(lmap, rmap).Values == rmap.Keys
    ensures forall i :: 0 <= i < |s| ==> createMap(lmap, rmap)[s[i]] == t[i]
{
    var test_map := createMap(lmap, rmap);
    assert createMap(lmap, rmap).Keys == lmap.Keys;
    forall x | x in rmap.Keys 
        ensures x in createMap(lmap, rmap).Values
    {
        assert rmap[x] in lmap.Values;
    }

    forall i | 0 <= i < |s|
        ensures createMap(lmap, rmap)[s[i]] == t[i]
    {
        // assert smapped[i] == tmapped[i];
        // //to further explain
        // assert lmap[s[i]] == smapped[i];
        // assert rmap[t[i]] == tmapped[i];
        var k :| k in rmap.Keys && rmap[k] == lmap[s[i]];
        calc {
            createMap(lmap, rmap)[s[i]];
            k;
            { 
            assert smapped[i] == tmapped[i]; 
            assert lmap[s[i]] == smapped[i];
            assert rmap[t[i]] == tmapped[i];
            }
            t[i];
        }
    }

}

lemma injectSubtract<T, U>(lmap: map<T, U>, val: T)
    requires InjectiveMap(lmap)
    requires val in lmap
    ensures InjectiveMap(lmap - {val})
    {

    }

lemma injectSubtractValues<T, U>(lmap: map<T, U>, key: T, val: U)
    requires InjectiveMap(lmap)
    requires key in lmap
    requires lmap[key] == val
    ensures (lmap - {key}).Values == lmap.Values - {val}
    {
        var removed := lmap - {key};
        assert lmap.Values == {val} + (lmap.Values-{val});
        assert lmap == (lmap - {key}) + map[key := val];
    }

lemma injectMapsOneToOne<T, U>(lmap: map<T, U>)
    requires InjectiveMap(lmap)
    ensures |lmap.Keys| == |lmap.Values|
{
    if lmap.Keys != {} {
        var x :| x in lmap.Keys;
        var lx := lmap[x];
        var removed := lmap - {x};
        assert lmap == (lmap - {x}) + map[x := lx];
        // assert removed.Keys == lmap.Keys - {x};
        // assert forall y :: y in lmap && x != y ==> lx != lmap[y];
        // assert InjectiveMap(removed);
        // assert lmap.Values == {lx} + (lmap.Values-{lx});
        // assert lx !in removed.Values;
        assert removed.Values == (lmap.Values - {lx});
        injectMapsOneToOne(removed);

        // calc {
        //     |lmap.Keys|;
        //     {assert lmap == (lmap - {x}) + map[x := lmap[x]];}
        //     |(lmap.Keys - {x}) + {x}|;
        //     |lmap - {x}| + 1;
        //     {injectSubtract(lmap, x);injectMapsOneToOne(lmap - {x});}
        //     |lmap.Values - {lx}| + 1;
        //     |(lmap.Values-{lx})+{lx}|;
        //     |lmap.Values|;
        // }
    }
}

lemma sameSizeMaps(lmap: map<char,nat>, rmap: map<char, nat>)
    requires InjectiveMap(lmap)
    requires InjectiveMap(rmap)
    requires rmap.Values == lmap.Values
    ensures |rmap.Keys| == |lmap.Keys|
{
    injectMapsOneToOne(lmap);
    injectMapsOneToOne(rmap);
}

lemma injectiveMapCanBeMade(lmap: map<char,nat>, rmap: map<char, nat>, s: string, t: string, smapped: seq<nat>, tmapped: seq<nat>)
    requires InjectiveMap(lmap)
    requires InjectiveMap(rmap)
    requires rmap.Values == lmap.Values
    requires |s| == |t| && |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] in lmap
    requires forall i :: 0 <= i < |t| ==> t[i] in rmap
    requires smapped == aps(s, lmap)
    requires tmapped == aps(t, rmap)
    requires smapped == tmapped
    ensures exists fn: map<char,char> :: InjectiveMap(fn) && forall i :: 1 <= i < |s| <= |t| ==> s[i] in fn && fn[s[i]] == t[i]
    ensures exists gn: map<char,char> :: InjectiveMap(gn) && forall i :: 1 <= i < |s| <= |t| ==> t[i] in gn && gn[t[i]] == s[i]
{
    var fn := createMap(lmap, rmap);
    var gn := createMap(rmap, lmap);
    // assert InjectiveMap(fn);
    // assert InjectiveMap(gn);
    createMapHasAllTheValues(lmap, rmap, s, t, smapped, tmapped);
}

/*
could convert fn to a map
given two sequences that are the same formed by two maps, such that
*/