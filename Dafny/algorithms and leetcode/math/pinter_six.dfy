
predicate Injective<A(!new), B>(f: A -> B)
{
    forall x, y :: x != y ==> f(x) != f(y)
}
predicate isTotal<G(!new), B(!new)>(f:G -> B)
    reads f.reads;
{
     forall g:G :: f.requires(g)
}

predicate Surjective<A(!new), B(!new)>(f: A -> B) 
    reads f.reads;
    // requires isTotal(f)
{
    forall b: B :: exists a: A :: f(a) == b 
}

predicate Bijective<A(!new), B(!new)>(f: A -> B) 
{
    Injective(f) && Surjective(f)
}
// predicate surjectivee<G>(f : G -> set<G> )  {
//      forall v : set<G>  :: (exists g:G :: f(g) == v && isSubset(v) )
// }
//reads f.reads; requires forall t:: f.requires(t) // f is a total function
//ensures forall v : set :: (exists u:G :: f(u) == v)
// map m is injective if no two keys map to the same value	
predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> a != b ==> m[a] != m[b]
}

predicate isTotalMap<G(!new), B(!new)>(m:map<G,B>)
{
     forall g:G :: g in m
}

predicate mapHasValue<U(!new), V(!new)>(m: map<U,V>, x: V)
{
    exists a: U :: a in m && m[a] == x
}

predicate mapSurjective<U(!new), V(!new)>(m: map<U,V>)
    // requires forall u: U :: u in m.Keys
    requires isTotalMap(m)
{
    forall x: V :: x in m.Values
    // forall x: V :: mapHasValue(m, x)
}

// the domain of a map is the set of its keys  
function domain<U,V>(m: map<U,V>) : set<U>
	ensures domain(m) == set u : U | u in m :: u;
	ensures forall u :: u in domain(m) ==> u in m;
    ensures domain(m) == m.Keys
{
		set u : U | u in m :: u
}
 
// the domain of a map is the set of its values
function range<U,V>(m: map<U,V>) : set<V>
	ensures range(m) == set u : U | u in m :: m[u];
	ensures forall v :: v in range(m) ==> exists u :: u in m && m[u] == v;
    ensures forall k :: k in m ==> m[k] in range(m)
    ensures range(m) == m.Values
{
	set u : U | u in m :: m[u]
}

function frange<U(!new),V(!new)>(f: U -> V): iset<V>
{
    iset u: U | true :: f(u) 
}

lemma InjectiveCompositionImpliesInjective<A(!new), B(!new), C(!new)>(f: A -> B, g: B -> C,  h: A -> C)
    requires h == (x => g(f(x)))
    requires Injective(h)
    ensures Injective(f)
{
    if !Injective(f) {
        var x: A, y: A :| x != y && f(x) == f(y);
        assert h(x) == h(y);
        assert false;
    }
}

lemma SurjectiveCompositionImpliesSurjective<A(!new), B(!new), C(!new)>(f: A -> B, g: B -> C,  h: A -> C)
    // requires isTotal(f) && isTotal(g) && isTotal(h)
    requires h == (x => g(f(x)))
    requires Surjective(h)
    ensures Surjective(g)
{
    // var x: A :| assume true;
    // var y: A :| assume y != x;
}

lemma InjectiveAlsoSurjective<A>(f: A -> A)
    requires Injective(f)
    ensures Surjective(f)
{
    // if !Injective(f) {
    //     var x: A, y: A :| x != y && f(x) == f(y);
    //     assert false;
    // }
    // forall a: A | true 
    //     ensures exists b:A :: f(b) == a
    // {
    //     if(f(a) == a) {

    //     }else{
    //         var b := f(a);
    //     }
    // }
    // if !Surjective(f) {
    //     var missing: A :| forall a: A :: f(a) != missing; 
    //     assert f(missing) != missing;
    //     var someresult := f(missing);
    //     var somex: A :| f(somex) == someresult && somex != missing;
    // }
}

lemma bijectiveComposition<A(!new), B(!new), C(!new)>(f: A -> B, g: B -> C,  h: A -> C)
    requires h == (x => g(f(x)))
    requires Injective(f)
    requires Surjective(g)
    ensures Bijective(h)
{
    assert Surjective(h);
}

datatype Color = Blue | Yellow | Green | Red

function toRed(x: Color): Color {
    Red
}

function shiftColor(x: Color): Color {
    match x {
        case Red => Blue
        case Blue => Yellow
        case Yellow => Green
        case Green => Red
    }
}

method TestSurjectiveMap() {
    var hmm := map[Red := Red];
    // TotalColorMapIsTotal(hmm);
    var toRedm := map[Red := Red, Blue := Red, Yellow := Red, Green := Red];
    assert toRedm.Keys == {Red, Blue, Yellow, Green};
    assert toRedm.Values == {Red};
    // assert forall u: Color :: u in toRedm;
    TotalColorMapIsTotal(toRedm);
    assert isTotalMap(toRedm);

    // assert mapSurjective(toRedm);
    // assert toShiftm.Values == {Blue, Yellow, Green, Red};
    var toShiftm := map[Red := Blue, Blue := Yellow, Yellow := Green, Green := Red];
    assert toShiftm[Red] == Blue;
    assert toShiftm[Blue] == Yellow;
    assert toShiftm[Yellow] == Green;
    assert toShiftm[Green] == Red;

    TotalColorMapIsTotal(toShiftm);
    ColorMapIsOnto(toShiftm);
    assert mapSurjective(toShiftm);
}

method testSurjective() {
    assert isTotal(toRed);
    assert isTotal(shiftColor);

    assert toRed(Green) == Red;
    assert toRed(Red) == Red;
    assert toRed(Blue) == Red;
    assert toRed(Yellow) == Red;
    // assert Surjective(toRed); //should fail
    var test := iset{Red, Blue, Green, Yellow};
    // assert Red in test;
    // var quoi := frange(shiftColor);
    // assert test == frange(shiftColor);
    // assert exists u: Color :: shiftColor(u) == Red;

    assert shiftColor(Green) == Red;
    assert shiftColor(Red) == Blue;
    assert shiftColor(Blue) == Yellow;
    assert shiftColor(Yellow) == Green;
    assert Surjective(shiftColor); //should succeed
}




function toShiftm(): map<Color, Color>
    ensures Red in toShiftm();
    ensures Blue in toShiftm();
    ensures Yellow in toShiftm();
    ensures Green in toShiftm();

    ensures Red in range(toShiftm());
    ensures Blue in range(toShiftm());
    ensures Yellow in range(toShiftm());
    ensures Green in range(toShiftm());
    ensures toShiftm().Keys == {Red, Blue, Yellow, Green}
    ensures toShiftm().Values == {Red, Blue, Yellow, Green}
    ensures |toShiftm()| == 4
    // ensures isTotalMap(toShiftm())
    // ensures forall x : Color :: x in  (set u : Color :: u) ==> x in toShiftm()
{

    var dom := map[Red := Blue, Blue := Yellow, Yellow := Green, Green := Red];
    assert |dom.Keys| == 4;
    // assert forall x: Color :: x in {Blue, Red, Yellow, Green} && x in dom;
    dom
}

lemma mapKeysAreEquivalent<A, B>(m: map<A,B>)
    ensures |m| == |m.Keys|
{

}

lemma TotalColorMapIsTotal<B>(m: map<Color, B>) 
    requires m.Keys == {Red, Blue, Green, Yellow}
    // ensures forall u: Color :: u in m
    ensures isTotalMap(m)
{
    forall u: Color | true
        ensures u in m
    {
        if u.Red? {
            assert u in m;
        }
    }
}

lemma ColorMapIsOnto<A>(m: map<A, Color>) 
    requires m.Values == {Red, Blue, Green, Yellow}
    ensures forall u: Color :: u in m.Values
{

    forall u: Color | true
        ensures u in m.Values
    {
        if u.Red? {
            assert u in m.Values;
        }
    }
}