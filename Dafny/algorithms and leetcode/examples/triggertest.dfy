//https://stackoverflow.com/questions/48963978/why-cant-dafny-verify-certain-easy-set-cardinality-and-relational-propositions
function method Double(n: int): int {
    2 * n
}
function method RangeSet(a: int, b: int): set<int> {
    set x: int | a <= x < b
}
lemma CardRangeSet(a: int, b: int)
    requires a <= b
    decreases b - a
    ensures |RangeSet(a, b)| == b - a
{
		if a != b {
        calc {
            |RangeSet(a, b)|;
            { assert RangeSet(a, b) == {a} + RangeSet(a + 1, b); }
            |{a} + RangeSet(a + 1, b)|;
            1 + |RangeSet(a + 1, b)|;
            { CardRangeSet(a + 1, b); }
            1 + (b - (a + 1));
            b - a;
        }
    }
}

function method MapSet<A,B>(f: A -> B, S: set<A>): set<B>
{
    set x | x in S :: f(x)
}
predicate Injective<A, B>(f: A -> B)
{
    forall x, y :: x != y ==> f(x) != f(y)
}
lemma CardMapSetInj<A, B>(f: A -> B, S: set<A>)
    requires Injective(f)
    decreases S
    ensures |MapSet(f, S)| == |S|
{
    if S != {} {
        var x :| x in S;
        calc {
            |MapSet(f, S)|;
            { assert MapSet(f, S) == MapSet(f, {x} + (S - {x})) == {f(x)} + MapSet(f, S - {x}); }
            |{f(x)} + MapSet(f, S - {x})|;
            1 + |MapSet(f, S - {x})|;
            { CardMapSetInj(f, S - {x}); }
            |S|;
        }
    }
}

method Main()
{
    var S := set s: int | 0 <= s < 50 :: Double(s);
    var T := set t | t in S && t < 25;
	assert S == MapSet(Double, RangeSet(0, 50));
	assert Double(1) in S;
	assert 2 in S;
	
    assert |S| == 50;                    // does not verify  
    assert T <= S;                       // does verify
	assert Double(13) in S;              //fixes the following
    assert T < S;                        // does not verify
}