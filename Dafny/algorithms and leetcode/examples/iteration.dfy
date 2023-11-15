
// function method MapToSequence<A,B>(m: map<A,B>): seq<(A,B)> {
//   var keys := SetToSequence(m.Keys);
//   seq(|keys|, i requires 0 <= i < |keys| => (keys[i], m[keys[i]]))
// }

function method MapToSequence<A(!new),B>(m: map<A,B>, R: (A, A) -> bool): seq<(A,B)>
  requires IsTotalOrder(R)
{
  var keys := SetToSequence(m.Keys, (a,a') => R(a, a'));
  seq(|keys|, i requires 0 <= i < |keys| => (keys[i], m[keys[i]]))
}

// function method SetToSequence(s: set<int>): seq<int>
//   ensures var q := SetToSequence(s);
//     forall i :: 0 <= i < |q| ==> q[i] in s
// {
//   if s == {} then [] else
//     var x :| x in s && forall y :: y in s ==> x <= y;
//     [x] + SetToSequence(s - {x})
// }
function method SetToSequence<A(!new)>(s: set<A>, R: (A, A) -> bool): seq<A>
  requires IsTotalOrder(R)
  ensures var q := SetToSequence(s, R);
    forall i :: 0 <= i < |q| ==> q[i] in s
{
  if s == {} then [] else
    ThereIsAMinimum(s, 	R);
    var x :| x in s && forall y :: y in s ==> R(x, y);
    [x] + SetToSequence(s - {x}, R)
}

// lemma ThereIsAMinimum(s: set<int>)
//   requires s != {}
//   ensures exists x :: x in s && forall y :: y in s ==> x <= y
// {
//   var x :| x in s;
//   if s == {x} {
//     // obviously, x is the minimum
//   } else {
//     // The minimum in s might be x, or it might be the minimum
//     // in s - {x}. If we knew the minimum of the latter, then
//     // we could compare the two.
//     // Let's start by giving a name to the smaller set:
//     var s' := s - {x};
//     // So, s is the union of s' and {x}:
//     assert s == s' + {x};
//     // The following lemma call establishes that there is a
//     // minimum in s'.
//     ThereIsAMinimum(s');
//   }
// }

lemma ThereIsAMinimum<A(!new)>(s: set<A>, R: (A,A) -> bool) 
	requires s != {} && IsTotalOrder(R)
	ensures exists x :: x in s && forall y :: y in s ==> R(x, y)
{
	var x :| x in s;
	if s == {x} {  // error: postcondition might not hold on this return path
		assert forall y :: y in s ==> x == y;
  	} else {
		var s' := s - {x};
		assert s == s' + {x};
		ThereIsAMinimum(s', R);
	}
}

predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
  // connexity
  && (forall a, b :: R(a, b) || R(b, a))
  // antisymmetry
  && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
  // transitivity
  && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
}