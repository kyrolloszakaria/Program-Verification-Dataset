// https://stackoverflow.com/questions/74632153/defining-a-surjective-predicate-for-maps-and-functions/74661338#74661338
// Note: to be useful, the function's type should be --> (a broken arrow)
// indicating the function CAN have preconditions.
// Otherwise, -> is already a subset type of --> whose constraint is exactly your predicate
// so it would be a typing issue to provide a non-total function.
// See https://dafny.org/latest/DafnyRef/DafnyRef#sec-arrow-subset-types
predicate isTotal<G(!new), B(!new)>(f:G --> B)
//    reads f.reads   // You don't need this, because f is not declared as being able to read a function
{
    forall g:G :: f.requires(g)
}

// Passthrough identity function used for triggers
function Id<T>(t: T): T { t }

predicate Surjective<A(!new), B(!new)>(f: A -> B) 
{
    // If not using Id(b), the first forall does not have a trigger
    // and get hard to prove. Not impossible, but extremely lengthy
    forall b: B :: exists a: A :: f(a) == Id(b)
}

predicate isTotalMap<G(!new), B(!new)>(m:map<G,B>)
{
     forall g: G :: g in m
}

predicate mapSurjective<U(!new), V(!new)>(m: map<U,V>)
    requires forall u: U :: u in m.Keys
{
    // If not using Id(b), the first forall does not have a trigger
    // and get hard to prove. Not impossible, but extremely lengthy
    forall x: V :: exists a: U :: m[a] == Id(x)
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
function partialFunction(x: Color): Color
  requires x.Red? {
  x
}

lemma TestWrong() {
  // When trying to prove an assertion with a proof, use assert ... by like this:
  assert !isTotal(partialFunction) by {
    // If we were using ->, we would get "Value does not satisfies Color -> Color"*
    // But here we can just exhibit a counter-example that disproves the forall 
    assert !partialFunction.requires(Blue);

    // A longer proof could be done by contradiction like this:
    if(isTotal(partialFunction)) {
      assert forall c: Color :: partialFunction.requires(c);
      assert partialFunction.requires(Blue); // it can instantiate the forall above.
      assert false; // We get a contradiction
    }
    assert !isTotal(partialFunction);// A ==> false means !A
  }
}

lemma TestSurjective() {
    assert isTotal(toRed);
    assert isTotal(shiftColor);
    var toRedm := map[Red := Red, Blue := Red, Yellow := Red, Green := Red];
    var toShiftm := map[Red := Blue, Blue := Yellow, Yellow := Green, Green := Red];
    assert !Surjective(toRed) by {
      if(Surjective(toRed)) {
        var _ := Id(Blue);
      }
    }
    assert Surjective(shiftColor) by {
      if(!Surjective(shiftColor)) {
        var _ := Id(Blue); // We need to trigger the condition of surjective so that Dafny is happy with the below:
        assert !forall b: Color :: exists a: Color :: shiftColor(a) == Id(b);
        assert exists b: Color :: forall a: Color :: shiftColor(a) != Id(b);
        var b : Color :| forall a: Color :: shiftColor(a) != Id(b);
        assert shiftColor(shiftColor(shiftColor(shiftColor(b)))) == Id(b);
        assert false;
      }
    }
    assert forall c: Color :: c in toRedm by {
      if(!forall c :: c in toRedm) {
        assert exists c :: c !in toRedm;
        var c :| c !in toRedm;
        assert c != Red;// Dafny picks up from here
        assert false;
      }
    }
    assert !mapSurjective(toRedm) by {
      if(mapSurjective(toRedm)) {
        assert forall x :: exists a :: toRedm[a] == Id(x);
        var _ := Id(Blue); // Will instantiate the axiom above with x == Blue
        assert exists a :: toRedm[a] == Id(Blue); // Not needed, but Dafny can prove this.
        assert false;
      }
    }
    assert forall u: Color :: u in toShiftm.Keys by {
      if(!forall u: Color :: u in toShiftm.Keys) {
        assert exists u :: u !in toShiftm.Keys;
        var u :| u !in toShiftm.Keys;
        assert u != Red; // Dafny can pick up from here
        assert false;
      }
    }
    assert isTotalMap(toShiftm); //also fails
    assert forall u: Color :: u in toShiftm.Keys;
    assert mapSurjective(toShiftm) by {
      if(!mapSurjective(toShiftm)) {
        var _ := Id(Red); // Necessary so that Dafny understands that the next forall is equivalent
        assert !forall x :: exists a :: toShiftm[a] == Id(x);
        assert exists x :: forall a :: toShiftm[a] != Id(x);
        var x :| forall a :: toShiftm[a] != Id(x);
        assert forall b :: exists a :: toShiftm[a] == Id(b) by {
          forall b: Color ensures exists a :: toShiftm[a] == Id(b) {
            var a := toShiftm[toShiftm[toShiftm[b]]];
            assert toShiftm[toShiftm[toShiftm[toShiftm[b]]]] == Id(b);
          }
        }
        assert exists a :: toShiftm[a] == Id(x);
        var b :| toShiftm[b] == Id(x);
        assert false;
      }
    }
}