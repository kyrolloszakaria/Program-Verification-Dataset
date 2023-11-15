module Factorial {

  function Fib(n: nat): nat {
    if n < 2 then n else Fib(n - 2) + Fib(n - 1)
  } by method {
    var x, y := 0, 1;
    for i := 0 to n
      invariant x == Fib(i) && y == Fib(i + 1)
    {
      x, y := y, x + y;
    }
    return x;
  }

  function factorial(n: nat): int 
    requires n >= 0
    ensures factorial(n) > 0
  {
      if n <= 1 then 1 else n * factorial(n-1)
  } by method {
      var fact: nat := 1;
      var i: nat := 1;
      while i <= n 
        invariant 1 <= i <= n+1 
        invariant fact == factorial(i-1)
      {
          fact := fact * i;
          i := i + 1;
      }
      return fact;
  }

  function choose(n: nat, k: nat): nat 
    requires 0 <= k <= n  
  {
    factorial(n)/(factorial(k) * factorial(n-k))
  }




  lemma factorialDef(n: nat) 
    ensures n <= 1 ==> factorial(n) == 1
    ensures n > 1 ==> factorial(n) == n * factorial(n-1)
  {

  }

  lemma factorialDividesItself(n: nat)
    ensures factorial(n)/factorial(n) == 1
  {

  }

  lemma modMultiplication(aone: int, bone: int, atwo: int, btwo: int, n: int)
      requires n != 0
      requires aone % n == bone
      requires atwo % n == btwo
      ensures (aone * atwo) % n == (bone * btwo) % n 

  lemma remainderSubtract(x: int, a: int, c: int) 
      requires a != 0
      requires c == x % a
      ensures (x-c) % a == 0

  function divAdd(b: int, a: int, c: int): int {
      b * a + c
  }

  lemma remainderTheorem(x: int, a: int, c: int)
      requires a != 0
      requires x % a == c;
      ensures exists q  :: divAdd(q,a,c) == x
  {
    var q := (x-c) / a;
    remainderSubtract(x,a,c);
    assert divAdd(q,a,c) == x;
  }
  lemma selfDivision(a: int) 
      requires a != 0;
      ensures a % a == 0;
  {
  }
  lemma selfAnnihilation(a: int, b: int) 
      requires a != 0
      ensures (b*a) % a == 0
  {
      calc {
          (b * a) % a;
          {modMultiplication(a,0,b,b%a,a);}
          (0 * b%a) % a;
          0;
      }
  }

  function div(a: nat, y: nat, c: nat): nat
    requires c != 0
  {
    c * y + a % c
  }


  lemma divisionRemainderTheorem(x: nat,  a: nat, y: nat, c: nat) 
    requires c != 0
    requires y == a / c
    requires x == a % c
    ensures exists y: nat :: div(a,y,c) == a
  {
    if x == 0 {
      calc{
        div(a,y,c);
        ==
        c * (y) + a % c;
        ==
        c* y + 0;
        ==
        a;
      }
    }else{
      var b := c * y;
      assert b != a;
      calc{
        div(a,y,c);
        ==
        c * y + a % c;
        ==
        b + a % c;
        ==
        a;
      }
    }
  }

  lemma divCancel(a: nat, c: nat)  
    requires c != 0
    ensures (a*c)/c == a
  {
    selfAnnihilation(c, a);
    assert a * c % c == 0;
  }

  lemma divAssoc(a: nat, c: nat) 
    requires c != 0
    ensures (a * c) / c  == a*(c/c)
  {
    calc {
      (a * c) / c;
      == {divCancel(a,c);}
      a;
      ==
      a * 1;
      ==
      a * (c/c);
    }
  }

  lemma factorialFacts(n: nat) 
    requires n > 1
    ensures factorial(n)/factorial(n-1) == n
  {

    var blarg := factorial(n)/factorial(n-1);
    var none := factorial(n-1);
    calc {
      blarg;
      ==
      factorial(n)/factorial(n-1);
      ==
      factorial(n)/ none;
      == {factorialDef(n);}
      (n * factorial(n-1))/ none;
      ==
      (n * none) / none;
      == {divAssoc(n, none);}
      n * (none / none);
      ==
      n * 1;
      ==
      n;
    }
  }


  function ProductSet(s: set<nat>): nat {
    if s == {} then 1 else
      var x :| x in s;
      x * ProductSet(s-{x})
  }

  function ProductSeq(s: seq<nat>): nat {
    if s == [] then 1 else ProductSeq(s[0..|s|-1]) * s[|s|-1]
  }

  lemma ProductSeqDef(s: seq<nat>)
    ensures s != [] ==> ProductSeq(s) ==ProductSeq(s[0..|s|-1] ) * s[|s|-1] 
  {

  }

  function fset(n: nat, k: int): set<nat>
    requires k <= n
    ensures k >= 0 ==> n-k in fset(n,k)
  {
    if k < 0 then {} else {n-k} + fset(n,k-1)
  }

  function fseq(n: nat, k: int): seq<nat> 
    requires k <= n
    ensures k >= 0 ==> n-k in fseq(n,k)
    ensures k < 0 ==> [] == fseq(n,k)
  {
    if k < 0 then [] else [n-k] + fseq(n,k-1)
  }

  lemma fseqRetsEnd(n: nat, k: int) 
    requires 0 <= k <= n
    ensures fseq(n, k)[|fseq(n,k)|-1] == n
  {

  }

  lemma fseqRets(n: nat, k: int)
    requires 0 <= k <= n
    ensures forall x :: inRange(x, n-k, n) ==> x in fseq(n,k)
    ensures forall x :: !inRange(x, n-k, n) ==> x !in fseq(n,k)
    ensures |fseq(n,k)| == k+1
    ensures k > 0 ==> fseq(n,k) == [n-k]+fseq(n,k-1)
  {
  }


  predicate inRange(x: int, lower: int, upper: int) {
    lower <= x <= upper
  }

  lemma fsetRets(n: nat, k: int)
    requires 0 <= k <= n
    ensures forall x :: inRange(x, n-k, n) ==> x in fset(n,k)
    ensures forall x :: !inRange(x, n-k, n) ==> x !in fset(n,k)
  {
    // assert n-k in fset(n, k);
  }
  /*
  n = 9
  k = 4

  9-4 == 5
  9-3 == 6
  9-2 = 7
  9-1 ==8
  9-0 == 9
  */

  // lemma ProductSeqLemma(n: nat, k: nat)
  //     requires n >= 0
  //     requires 1 <= k < n
  //     ensures ProductSeq(fseq(n,k)) == ProductSeq(fseq(n,k-1))*(n-k);
  // {
  //     // var oldset := fseq(n,k-1);
  //     // fseqRets(n, k-1);

  //     // assert n-(k-1) in oldset;
  //     // assert !inRange(n-k, n-(k-1), n);
  //     // assert n-k !in oldset;
  //     // assert fseq(n,k) == [n-k]+oldset;
  //     // calc {
  //     //   ProductSeq(vq(n,k));
  //     //   ==
  //     //   (n-k) * ProductSeq(fseq(n,k-1));
  //     // }
  // }

  lemma fseqSucc(n: nat, k: int)
    requires n >= 1
    requires 0 < k <= n-1
    ensures fseq(n,k) == fseq(n-1,k-1) + [n]
  {
    // var left := fseq(n,k);
    // fseqRetsEnd(n,k);
    // assert left[|left|-1] == n;
    // var right := fseq(n-1,k-1);
    // fseqRetsEnd(n-1,k-1);
    // assert right[|right|-1] == n-1;
  }

  lemma fseqSubsets(n: nat) 
    requires n >= 1
    ensures fseq(n,n-1) == fseq((n-1),(n-1)-1) + [n]
  {
    if n == 1{
      assert fseq(1,0) == [1] == fseq(n, n-1);
      assert fseq(0,-2) == [] == fseq((n-1), (n-1)-1);
      assert fseq(n, n-1) == fseq((n-1), (n-1)-1) + [n];
    } else if n == 2 {
      assert fseq(2,1) == [1,2] == fseq(n, n-1);
      assert fseq(1,0) == [1] == fseq((n-1), (n-1)-1);
      assert fseq(n, n-1) == fseq((n-1), (n-1)-1)+[2];
    }else{
      // var right := fseq((n-1),(n-1)-1);
      fseqSucc(n,n-1);
      // fseqSubsets(n-1);
      // fseqRets(n-1, n-1-1);
      // var left := fseq(n,n-1);
      // assert left == [1]+fseq(n,n-2);
      // assert fseq(n-1, n-2) == fseq((n-1), (n-1)-1);
      // assert fseq(n,n-2) == fseq(n-1, n-2)+[n];
      // fseqRets(n, n-1);
      // assert right == fseq(n-2, n-3) + [n-1];
      // assert n !in right;
      // assert n in left;
      // assert 1 <= (n-1)-(n-2) <= n - (n-1) < n-1 < n;
      // forall x | 1 <= x <= n-1 
      //   ensures x in left && x in right
      // {
      //   assert x in left;
      //   assert x in right;
      // }
      // assert left == right+[n];
    }
  }

  lemma ProductSeqFseq(n: nat) 
    requires n >= 1
    ensures ProductSeq(fseq(n,n-1)) == ProductSeq(fseq(n-1,n-2))*n
  {
      var data := fseq(n,n-1);
      fseqSubsets(n);
      assert data == fseq((n-1),(n-1)-1)+[n];
      assert data != [];
      assert ProductSeq(data) == ProductSeq(fseq(n-1,n-2))*n;
  }

  lemma factorialSeq(n: nat)
    requires n >= 1
    ensures factorial(n) == ProductSeq(fseq(n,n-1))
  {
    if n == 1 {

    }else{
      ProductSeqFseq(n);
      // var data := fseq(n,n-1);
      // fseqSubsets(n);
      // assert data == fseq((n-1),(n-1)-1)+[n];
      // var res := ProductSeq(data);
      // assert res == n * ProductSeq(fseq(n-1, (n-1)-1)) ;
      // var fact := factorial(n);
      // assert fact == n * factorial(n-1);
      // fseqRets(n, n-1);
      // assert inRange(1,n-(n-1),n);
      // assert inRange(n,n-(n-1),n);
      // assert n in data;
      // assert 1 in data;
    }

  }

  // lemma fsetFact(n: nat, k: nat) 
  //   requires k <= n
  //   ensures fset(n,k) == {n-k+1} + fset(n,k-1)
  // {

  // }
  //5! = 5*4*3*2*1
  //3! = 3*2*1
  //5!/(5-2)! == 5*4
  //fseq(5,2-1)==[4,5] 
  //factorial(5) == fseq(5,4) == [1,2,3,4,5]
  //factorial(3) == fseq(3,2) == [1,2,3]
  //5!/(5-(2-1)) == 5!/(5-1)! == 5/4! = fseq(5,2-2) == [5]

  lemma ProductSeqSubseq(n: nat, k: nat) 
    requires n >= 0
    requires 0 <= k < n
    ensures ProductSeq(fseq(n,n-1)) == ProductSeq(fseq(n-k,(n-k)-1)) + ProductSeq(fseq(n,k-1));


  // lemma factorialDivison(n: nat, k: nat)
  //   requires n >= 0
  //   requires 0 <= k < n
  //   ensures factorial(n)/factorial(n-k) == ProductSeq(fseq(n, k-1))
  // {
  //   if k == 0 {
  //     assert fseq(n,k-1) == [];
  //     assert ProductSeq(fseq(n,k-1)) == 1;
  //     assert factorial(n)/factorial(n-k) == 1;
  //     // calc {
  //     //     factorial(n)/factorial(n-k);
  //     //     ==
  //     //     factorial(n)/factorial(n-1);
  //     //     == {factorialFacts(n);}
  //     //     n;
  //     //     ==
  //     //     ProductSet(fset(n,k-1));
  //     // }
  //   }else{
  //     var k' := k - 1;
  //     assert fseq(n,k) == [n-k] + fseq(n,k-1);
  //     assert fseq(n,k-1) == [n-k+1] + fseq(n,k-2);
  //     assert ProductSeq(fseq(n,k-1)) == ProductSeq(fseq(n,k-2))*(n-k+1);
  //     // factorialSeq(n);
  //     // assert factorial(n) == ProductSeq(fseq(n,n-1));
  //     // factorialSeq(n-k);
  //     // assert factorial(n-k) == ProductSeq(fseq(n-k,(n-k)-1));
  //     // // ProductSeqSubseq(n,k);
  //     // // assert ProductSeq(fseq(n,n-1)) == ProductSeq(fseq(n-k,(n-k)-1)) + ProductSeq(fseq(n,k-1));
  //     // // // assert ProductSet(fset(n,k)) == (n-k)*ProductSet(fset(n,k-1));

  //     // factorialDivison(n, k - 1);
  //     // assert factorial(n)/factorial(n-(k-1)) == ProductSeq(fseq(n,k-2));
      

  //   }
  // }

  method Test(n: nat, k: nat)
  requires n > 0 && 0 < k < n 
  {
    assert fset(n, 0) == {n};
    assert fset(n, 1) == {n, n-1};
    assert fset(n, 2) == {n, n-1, n-2};
  }
}