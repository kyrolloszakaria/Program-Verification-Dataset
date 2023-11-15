

function Range<T, U>(f: T -> U, A: set<T>): set<U> {
    set x | x in A :: f(x)
}
ghost predicate Injective<A(!new), B>(f: A -> B)
{
    forall x, y :: x != y ==> f(x) != f(y)
}
ghost predicate isTotal<G(!new), B(!new)>(f:G -> B)
    reads f.reads
{
     forall g:G :: f.requires(g)
}

ghost predicate Surjective<A(!new), B(!new)>(f: A -> B) 
    reads f.reads
    // requires isTotal(f)
{
    forall b: B :: exists a: A :: f(a) == b 
}

lemma exercise1_5<T>(A: set<T>, B: set<T>)
    requires A + B == A
    ensures B <= A
{

}

ghost predicate Bijective<A(!new), B(!new)>(f: A -> B) 
{
    Injective(f) && Surjective(f)
}

lemma exercise1_6<T,U>(f: T  -> U, f_inv: U -> T, B: set<U>)
    requires forall u: U :: f(f_inv(u)) == u
    ensures Range(f, Range(f_inv, B)) <= B
{

}

lemma exercise1_6c<T,U>(f: T  -> U, f_inv: U -> T, A: set<T>)
    // requires forall u: U :: f(f_inv(u)) == u
    requires forall a: T :: a in A ==> f_inv(f(a)) == a
    ensures A <= Range(f_inv, Range(f, A))
{

}

lemma exercise1_7<X(!new), Y(!new)>(f: X -> Y, g: Y -> X)
    requires forall x: X :: g(f(x)) == x
    ensures Injective(f) && Surjective(g)
{
    if !Injective(f) {
        var x,y: X :| x != y && f(x) == f(y);
        assert g(f(x)) == g(f(y));
        assert false;
    } else if !Surjective(g) {
        // assert exists b: Y :: !(exists a: X :: f(a) == b);
        // assert !(forall b: X :: exists a: Y :: g(a) == b);
        // var b: X :| !(exists a: Y :: g(a) == b);
        var b: X :| forall a: Y :: g(a) != b;
        assert g(f(b)) != b;
        assert false;
    }
}

function sub(a: real, b: real): real {
    a - b
}

function add(a: real, b: real): real {
    a+b
}

function prod(a: real, b: real): real {
    a * b
}

ghost predicate upperBound(A: iset<real>, a: real) {
    forall x :: x in A ==> x <= a    
}

ghost predicate lowerBound(A: iset<real>, b: real) {
    forall x :: x in A ==> x >= b
}

ghost predicate leastUpperBound(A: iset<real>, a: real) 
{
    forall epsilon: real :: epsilon > 0.0 ==> !upperBound(A, sub(a, epsilon))  
}

ghost predicate greatestLeastBound(A: iset<real>, b: real) {
    forall epsilon: real :: epsilon > 0.0 ==> !lowerBound(A, add(b , epsilon))  
}

ghost predicate sup(A: iset<real>, a: real) {
    upperBound(A, a) && leastUpperBound(A, a)
}

ghost predicate inf(A: iset<real>, b: real) {
    lowerBound(A, b) && greatestLeastBound(A, b)
}

ghost predicate minimalElement(A: iset<real>, a: real) {
    a in A && lowerBound(A, a)
}

ghost predicate maximalElement(A: iset<real>, a: real) {
    a in A && upperBound(A, a)
}

lemma example1_25(A: iset<real>)
    requires A == iset x: real | x < 0.0
    ensures sup(A, 0.0)
{
    assert forall x: real :: x in A ==> x < 0.0;
    assert upperBound(A, 0.0);
    forall epsilon: real | epsilon > 0.0
        ensures !upperBound(A, sub(0.0,epsilon))
    {
        calc ==> {
            epsilon > 0.0;
            - epsilon > -2.0 * epsilon;
            (- epsilon)/2.0 > -epsilon;
        }
        assert (-epsilon)/2.0 in A;
        assert (-epsilon)/2.0 > sub(0.0,epsilon);
        // assert !upperBound(A, )
    }
    assert leastUpperBound(A, 0.0);
}

lemma CompletenessAxiomUpper(A: iset<real>, a: real)
    requires exists p: real :: p in A 
    requires upperBound(A, a)
    // ensures exists k: real :: leastUpperBound(A, k) && upperBound(A, k)
    ensures exists k: real :: sup(A, k)

lemma CompletenessAxiomLower(A: iset<real>, a: real)
    requires exists p: real :: p in A 
    requires lowerBound(A, a)
    // ensures exists k: real :: greatestLeastBound(A, k) && lowerBound(A, k)
    ensures exists k: real :: inf(A, k)

predicate greaterThan(n: nat, x: real) {
    n as real > x
}

predicate lessThan(n: nat, x: real) {
    n as real < x
}

predicate lessThanEqual(n: nat, x: real) {
    n as real <= x
}

lemma stillInt(x: real) 
    requires x.Floor as real == x
    ensures sub(x, 1.0).Floor as real == sub(x, 1.0)
{
    var m: int := x.Floor;
    assert (m-1) as real == sub(x, 1.0);
}

lemma stillIntPlus(x: real) 
    requires x.Floor as real == x
    ensures add(x, 1.0).Floor as real == add(x, 1.0)
{
    var m: int := x.Floor;
    assert (m+1) as real == add(x, 1.0);
}

lemma floorNaturals(nats: iset<real>)
    requires forall x :: x in nats ==> exists k: nat :: k as real == x
    ensures forall x :: x in nats ==> x.Floor as real == x
{

}

type pos = x: nat | 1 <= x witness 1
lemma ArchProof(x: real, a: real, b: real)
    requires a > 0.0
    requires x == b/a
    ensures exists n: pos :: n as real > x
{
    if x < 0.0 {
        assert 1 as real > x;
    }else{
        assert b >= 0.0;
        if forall n: pos :: n as real <= x {
            var naturals: iset<real> := iset ns: nat | lessThanEqual(ns, x) :: ns as real;
            // assert upperBound(naturals, x);
            if x <= 1.0 {
                assert 2 as real > x;
                assert false;
            }else{
                assert lessThanEqual(1, x);
                assert 1.0 in naturals;
            }
            CompletenessAxiomUpper(naturals, x);
            var alpha: real :| leastUpperBound(naturals, alpha as real) && upperBound(naturals, alpha as real); 
            var mp: nat := add(alpha , 1.0).Floor;
            assert lessThanEqual(mp, x);
            assert mp as real in naturals;
            assert upperBound(naturals, mp as real);

            assert false;
        }
    }
}
/*
Alt formulation of the branch
    // var kk: nat := x.Floor + 1;
    // calc ==> {
    //     kk as real > x;
    //     (kk ) as real > b/a;
    //     {what(kk, a, b);}
    //     kk as real * a > b;
    // }
    // assert (kk ) as real > x;
    // assert (kk ) as real > b/a;
    // assert prod(kk  as real, a) > b;
*/

/**
extra bits
    // assert n >= 1;
    // assert 1 as real < x;
    // assume alpha in naturals;
    // assert alpha < x;
    // assert alpha.Floor as real == alpha ;
    // assert 1.0 > 0.0;
    // assert alpha in naturals;
    // var m := sub(alpha, 1.0);
    // assert m < x;
    // assert mp as real > alpha;
    // assert mp as real <= x;
    // assert m.Floor as real == m;
    // assert m in naturals;
    // assert !upperBound(naturals, m);
    // assert lessThanEqual(m.Floor, x);
    // assert lessThan(m.Floor+1, x);
    // assert m as real in naturals;
    // assert (m + 1) as real > alpha ;
    // assert m as real == sub(alpha, 1.0);
    assert upperBound(naturals, alpha as real);
    assert leastUpperBound(naturals, alpha as real);
    assert forall epsilon: real :: epsilon > 0.0 ==> !upperBound(naturals, sub(alpha as real, epsilon));
 */

lemma ArchimedeanPrinciple(epsilon: real)
    requires epsilon > 0.0
    ensures exists n: pos :: 1.0 / (n as real) < epsilon
{
    ArchProof(1.0 / epsilon, epsilon, 1.0);
    var n: pos :| n as real > 1.0 / epsilon;
    calc ==> {
        n as real > 1.0 / epsilon;
        {assert (n as real) *  epsilon > (1.0/epsilon)*epsilon;}
        (n as real) * epsilon > 1.0;
        epsilon > 1.0 / (n as real);
    }
}

lemma exercise1_23(A: iset<real>, B: iset<real>, abound: real, bbound: real, epsilon: real)
    requires A <= B
    requires sup(A, abound)
    requires sup(B, bbound)
    requires epsilon > 0.0
    ensures abound <= bbound
{
  if abound > bbound {
    var myepsilon := abound - bbound;
    assert bbound == sub(abound, myepsilon);
    assert upperBound(A, bbound);
    assert upperBound(A, sub(abound, myepsilon));
    assert  false;
  }
}

/*
    // var apoint := sub(abound, epsilon);
    // var bpoint := sub(bbound, epsilon);
    // assert !upperBound(A, apoint);
    // assert !upperBound(A, bpoint);
    // assert !upperBound(B, apoint);
    // assert !upperBound(B, bpoint);
    // assert apoint > bpoint;
    // var k: real :| k in A && k > apoint && k < abound;
    // assert upperBound(B, abound);
    // assert k in B;
*/

function e29(n: nat): real {
    (n as real)/(n as real + 1.0)
}

lemma exercise1_29a(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures sup(A, 1.0)
{
    assert upperBound(A, 1.0);
    forall epsilon: real | epsilon > 0.0 
        ensures !upperBound(A, sub(1.0, epsilon))
    {
        ArchimedeanPrinciple(epsilon);
        var n: pos :| 1.0 / (n as real) < epsilon; 
        assert (1.0 / (n as real + 1.0)) < 1.0 / (n as real);
        assert e29(n) in A;
        assert sub(1.0, 1.0 / (n as real + 1.0)) == e29(n); 
        // assert exists k :: k in A && k > sub(1.0, epsilon);
    }
}

lemma exercise1_29b(A: iset<real>)
    requires A == iset n: pos :: e29(n)
    ensures inf(A, 1.0/2.0)
{
    assert e29(1) in A;
    forall x | x in A 
        ensures x >= 1.0/2.0
    {
        var n: nat :| x == e29(n);
        if n == 1 {

        }
    }
    assert lowerBound(A, 1.0/2.0);
    assert greatestLeastBound(A, 1.0/2.0);
}

lemma exercise1_30(A: iset<real>, B: iset<real>, abound: real, bbound: real)
    requires sup(A, abound)
    requires sup(B, bbound)
    requires abound < bbound
    ensures exists b: real :: b in B && upperBound(A, b)
{
    // assert upperBound(A, bbound);
    // assert leastUpperBound(B, bbound);
    // assert forall epsilon: real :: epsilon > 0.0 ==> !upperBound(B, sub(bbound, epsilon));
    var epsilon := sub(bbound, abound);
    // assert abound + epsilon == bbound;
    // assert epsilon > 0.0;
    assert !upperBound(B, sub(bbound, epsilon));
}

function abs(a: real): real {
    if a >= 0.0 then a else -a
}

predicate positiveNat(x: nat) {
    x > 0
}

predicate positiveReal(x: real) {
    x > 0.0
}

ghost predicate Limit(a_i: pos -> real, a: real) {
    forall epsilon: real :: positiveReal(epsilon) ==> exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon, a)
}

function oneOverN(n: pos): real {
    1.0 / n as real
}

predicate converges(a_i: pos -> real, n: pos, epsilon: real, a: real) {
    abs(a_i(n)-a) < epsilon
}

predicate CauchyCriterion(a_i: pos -> real, epsilon: real, m: pos, n: pos) {
    abs(a_i(m)-a_i(n)) < epsilon
}

ghost predicate isCauchy(a_i: pos -> real) {
    forall epsilon: real :: positiveReal(epsilon) ==> exists N: nat :: positiveNat(N) && forall n: pos,m:pos :: m > n > N ==> CauchyCriterion(a_i, epsilon, m, n)
}

lemma helper(x: real, y: real, z: real)
    requires x >0.0 && y > 0.0 && z> 0.0
    requires x * y > z * y
    ensures x > z
{

}

lemma helper2(x: real, y: real, z: real)
    requires x >0.0 && y > 0.0 && z> 0.0
    requires x > z
    ensures x * y > z * y
{

}

lemma biggerDenominator(bigger: nat, smaller: nat)
    requires 0 < smaller < bigger
    ensures (1.0 / smaller as real) > (1.0 / bigger as real)
{
    var delta: pos := bigger - smaller;
    helper((1.0 / smaller as real), ((smaller+delta) as real), (1.0 / (smaller + delta) as real));
}

lemma biggerDenominatorReal(bigger: real, smaller: real)
    requires 0.0 < smaller < bigger
    ensures (1.0 / smaller) > (1.0 / bigger)
{

    var delta := bigger - smaller;
    helper((1.0 / smaller as real), ((smaller+delta) as real), (1.0 / (smaller + delta) as real));
}
// calc {
//     (1.0 / smaller as real)*((smaller+delta) as real) > (1.0 / (smaller + delta) as real) * ((smaller+delta) as real);
//     {helper((1.0 / smaller as real), ((smaller+delta) as real), (1.0 / (smaller + delta) as real));}
//     (1.0 / smaller as real) > 1.0 / (smaller + delta) as real;

// }
// ((smaller+delta) as real/smaller as real) > 1.0 as real;
// ((smaller+delta) as real/smaller as real) > (1.0 / (smaller + delta) as real) *((smaller+delta) as real);
// assert a - delta == bigger;
// assert a == bigger + delta;
// calc {
//     1.0 / a as real;
//     1.0 / (bigger + delta) as real;
// }

lemma helper3(a: real, b: real)
    requires 0.0 < a < b 
    ensures 1.0 / a > 1.0 / b
{
    var delta: real := b - a;
}

lemma oneOverNLessThanEpsilon(epsilon: real, N: nat) 
    requires epsilon > 0.0
    requires N == (1.0 / epsilon).Floor + 1
    ensures 1.0 / N as real < epsilon
{
    if epsilon > 1.0 {

    }else if epsilon == 1.0 {
        
    }else if epsilon < 1.0 {
        helper3(1.0/epsilon, N as real);
        // assert 1.0 / N as real < 1.0/(1.0/epsilon);
        assert 1.0/(1.0/epsilon) == epsilon;
        // assert 1.0 / N as real < epsilon;
    }
}



lemma {:verify } exercise3_9() 
    ensures Limit(oneOverN, 0.0)
{
    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(oneOverN, n, epsilon, 0.0)
    {
        var N: nat := (1.0 / epsilon).Floor + 1;
        assert positiveNat(N);
        forall n: pos | n > N
            ensures converges(oneOverN, n, epsilon, 0.0)
        {
            biggerDenominator(n,N);
            oneOverNLessThanEpsilon(epsilon, N);
            assert 1.0 / N as real < epsilon;
            assert abs(oneOverN(n)-0.0) < epsilon; //figured out that 1.0/n < 1.0/ N < epsilon
            //figured out that f(n) < f(N) < epsilon
        }
    }
}


lemma multiplyByXoverX(a: real, b: real, x: real)
    requires x != 0.0 && b != 0.0
    ensures a/b == prod(a,x)/prod(b,x)
{

}

lemma subtractLikeBase(denominator: real, x: real, y: real)
    requires denominator != 0.0
    ensures x/denominator-y/denominator == (x-y)/denominator
{

}


function TwoNminusTwoOverFiveNPlusOne(n: pos): real {
    (2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)
}

lemma TwoNminusTwoOverFiveNPlusOneN(n: pos, N: pos, epsilon: real)
    requires epsilon > 0.0
    requires n > N
    requires N == ((12.0/epsilon-5.0)/25.0).Floor+1
    ensures 12.0/(25.0*(n as real)+5.0) < 12.0/(25.0*(N as real)+5.0)
{}

lemma {:verify } exercise3_4b() 
    ensures Limit(TwoNminusTwoOverFiveNPlusOne, 2.0/5.0);
{

    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0)
    {

/*
        12.0/(25.0*(n as real)+5.0) < 12.0/(25.0*(N as real)+5.0) = epsilon;
        12.0/(25.0*(N as real)+5.0) = epsilon;
        12.0/epsilon-5.0 = 25.0*(N as real)
        (12.0/epsilon-5.0)/25.0 = (N as real)
*/
        if epsilon >= 1.0 {
            assert positiveNat(1);
            forall n: nat | n >1 
                ensures  12.0/(25.0*(n as real)+5.0) < epsilon
            {
calc {
                    abs(TwoNminusTwoOverFiveNPlusOne(n)-(2.0/5.0)) ;
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0/5.0)) ;
                    // {multiplyByXoverX(2.0, 5.0, (5.0*(n as real)+1.0));}
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-prod(2.0,(5.0*(n as real)+1.0))/prod(5.0,(5.0*(n as real)+1.0))) ;
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    {multiplyByXoverX(2.0*(n as real)-2.0, 5.0*(n as real)+1.0, 5.0);}
                    abs((5.0*(2.0*(n as real)-2.0))/(5.0*(5.0*(n as real)+1.0))-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    abs((10.0*(n as real)-10.0)/(5.0*(5.0*(n as real)+1.0))-((10.0*(n as real)+2.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    abs((10.0*(n as real)-10.0)/(25.0*(n as real)+5.0)-(10.0*(n as real)+2.0)/(25.0*(n as real)+5.0)) ;
                    {subtractLikeBase(25.0*(n as real)+5.0, 10.0*(n as real)-10.0, 10.0*(n as real)+2.0);}
                    abs((10.0*(n as real)-10.0-(10.0*(n as real)+2.0))/(25.0*(n as real)+5.0)) ;
                    abs((10.0*(n as real)-10.0-10.0*(n as real)-2.0)/(25.0*(n as real)+5.0)) ;
                    abs((10.0*(n as real)-10.0*(n as real)-12.0)/(25.0*(n as real)+5.0)) ;
                    abs(-12.0/(25.0*(n as real)+5.0)) ;
                    {assert forall n : pos :: -12.0/(25.0*(n as real)+5.0) < 0.0;}
                    -(-12.0/(25.0*(n as real)+5.0)) ;
                    {assert forall x: real :: --x == x; assert -(-12.0/(25.0*(n as real)+5.0)) == 12.0/(25.0*(n as real)+5.0);}
                    12.0/(25.0*(n as real)+5.0) ;
                }
                assert converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0);
            }
        }else{
            var N: nat := ((12.0/epsilon-5.0)/25.0).Floor+1;
            assert positiveNat(N);

            forall n: pos | n > N
                ensures converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0)
            {
                calc {
                    abs(TwoNminusTwoOverFiveNPlusOne(n)-(2.0/5.0)) ;
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0/5.0)) ;
                    // {multiplyByXoverX(2.0, 5.0, (5.0*(n as real)+1.0));}
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-prod(2.0,(5.0*(n as real)+1.0))/prod(5.0,(5.0*(n as real)+1.0))) ;
                    abs((2.0*(n as real)-2.0)/(5.0*(n as real)+1.0)-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    {multiplyByXoverX(2.0*(n as real)-2.0, 5.0*(n as real)+1.0, 5.0);}
                    abs((5.0*(2.0*(n as real)-2.0))/(5.0*(5.0*(n as real)+1.0))-(2.0*(5.0*(n as real)+1.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    abs((10.0*(n as real)-10.0)/(5.0*(5.0*(n as real)+1.0))-((10.0*(n as real)+2.0))/(5.0*(5.0*(n as real)+1.0))) ;
                    abs((10.0*(n as real)-10.0)/(25.0*(n as real)+5.0)-(10.0*(n as real)+2.0)/(25.0*(n as real)+5.0)) ;
                    {subtractLikeBase(25.0*(n as real)+5.0, 10.0*(n as real)-10.0, 10.0*(n as real)+2.0);}
                    abs((10.0*(n as real)-10.0-(10.0*(n as real)+2.0))/(25.0*(n as real)+5.0)) ;
                    abs((10.0*(n as real)-10.0-10.0*(n as real)-2.0)/(25.0*(n as real)+5.0)) ;
                    abs((10.0*(n as real)-10.0*(n as real)-12.0)/(25.0*(n as real)+5.0)) ;
                    abs(-12.0/(25.0*(n as real)+5.0)) ;
                    {assert forall n : pos :: -12.0/(25.0*(n as real)+5.0) < 0.0;}
                    -(-12.0/(25.0*(n as real)+5.0)) ;
                    12.0/(25.0*(n as real)+5.0) ;
                }

                TwoNminusTwoOverFiveNPlusOneN(n, N, epsilon);
                assert 12.0/(25.0*(N as real)+5.0) < epsilon by {
                    var niceN := ((12.0/epsilon-5.0)/25.0);
                    var result := 12.0/(25.0*(N as real)+5.0);
                    assert (((12.0/epsilon-5.0)/25.0).Floor+1 ) as real > niceN;
                    assert N == (((12.0/epsilon-5.0)/25.0).Floor+1 );
                    calc {
                        12.0/(25.0*(((12.0/epsilon-5.0)/25.0))+5.0);
                        12.0/(25.0*((12.0/epsilon-5.0)/25.0)+5.0);
                        12.0/(12.0/epsilon-5.0+5.0);
                        12.0/(12.0/epsilon);
                        epsilon;

                    }
                    
                    assert  (25.0*(N as real)+5.0) > (25.0*niceN+5.0);
                    biggerDenominatorReal((25.0*(N as real)+5.0), 25.0*niceN+5.0);
                    assert 1.0/(25.0*(N as real)+5.0) < 1.0/(25.0*(niceN)+5.0);
                    assert (1.0/(25.0*(N as real)+5.0) )*12.0 == result;
                    assert (1.0/(25.0*(N as real)+5.0) )*12.0 < 1.0/(25.0*(niceN)+5.0)* 12.0;
                    assert 12.0/(25.0*(((12.0/epsilon-5.0)/25.0))+5.0) == 1.0/(25.0*(niceN)+5.0)* 12.0;
                    assert result < 1.0/(25.0*(niceN)+5.0)* 12.0;
                }
                assert converges(TwoNminusTwoOverFiveNPlusOne, n, epsilon, 2.0/5.0);
            }
        }
    }
}

ghost function setOfNegatives(a_i: pos -> real): iset<real> {
    iset n | a_i(n) < 0.0 :: a_i(n)
}

lemma exercise3_1(a_i: pos -> real)
    requires Limit(a_i, 0.001)
    // ensures exists n: nat :: |setOfNegatives(a_i)| <= n
{
    if forall n: pos :: true ==> a_i(n) >= 0.0 {
        // assume !Limit(a_i, 0.001);
    }
    // if !Limit(a_i, 0.001) {

        // assert !(forall epsilon: real :: positiveReal(epsilon) ==> exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon, 0.001));
        // assert exists epsilon: real :: positiveReal(epsilon) && forall N: nat :: positiveNat(N) ==> exists n: pos :: n > N &&  !(converges(a_i, n, epsilon, 0.001));
    //     assume forall n: pos :: true ==> a_i(n) >= 0.0;
    // }
}

lemma exercise3_1b(a_i: pos -> real, N: nat)
    requires Limit(a_i, 0.001)
    requires positiveNat(N) && forall n :: n > N ==> converges(a_i, n, 0.001, 0.001)
    ensures forall n:: n > N ==> a_i(n) >= 0.0
{
    forall n | n > N 
        ensures a_i(n) >= 0.0
    {
        assert converges(a_i, n, 0.001, 0.001);
    }

}

method exercise3_1m(a_i: pos -> real) returns (ghost negatives: set<nat>)
    requires Limit(a_i, 0.001)
    ensures forall x :: x in negatives ==> a_i(x) < 0.0
    ensures exists N: nat :: positiveNat(N) && |negatives| <= N
{
    var epsilon: real := 0.001;
    assert positiveReal(epsilon);
    ghost var N: nat :| positiveNat(N) && forall n :: n > N ==> converges(a_i, n, epsilon, 0.001);
    ghost var i: nat := 1;
    negatives := {};
    while i < N
        invariant 0 <= i <= N
        invariant forall x :: x in negatives ==> a_i(x) < 0.0
        invariant |negatives| <= i
    {
        if a_i(i) < 0.0 {
            negatives := {i} + negatives;
        }
        i := i + 1;
    }
    assert i <= N;
    assert |negatives| <= N;

}

function addSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
    (n:pos) => a_i(n) + b_i(n)
}

function prodSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
    (n:pos) => prod(a_i(n) , b_i(n))
}

function subSequence(a_i: pos -> real, b_i: pos -> real): pos -> real {
    (n:pos) => a_i(n) - b_i(n)
}

function mulSequence(a_i: pos -> real, c: real): pos -> real {
    (n:pos) => prod(c, a_i(n))
}

lemma TriangeInequality(a: real, b: real)
    ensures abs(a+b) <= abs(a) + abs(b)
{
}

function maxNat(a: nat, b: nat): nat {
    if a >= b then a else b
}

function maxReal(a: real, b: real): real {
    if a >= b then a else b
}

lemma exercise3_8(a_i: pos -> real, b_i: pos -> real, a: real, b: real)
    requires Limit(a_i, a)
    requires Limit(b_i, b)
    ensures Limit(addSequence(a_i, b_i), a+b)
{

    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(addSequence(a_i, b_i), n, epsilon, a+b)
    {
        var epsilonOver2 := epsilon / 2.0;
        assert positiveReal(epsilonOver2);
        var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilonOver2, a);
        var M: nat :|  positiveNat(M) && forall n: pos :: n > M ==> converges(b_i, n, epsilonOver2, b);
        var Q := maxNat(N,M);
        assert positiveNat(Q);
        assert forall n: pos :: n > Q ==> converges(a_i, n, epsilonOver2, a);
        assert forall n: pos :: n > Q ==> converges(b_i, n, epsilonOver2, b);
        forall n: pos | n > Q 
            ensures converges(addSequence(a_i, b_i), n, epsilon, a+b)
        {
            calc {
                abs(addSequence(a_i, b_i)(n)-(a+b));
                abs(a_i(n) + b_i(n)-(a+b));
                abs(a_i(n) + b_i(n)-a-b);
                abs(a_i(n) -a + b_i(n)-b);
            }
            assert converges(a_i, n, epsilonOver2, a);
            assert converges(b_i, n, epsilonOver2, b);
            assert abs(a_i(n) -a) < epsilonOver2;
            assert abs(b_i(n)-b) < epsilonOver2;
            assert abs(a_i(n) -a + b_i(n)-b) <= abs(a_i(n) -a) + abs(b_i(n)-b);
        }
    }
}

lemma inequalitProduct(a: real, b: real, c: real)
    requires a < b
    requires c > 0.0
    ensures c*a < c*b
{

}

lemma inequalitProductNeg(a: real, b: real, c: real)
    requires a < b
    requires c < 0.0
    ensures c*a > c*b
{

}

lemma absThings(a: real, c: real)
    requires c > 0.0
    ensures c * abs(a) == abs(c*a)
{
}

lemma exercise3_8b(a_i: pos -> real, a: real, c: real)
    requires Limit(a_i, a)
    ensures Limit(mulSequence(a_i, c), prod(c, a))
{
    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
    {
        if c > 0.0 {
            var epsilonOverC := epsilon/c;
            assert positiveReal(epsilonOverC);
            var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon/c, a);
            forall n: pos | n > N 
                ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
            {
                assert converges(a_i, n, epsilonOverC, a);
                // calc {
                //     abs(mulSequence(a_i, c)(n)-prod(c,a));
                //     abs(prod(c,a_i(n))-prod(c,a));
                //     abs(c*a_i(n)-c*a);
                //     abs(c*(a_i(n)-a));
                // }
                var dist := abs(a_i(n)-a);
                assert 0.0 <= dist < epsilonOverC;
                inequalitProduct(dist, epsilonOverC, c);
                assert c*0.0 <= c * dist < c * epsilonOverC;
                assert c * epsilon/c == epsilon;
                assert epsilonOverC == epsilon/c;
                // assert c * epsilonOverC == epsilon;
                // assert c*0.0 <= c * dist < epsilon;
                // assert 0.0 < c*epsilon;
                // assert c * abs(a_i(n)-a) < c*epsilon;
                var diff := a_i(n)-a;
                // absThings(diff,c);
                // assert c *dist == abs(c*diff);
                // assert c * abs(diff) == abs(c*diff); 
                // assert abs(c*diff) == abs(c*(a_i(n)-a));
                // assert abs(c*(a_i(n)-a)) < epsilon; 
                // assert abs(mulSequence(a_i, c)(n)-prod(c,a)) == abs(c*(a_i(n)-a));
                assert abs(mulSequence(a_i, c)(n)-prod(c,a)) < epsilon;
                assert converges(mulSequence(a_i, c), n, epsilon, prod(c, a));
            }
        }else if c == 0.0 {
            var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilon, a);
            forall n: pos | n > N 
                ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
            {
            }
        }else {
            var epsilonOverC := -epsilon/c;
            assert positiveReal(epsilonOverC);
            var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(a_i, n, epsilonOverC, a);
            forall n: pos | n > N 
                ensures converges(mulSequence(a_i, c), n, epsilon, prod(c, a))
            {

                assert converges(a_i, n, epsilonOverC, a);
                // calc {
                //     abs(mulSequence(a_i, c)(n)-prod(c,a));
                //     abs(prod(c,a_i(n))-prod(c,a));
                //     abs(c*a_i(n)-c*a);
                //     abs(c*(a_i(n)-a));
                // }
                var dist := abs(a_i(n)-a);
                assert 0.0 <= dist < epsilonOverC;
                // inequalitProduct(dist, epsilonOverC, c);
                assert c*0.0 <= -c * dist < -c * epsilonOverC;
                // assert c * epsilon/c == epsilon;
                // assert epsilonOverC == -epsilon/c;
                assert -c * epsilonOverC == epsilon;
                assert -c*0.0 <= -c * dist < epsilon;
                // assert 0.0 < -c*epsilon;
                // assert c * abs(a_i(n)-a) < c*epsilon;
                var diff := a_i(n)-a;
                // absThings(diff,-c);
                // assert -c *dist == abs(c*diff);
                // assert -c * abs(diff) == abs(c*diff); 
                assert abs(c*diff) == abs(-c*(a_i(n)-a));
                // assert abs(c*(a_i(n)-a)) < epsilon; 
                assert abs(mulSequence(a_i, c)(n)-prod(c,a)) == abs(c*(a_i(n)-a));
                // assert abs(mulSequence(a_i, c)(n)-prod(c,a)) < epsilon;
                // assert converges(mulSequence(a_i, c), n, epsilon, prod(c, a));
            }
        }
    }
}

lemma {:verify false} exercise3_13(a_i: pos -> real, b_i: pos -> real, a: real, b: real)
    requires Limit(a_i, a)
    requires Limit(b_i, b)
    ensures Limit(subSequence(a_i, b_i), a-b)
{
    // exercise3_8(a_i, b_i, a, b);
}

ghost predicate bounded(ss: iset<real>, L: real, U: real) {
    forall x :: x in ss ==> L <= x <= U
}

ghost predicate boundedSeq(a_i: pos -> real, L: real, U: real) {
    forall n:pos :: positiveNat(n) ==> L <= a_i(n) <= U
}

lemma boundedEqual(a_i: pos -> real, a_range: iset<real>, L: real, U: real)
    requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
    requires bounded(a_range, L, U)
    ensures boundedSeq(a_i, L, U)
{
    forall n:pos | positiveNat(n)
        ensures L <= a_i(n) <= U
    {
        assert a_i(n) in a_range;
    }

}

lemma boundedEqualLeft(a_i: pos -> real, a_range: iset<real>, L: real, U: real)
    requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
    requires boundedSeq(a_i, L, U)
    ensures bounded(a_range, L, U)
{
}

lemma absProd(a: real, b: real)
    ensures abs(prod(a,b)) == prod(abs(a), abs(b))
{

}

lemma prodLessThan(a: real, b: real, c: real)
    requires a > 0.0
    requires 0.0 <= b < c 
    ensures prod(a , b) < prod(a , c)
{
    
}

function div(a: real, b: real): real 
    requires b != 0.0
{
    a / b
}

lemma divSmaller(a: real, b: real)
    requires a >= 0.0
    requires b > a
    ensures div(a,b) < 1.0
{
    var diff := b-a;
    assert a/(a+diff) < 1.0;
}

lemma divCommute(a: real, b: real, c: real)
    requires c != 0.0
    // ensures a * (b/c) == (a/c)*b
    ensures prod(a , div(b,c)) == prod(div(a,c),b)
{
}

lemma smallerX(a: real, b : real)
    requires a > 0.0
    requires 0.0 <= b < 1.0
    ensures b*a < a 
{

}

lemma exercise3_18a(a_i: pos -> real, b_i: pos -> real, a_range: iset<real>, al: real, au: real)
    requires Limit(b_i, 0.0)
    requires a_range == iset n: pos | positiveNat(n) :: a_i(n)
    requires al <= au
    requires bounded(a_range, al, au) && boundedSeq(a_i, al, au)
    ensures Limit(prodSequence(a_i, b_i), 0.0)
{
    assert al <= au;
    forall epsilon: real | positiveReal(epsilon)
        ensures exists N: nat :: positiveNat(N) && forall n: pos :: n > N ==> converges(prodSequence(a_i, b_i), n, epsilon, 0.0)
    {
        var max := maxReal(abs(al), abs(au))+1.0;
        var epsilonOverMax := div(epsilon , max);
        assert positiveReal(epsilonOverMax);
        var N: nat :|  positiveNat(N) && forall n: pos :: n > N ==> converges(b_i, n, epsilonOverMax, 0.0);
        forall n: pos | n > N 
            ensures converges(prodSequence(a_i, b_i), n, epsilon,  0.0)
        {
            assert converges(b_i, n, epsilonOverMax, 0.0);
            assert abs(b_i(n)-0.0) < epsilonOverMax;
            assert abs(b_i(n)) < epsilonOverMax;
            calc {
            abs(prodSequence(a_i, b_i)(n)-0.0); 
            abs(prodSequence(a_i, b_i)(n)); 
            abs(prod(a_i(n), b_i(n))); 
            }
            absProd(a_i(n), b_i(n));
            // assert prod(abs(a_i(n)) , abs(b_i(n))) == abs(prod(a_i(n), b_i(n)));
            // assert abs(b_i(n)) < epsilonOverMax;
            assert prod(abs(a_i(n)) , epsilonOverMax) < epsilon by {
                assert al <= a_i(n) <= au;
                var an := abs(a_i(n));
                assert an >= 0.0;
                var bx:=div(an,max); 
                assert bx >= 0.0;
                calc {
                    prod(abs(a_i(n)),  div(epsilon , max));
                    prod(an,  div(epsilon , max));
                    {divCommute(an, epsilon, max);}
                    prod(div(an , max) , epsilon);
                    prod(bx , epsilon);
                    (bx) * epsilon;
                }
                if abs(al) >= abs(au) {
                    // assert abs(a_i(n)) <= abs(al) < max;
                    divSmaller(abs(a_i(n)), max);
                    assert abs(a_i(n))/max < 1.0;
                    smallerX(epsilon, bx);
                    // assert (bx) * epsilon < epsilon;
                    // assert (abs(a_i(n)) / max) * epsilon < epsilon;
                    // assert bx == abs(a_i(n)) / max;
                    // assert (bx) * epsilon == prod(abs(a_i(n)) , div(epsilon , max));
                    assert prod(abs(a_i(n)) , div(epsilon , max)) < epsilon;
                }else{
                    assert abs(a_i(n)) <= abs(au) < max;
                    divSmaller(abs(a_i(n)), max);
                    assert abs(a_i(n))/max < 1.0;
                    // assert 0.0 <= bx < 1.0;
                    smallerX(epsilon, bx);
                    // assert (bx) * epsilon < epsilon;
                    // assert (bx) * epsilon == prod(abs(a_i(n)) , div(epsilon , max));
                    assert prod(abs(a_i(n)) , div(epsilon , max)) < epsilon;
                }
            }
            // assert abs(prodSequence(a_i, b_i)(n)-0.0) ==abs(prod(a_i(n), b_i(n)));  
            if abs(a_i(n)) == 0.0 {
                // assert prod(abs(a_i(n)),abs(b_i(n)))  < epsilon;
                // assert abs(prod(a_i(n), b_i(n))) < epsilon; 
                // assert abs(prodSequence(a_i, b_i)(n)-0.0) < epsilon;
                assert converges(prodSequence(a_i, b_i), n, epsilon, 0.0);
            }else if abs(a_i(n)) > 0.0 {
                // assert abs(a_i(n)) > 0.0;
                prodLessThan(abs(a_i(n)), abs(b_i(n)), epsilonOverMax);
                assert prod(abs(a_i(n)),abs(b_i(n))) < prod(abs(a_i(n)),epsilonOverMax) < epsilon;
                // assert abs(prod(a_i(n), b_i(n))) < epsilon; 
                // assert abs(prodSequence(a_i, b_i)(n)-0.0) < epsilon;
                assert converges(prodSequence(a_i, b_i), n, epsilon, 0.0);
            }
        }

    }
}
// calc ==> {
//     n > N;
//     n / n > N/n;
//     1.0 > N as real / n as real;
//     {assert (N as real / n as real) / N as real == 1.0 / n as real;}
//     {biggerDenominator(n,N);}
//    ( (1.0) / N as real) > 1.0 / n as real;
// }
// assert (1.0 / n as real) < (1.0 / N as real);
// calc ==> {
//     abs(oneOverN(n)-0.0) < epsilon;
//     abs(oneOverN(n)) < epsilon;
//     oneOverN(n) < epsilon;
// }
// assert oneOverN(n) < epsilon;
// calc{
//     abs(oneOverN(n)-0.0);
//     abs(oneOverN(n));
//     oneOverN(n);
//     1.0/n as real;
// }
// calc {
//     1.0 / N as real;
//     1.0 / ((1.0 / epsilon).Floor + 1) as real;
// }
// calc{ 
//     ((1.0 / epsilon).Floor + 1) as real* 1.0 / ((1.0 / epsilon).Floor + 1) as real;
//     1.0;
// }
// calc ==> {
//     1.0 / N as real < epsilon;
//     1.0 / ((1.0 / epsilon).Floor + 1) as real < epsilon;
//     {helper2(epsilon, ((1.0 / epsilon).Floor + 1) as real, 1.0 /((1.0 / epsilon).Floor + 1) as real);}
//     ((1.0 / epsilon).Floor + 1) as real* 1.0 / ((1.0 / epsilon).Floor + 1) as real < ((1.0 / epsilon).Floor + 1) as real * epsilon;
//     1.0 < ((1.0 / epsilon).Floor + 1) as real * epsilon;
// }