
/*
https://leetcode.com/problems/number-of-1-bits/
function hammingWeight(n: number): number {
    let count = 0;
    for(let i = 0; i < 32; i++) {
        count += n & 1;
        n = n >> 1;
    }
    return count;
};
*/
function method twoPow(x: bv16): bv16
  requires 0 <= x <= 16
{
  1 << x
}

function method oneMask(n: bv16): bv16
    requires 0 <= n <= 16
    ensures oneMask(n) == twoPow(n)-1
{
   twoPow(n)-1
}

function method OneMaskOr(n: bv8): bv8 
    requires 0 <= n <= 8
    ensures OneMaskOr(n) as bv16 == oneMask(n as bv16)
{
    if n == 0 then 0 else (1 << (n-1)) | OneMaskOr(n-1)
}

function twos(): seq<bv8> {
    [1,2,4,8, 16,32,64,128]
}


function method linearBits(n: bv8) : bv8 
    requires 0 <= n <= 255;
    ensures 0 <= linearBits(n) <= 8
{
    (n & 1) + ((n & 2)>>1) + ((n & 4)>>2) + ((n & 8) >> 3) + ((n & 16) >> 4) + ((n & 32)>>5) + ((n & 64)>>6) + ((n & 128)>> 7)
}

function countOneBits(n:bv8): bv8 
    requires 0 <= n <= 255
    // ensures 0 <= countOneBits(n) <= 8
    decreases n
{
    if n == 0 then 0 else (n & 1) + countOneBits(n >> 1)
}

// lemma shiftIsOneLess(n: bv8, v: bv8) 
//     requires v == n >> 1;
//     ensures forall n :: 0 <= n <= 255 ==> (countOneBits(n) - countOneBits(n>>1)) <= 1
//     decreases n
// {
//     forall n' | 0 <= n' < n {
//         shiftIsOneLess(n', n' >> 1);
//     }
// }

lemma allLessThan8(n: bv8) 
    requires 0 <= n <= 255
    ensures forall n: bv8 :: 0 <= n <= 255 ==> n >> 8 == 0
{
    forall n' | 0 <= n' <= n 
        ensures n' >> 8 == 0
    {
        assert n' >> 8 == 0;
    }
}

lemma eightExists(n: bv8) 
    requires 0 <= n <= 255
    ensures exists x: bv8 :: 0 <= x <= 8 && n >> x == 0
{
    if 0 <= n <= 255 {
        var x :| 0 <= x <= 8 && n >> x == 0 ;
        assert n >> (8 as bv8) == 0;
        assert n >> x == 0;
    }else{

    }
}

// lemma allLessThanN(n: bv8)
//     requires 0 <= n <= 255
//     ensures forall n: bv8 :: 0 <= n <= 255 ==> (exists k: bv8 :: 0 <= k <= 8 && n >> k == 0)
// {
//     if 0 <= n <= 255 { 

//         forall n: bv8 | 0 <= n <= 255 
//             ensures exists k: bv8 :: 0 <= k <= 8 && n >> k == 0
//         {

//             if 0 <= n <= 255 {
//                 assert 0 <= n <= 255;

//                 var k: bv8 :| 0 <= k <= 8 && k == 8;
//                 assert 0 <= k <= 8;
//                 assert n >> k == 0;
//             }
//         }
//     }else{

//     }
// }

lemma rightShiftIsLess(n: bv8, x: bv8) 
    requires x == n >> 1;
    ensures x <= n;
{
    calc ==> {
        n / 2 < n;
        x == n/2;
        x <= n;
    }
}

lemma shiftMaintainsRange(n: bv8, x: bv8)
    requires 0 <= n <= 255
    requires x == n >> 1
    ensures 0 <= x <= 255
{
    if 0 <= n <= 255 && x == n >> 1 {
        rightShiftIsLess(n,x);
        assert 0 <= x <= n <= 255;
    }
}

// lemma CountOneBitsRange(n: bv8)
//     requires 0 <= n <= 255
//     ensures 0 <= countOneBits(n) <= 8
// {
//  if n == 0 {
//      assert countOneBits(n) == 0;
//  }else{
//      var x := n >> 1;
//     //  shiftMaintainsRange(n,x);
//     //  if 0 <= x <= 255;
//     assert 0 <= x <= 255;
//      eightExists(x);
//      var k: bv8 :| 0 <= k <= 8 && x >> k == 0;
//      assert 0 <= k <= 8;
//     //  calc == {
//     //      countOneBits(n);
//     //      n & 1 + countOneBits(n>>1);
//     //      n & 1 + countOneBits(x);
//     //  }

//  }
// }

lemma CountOneBitsRange2(n: bv8) 
    requires 0 <= n <= 255
    ensures forall n :: 0 <= countOneBits(n) <= 8
// {
//     if 0 <= n <= 255 {
//         forall n' | 0 <= n' <= n 
//             ensures 0 <= countOneBits(n') <= 8
//         {
//             assert  0 <= countOneBits(n') <= 8
//         }
//     }
// }

method hammingWeight(n: bv8) returns (count: bv8 )
    ensures count == linearBits(n)
{
    count := 0;
    var i := 0;
    var n' := n;
    while i < 8
        invariant 0 <= i <= 8
        invariant n' == n >> i
        invariant count == linearBits(n & oneMask(i) as bv8);
        decreases 8 - i
    {
        count := count + n' & 1;
        n' := n' >> 1;
        i := i + 1;
    }
}

function removeTilNextOne(n: bv8): bv8 {
    n & (n-1)
}


// method rtno(n: bv8, ghost p: bv8) returns (n': bv8, ghost p': bv8) 
//     requires 0 <= p <= 7
//     requires (n >> p) << p == n
//     ensures removeTilNextOne(n) == n'
//     ensures n' == n & (n-1)
//     ensures p' == p+1
//     ensures n & (n-1) == (n >> p') << p'
// {
//     n' := n & (n-1);
//     p' := p+1;
//     assert n & (n-1) == (n >> p') << p';
// }

// lemma pexists(n: bv8) returns (p: bv8)
//     ensures exists p :: 0 <= p <= 8 ==> n & (n-1) == (n >> p) << p
// {
//    if p :| 0 <= (p-1) <= 7 && 1 << (p-1) == n {
//     calc {
//         (n >> p) << p;
//         {funky(p, n);}
//         (0) << p;
//         0;
//         {singleToZero(n, p-1);}
//         n & (n-1);
//         0;
//     }
//        //assert  n & (n-1) == (n >> p) << p;
//    }else if p,k :| 0 <= p < k <= 7 && n == (1 << p) | (1 << k) {

//    }
// }

lemma funky(p: bv8, n: bv8) 
    requires 1 <= p <= 8 
    requires n == 1 << (p-1)
    ensures n >> p == 0
{
    assert n >> p == 0;
}

lemma singleToZero(n: bv8, p: bv8)
    requires 0 <= p <= 7
    requires n == 1 << p 
    ensures n & (n - 1) == 0
{
    assert n & (n -1) == 0;
}
 

//128+1+2 1000 0011
//128-1   1000 0010
// & .    1000 0010
// 1000 0010
// 1000 0001
//&1000 0000
// 0111 1111
//&0000
method hammingWeight2(n: bv8) returns (count: bv8) 
    ensures count == linearBits(n)
{
    count := 0;
    var n': bv8 := n;
    // CountOneBitsRange2(n);
    // assert 0 <= countOneBits(n) <= 8; 
    while n' > 0
        invariant n' <= n
        invariant 0 <= n' <= 255
        invariant 0 <= count <= 8
        invariant count == linearBits(n - n')
        decreases linearBits(n')
    {
            // ghost var old_decreases := linearBits(n');
            count := count + 1;
            n' := n' & (n' - 1);
            count2bits(count, n, n');
            //  assert linearBits(n') < old_decreases;
            // assert count == linearBits(n - n');
    }
    assert n' == 0;
}




// lemma xorLte(n: bv8) 
//     requires n > 0
//     ensures removeTilNextOne(n) < n
//     decreases removeTilNextOne(n)
// {
//     if n == 1 {
//         assert removeTilNextOne(0) == 0;
//         assert 0 < n;
//     }else if n > 0 {
//         xorLte(n);
//         if  removeTilNextOne(n) < n {
//             assert removeTilNextOne(removeTilNextOne(n)) < n;
//         }
//     }
// }
// 111
// 110


lemma count2bits(count: bv8, n: bv8, n': bv8)
    requires n > 0
    requires n' <= n
    ensures count == linearBits(n - n') 

method testLin() {
    assert 1 == linearBits(64);
    assert 1 == linearBits(128);
    assert 4 == countOneBits(240);
    assert 8 == countOneBits(255);
    assert 8 == linearBits(255);
    var foo: bv8 := 3;
    var boo: bv8 := 0;
    assert boo - 1 == 255;
}

function countOneBits2(n:bv8, i: int, j:int): bv8
  requires i >= 0 && i <= j && j <= 8
  decreases 8-i {
  if i == j then 0
  else (n&1) + countOneBits2(n >> 1, i+1, j)
}

method hammingWeight3(n: bv8) returns (count: bv8 )
ensures count == countOneBits2(n,0,8)
{
    count := 0;
    var i := 0;
    var n' := n;
    //
    assert count == countOneBits2(n,0,i);
    //
    while i < 8
        invariant 0 <= i <= 8;
        invariant n' == n >> i;
        invariant count == countOneBits2(n,0,i);
    {
        count := (n' & 1) + count;
        n' :=  n' >> 1;
        i :=  i + 1;
    }
}

// lemma 
    // assert (0 as bv8) & (0-1) == 0;
    // assert (0 == countOneBits(0));
    // assert (n & oneMask(0)) == 0;
    // assert countOneBits(0) == 0;
    // assert 1 as bv8 << 8 == 0;
    // assert oneMask(7) as bv8 == 127;
    // assert n & 255 == n;
    // assert oneMask(0) == 0;
    //aagh so fucking fiddly
    //basically I need to line up all these off by one errors in the invariants
