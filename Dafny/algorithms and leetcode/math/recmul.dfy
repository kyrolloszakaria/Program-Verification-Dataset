function method power(A:int, N:nat):int
{
	if (N==0) then 1 else A * power(A,N-1)
}

function bvmul(a: bv8, b: bv8): bv16 {
	(a as bv16) * (b as bv16)
}
function bvmul16(a: bv16, b: bv16): bv16 {
	a * b
}
function bvshift(a: bv16): bv16 {
  a << 8
}

const twoSixteenth: int := power(2,16);

function pow2(A: nat): (c: int)
  ensures c == power(2, A)
{
  power(2, A)
}

function max2pow(z: bv16, i: nat): nat
  requires 0 <= i <= 16
  ensures power(2, max2pow(z,i)) >= (z as int)
  ensures 0 <= max2pow(z,i) <= 16
  decreases 16 - i
{
  if (z as int) > power(2, i) then max2pow(z, i+1) else i  
} 



// function bvBitToMask(a: bv16, start: bv16, index: bv8): (c: bv16) 
//   requires index == 0 ==> a == start && start in two16;
//   decreases twoSixteenth - (a as int);
// {
//   if a == 0 then 0 else if a & 1 == 1 then a else bvBitToMask(a | (a>>1), start, index+1)
// }

function method oneMask(n: bv16): bv16 
    requires 0 <= n <= 8
    ensures oneMask(n) == pow2(n as nat) as bv16 - 1
{
    if n == 0 then 0 else (1 << (n-1)) | oneMask(n-1)
}


function twos(): set<bv8> 
{
  {1,2,4,8,16,32,64,128}
}

function twos16(): set<bv16> 
{
  {1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768}
}

const two16: set<bv16> := {1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768};
const two16one: set<bv16> := {1,3,7,15,31,63,127,255,511,1023,2047,4095,8191,16383,32767};

function mulpartial(a: bv16, b: bv16, j: bv16): (c: bv16) 
  requires j in two16;
{
  a * (b as bv16 & (0xFFFF - oneMask(j as bv16)) )
}

// method mul(a: bv8, b: bv8) returns (hl: bv16)
//   requires 0 <= a <= 255;
//   requires 0 <= b <= 255;
//   ensures hl == bvmul(a,b)
// {
//   hl := 0;
//   if a == 0 || b == 0 {
//     return hl;
//   }

//   var j: bv8, i: bv8 := 1, 1;
//   var stack: seq<bv16> := [a as bv16];
//   hl := a as bv16;
//   assert j == 1;
//   assert i == 1;
//   label buildup: while j < b
//     invariant 0 <= b <= 255;
//     invariant j in twos();
//     invariant 0 < i <= 8;
//     invariant hl == bvmul(j,a);
//     invariant |stack| == (i as int);
//     decreases b-j
//   {
//     hl := hl+hl;
//     stack := stack + [hl];
//     j := j << 1;
//     if j == 128 {
//       break buildup;
//     }
//     i := i + 1;
//   }
//   hl := 0;
//   j := j >> 1;
  // assert i as int == |stack|-1;

  
  // while j > 0 
  //   invariant hl ==  bvmul16(a as bv16, (b as bv16 & (0xFFFF - bvBitToMask(j as bv16)) ));
  //   invariant |stack| as bv8 == i;
  //   decreases j
  // {
  //   if (b & j) > 0 {
  //     hl := hl + stack[i];
  //     stack := stack[..i];
  //   }else{
  //     stack :=stack[..i]; 
  //   }
  //   j := j >> 1;
  //   i := i-1;
  // }

//   return hl;
// }

method mul(a: bv8, b: bv8) returns (bc: bv16)
  requires 0 <= a <= 255;
  requires 0 <= b <= 255;
  ensures bc == bvmul(a,b)
{
  if a == 0 || b == 0 {
    return 0;
  }
  var hl: bv16 := a as bv16;
  var j: bv16 := 1;
  var i: bv4 := 0;
  bc := 0;
  while i <= 7 
    invariant i <= 8;
    invariant j in twos16();
    invariant hl == (j * (a as bv16));
    invariant bc ==  bvmul16(a as bv16, (b as bv16 & (0xFFFF - oneMask(j)) ));
    decreases 8-i;
  {
    if (((b as bv16) & j) > 0) {
      bc := bc + hl;
    }
    hl := hl + hl;
    i := i + 1;
    j := j << 1;
  }
  return bc;
}

  // 101

  // 111
  //-111
  // 000

  // 0101

  // 1111
  //-0011
  // 1100

  // 101

  //-111
  // 001
  // 110

  //000
  //111
  //b & (~j)