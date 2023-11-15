function twoPow(x: bv8): bv8
  requires 0 <= x <= 7
{
  1 << x
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

function bvBitToMask(a: bv16): bv16 
  decreases a ^ ( a & (a-1))
{
  if a == 0 then 0 else if a & 1 == 1 then a else bvBitToMask(a | (a>>1))
}

method shiftmul(a: bv8, b: bv8) returns (h: bv8, l: bv8)
  requires 0 <= a <= 255;
  requires 0 <= b <= 255;
  ensures bvshift(h as bv16) | (l as bv16) == bvmul16(a as bv16, b as bv16)
{
  h,l := 0, 0;
  if a == 0 || b == 0 {
    return h,l;
  }
  var i: bv16 := 1;
  var d: bv8, e: bv8 := 0,a;
  while i < 256 
    invariant 0 < i <= 256;
    invariant bvshift(d as bv16) | (e as bv16) == (a as bv16) * i;
    invariant bvshift(h as bv16) | (l as bv16) == bvmul16(a as bv16, (b as bv16 & bvBitToMask(i>>1)));
    decreases 256-i
  {
    if (b as bv16 & i) != 0 {
      if (l as bv16 + e as bv16 >= 256) {
        l := l + e;
        h := h + d+1;
      }else{
        l := l + e;
        h := h + d;
      }
    } 
    i := i << 1;
    if e >= 128 {
      e := e << 1;
      d := (d << 1)+1;
    }else{
      e := e << 1;
      d := (d << 1);
    }
  }
  return h,l;
}


method mul(a: bv8, b: bv8) returns (h: bv8, l: bv8)
  requires 0 <= a;
  requires 0 <= b;
  ensures bvshift(h as bv16) | (l as bv16) == bvmul(a,b)
{
  h,l := 0, 0;
  if a == 0 || b == 0 {
    return h,l;
  }
  var i: bv8 := b;
  while i > 0 
    decreases i
  {
    if(l+a > 255) {
      l:= l+a;
    }else{
      l:=l+a;
      h := h+a+1;
    }
    i := i-1;
  }
  return h,l;
}


method muls(a: bv8, b: bv8) returns (hl: bv16)
  requires 0 <= a;
  requires 0 <= b;
  ensures hl == bvmul(a,b)
{
  hl := 0;
  if a == 0 || b == 0 {
    return hl;
  }
  var i: bv8 := b;
  while i > 0 
    decreases i
  {
    hl := hl+(a as bv16);
    i := i-1;
  }
  return hl;
}

// lemma orSelfEnbiggens(x: bv8)
//   ensures x | (x>>1) >= x 
// {
//   if x == 0 || x == 1 {}
//   else{
//     calc {
//       x | (x>>1);
//     }
//   }
// }
