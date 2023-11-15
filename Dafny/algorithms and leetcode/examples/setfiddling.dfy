function twos(): set<bv8> 
{
  {1,2,4,8,16,32,64,128}
}

// lemma shiftgetsbigger() 
//   ensures forall k: bv8 :: 0 < k < 128 ==> (k << 1) > k
// {

// }


method foo() returns (res: bv8)

{
  res := 0;
  var j: bv8 := 1;

  assert |twos()| == 8;
  assert 2 in twos();
  assert j in twos();
  label startup: while j <= 128
    invariant j in twos();
    decreases 256-j as bv16
  {
    res := res + 1;
    j := j << 1;  
	if j == 128 {
		break startup;
	}
  }
  return res;
}