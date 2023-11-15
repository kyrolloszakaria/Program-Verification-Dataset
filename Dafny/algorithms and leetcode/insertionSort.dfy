predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted (a:array<int>)
  reads a;
{
  sorted_between (a, 0, a.Length)
}

// method Max(a: int, b: int) returns (r: int) 
// 	ensures r >= a && r >= b;
// {
// 	if (a > b) {
// 		return a;
// 	}else{
// 		return b;
// 	}
// }
function Max(a: int, b: int): int 
{
	if (a > b) then a else b
}

method insertionSort(a: array<int>)
	modifies a;
	requires a.Length > 0;
	ensures sorted(a);
	ensures multiset(old(a[..])) == multiset(a[..]);
{
	var j: nat := 1;
	while (j < a.Length)
		invariant j <= a.Length;
		invariant multiset(old (a[0..j])) == multiset(a[0..j]);
		invariant sorted_between(a, 0, j-1);
	{
		var key: int := a[j];
		var i: int := j - 1;
		while (i >= 0 && a[i] > key)
			invariant -1 <= i < j < a.Length;
			invariant forall u,v :: u <= u < j < v < i ==> a[u] <= a[v];
			invariant old(a[0..Max(i,0)]) == a[0..Max(i,0)];
			invariant sorted_between(a, 0, j-1);
		{
			a[i+1] := a[i];
			i := i - 1;
		}
		a[i+1] := key;
		j := j + 1;
	}

}