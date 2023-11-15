
function method power(a:nat, n:nat):nat
    ensures power(a,n) == if n == 0 then 1 else power(a, n-1) * a
{
	if (n==0) then 1 else power(a,n-1) * a
}


// predicate IsSingleDecimalDigit(d: nat) { 0 <= d && d <= 9 }

// predicate NumberOfDecimalDigits(n: nat, length: nat)
//     requires length >= 1
// 	decreases length
// {
// 	(length == 1 && IsSingleDecimalDigit(n)) ||
// 	(length > 1 && !IsSingleDecimalDigit(n) && NumberOfDecimalDigits(n/10, length-1)) 
// }


method {:verify true} findNumberOfDigitsG(n: nat) returns (length: nat)
	// ensures NumberOfDecimalDigits(n, length)
{
    assert !NumberOfDecimalDigits(17,1);
	assert NumberOfDecimalDigits(17, 2);
	assert !NumberOfDecimalDigits(17, 3);
	if n == 0
	{
		length := 1;
	} else {
		ghost var tenpower: nat := 1;
		ghost var truncated_n := 0;
		ghost var oldLength: int := -1;
		length := 0;
		var n' := n;
		while n' > 0 
			invariant length == oldLength + 1
			invariant 1 <= tenpower 
			invariant tenpower == power(10, length)
			invariant truncated_n == n % tenpower
            // I believe the following are true but Dafny's induction is failing to prove them
            // invariant n' == n / tenpower
            // invariant n == truncated_n + tenpower * n'
			// invariant tenpower > 1 ==> NumberOfDecimalDigits(truncated_n, length)
		{
			oldLength := length;
			length := length + 1;
			n' := n' / 10;
			tenpower := tenpower * 10;
			truncated_n := n % tenpower;
		}
	}
}

predicate IsSingleDecimalDigit(d: nat) { 0 <= d && d <= 9 } // returns true if it's a signle-digit number

predicate NoLeadingZeros(q: seq<nat>) // returns true if the number is zero or has no leading zeros
    requires |q| != 0
{
    q[0] == 0 ==> |q| == 1
}

predicate IsDecimal(q: seq<nat>) // returns true if it's a sequence of digits (which creates a decimal number)
{
    |q| != 0 && (forall d :: d in q  ==> IsSingleDecimalDigit(d)) && NoLeadingZeros(q)
}

function SeqToNat(q: seq<nat>): nat // requires q is decimal - returns natural number out of a sequnce // recursive function
    requires IsDecimal(q)
{
    if |q| == 1 then q[0] else SeqToNat(q[..|q|-1])*10+q[|q|-1]
}

predicate DecimalDigits(q: seq<nat>, n: nat) // gets a sequnce & a number and returns true if they are the same
{
    IsDecimal(q) && SeqToNat(q) == n
} 

predicate NumberOfDecimalDigits(n: nat, length: nat) // returns true if n is of length |length| (for example: true for 1223 4 , false for 1223 2)
    decreases length
{
    (length == 1 && IsSingleDecimalDigit(n)) ||
    (length > 1 && !IsSingleDecimalDigit(n) && NumberOfDecimalDigits(n/10, length-1)) 
}

method {:verify true} findNumberOfDigits(n: nat) returns (length: nat)
    ensures NumberOfDecimalDigits(n, length)
{
    if n<10{
        length := 1;
    } else{
        length := findNumberOfDigits(n/10);
        length := length + 1;
    }
}
   