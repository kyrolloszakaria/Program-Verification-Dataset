function Pick(s: set<int>): int 
	requires s != {}
{
	var x :| x in s; x
}

function Sum(s: set<int>): int 
	decreases s
{
	if s == {} then 0 else
	var x := Pick(s);
	x+Sum(s-{x})
}

lemma SumMyWay(s: set<int>, y: int) 
	requires y in s
	ensures Sum(s) == y + Sum(s-{y})
{
	var x := Pick(s);
	if y == x {

	} else {
		calc {
			Sum(s);
			==
			x + Sum(s - {x});
			==  { SumMyWay(s - {x}, y); }
			x + y + Sum(s - {x} - {y});
			==  { assert s - {x} - {y} == s - {y} - {x}; }
			y + x + Sum(s - {y} - {x});
			==  { SumMyWay(s - {y}, x); }
			y + Sum(s - {y});
		}
	}
}

lemma AddToSum(s: set<int>, y: int) 
	requires y !in s
	ensures Sum(s + {y}) == Sum(s) + y
{
	SumMyWay(s + {y}, y);
}

method AddElement(s: set<int>, a: int, y: int) returns (t: set<int>, b: int) 
	requires a == Sum(s) && y !in s
	ensures t == s + {y} && b == Sum(t)
{
	t := s + {y};
	b := a + y;
	AddToSum(s,y);
}