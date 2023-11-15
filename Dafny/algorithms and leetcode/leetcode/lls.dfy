// var lengthOfLongestSubstring = function(s) {
//     let letters = new Set([]);
//     let longest = 0;
//     let current = 0;
//     foo: for(let j = 0; j < s.length; j++) {
//         for(let i = j; i < s.length; i++) {
//             if(letters.has(s[i])) {
//                 if(current > longest) {
//                     longest = current    
//                 }
//                 //console.log(letters, j,i, current);
//                 letters = new Set([]);
//                 current = 0;
//                 continue foo;
                
//             }else{
//                 letters.add(s[i]);
//                 current++;
//             }
//         }
//     }
//     if(current > longest) {
//         longest = current
//     }
//     return longest
// };

// var test: set<char> := (set x: nat | 0 <= x < 4 :: sample[x]);
function stringToSet(s: string): (r: set<char>)
ensures forall x :: 0 <= x < |s| ==> s[x] in r
{
//  set x | 0 <= x < |s| :: s[x]
 set x | 0 <= x < |s| :: s[x]
}

function stringToSetPartial(s: string, start: int, end: int): (r: set<char>)
	requires 0 <= start <= end < |s|
	ensures forall x :: 0 <= start <= x < end < |s| ==> s[x] in r
{
	set x | 0 <= start <= x < end < |s| :: s[x]
}

function stringToSetSize(s: string): (r: int)
{
 |set x | 0 <= x < |s| :: s[x]|
}

predicate longestSubString(s: string, end: int, longest: int) 
	requires 0 <= end <= |s|
{
	forall a, b :: 0 <= a < b < end ==> stringToSetSize(s[a..b]) <= longest
}

predicate subsetIsOneToOne(s: string, start: int, end: int)
	requires 0 <= start <= end <= |s|
{
	forall x :: x in multiset(s[start..end]) ==> multiset(s[start..end])[x] == 1
}


method lengthOfLongestSubstring(s: string) returns (longest: int) 
	ensures longestSubString(s, |s|, longest);
	//ensures forall a, b :: 0 <= a < b < |s|  ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
	//ensures forall a, k :: 0 <= a < |s| && 0 <= k <= |s| && a+k <= |s| ==> s[a..k]
{
	var letters: set<char> := {};
	var  current: int := 0;
	longest := 0;
	var j,i := 0,0;
	while j < |s|
	 invariant 0 <= j <= |s|
	 invariant longestSubString(s, j, longest)
	 decreases |s|-j
	{
		i := j;
		while i < |s| 
		invariant 0 <= j <= i
		invariant 0 <= i <= |s|
		invariant subsetIsOneToOne(s, j, i) ==> letters == stringToSetPartial(s, j, i)
		invariant !subsetIsOneToOne(s, j, i) ==> letters == {}
		// invariant 0 <= current <= i-j
		// invariant |stringToSetPartial(s, j, i)| == i-j ==> letters == stringToSetPartial(s, j, i)
		decreases |s|-i
		{
			if s[i] in letters {
				assert i > 0;
				if current > longest {
					longest := current;
				}
				assert s[j..i] == s[j..i-1] + [s[i-1]]; 
				
				assert !subsetIsOneToOne(s,j,i) ==> letters == stringToSetPartial(s, j, i-1);
				letters := {};
				current := 0;
				break;
			}else{
				letters := letters + {s[i]};
				// assert letters == stringToSetPartial(s, j, i) == stringToSetPartial(s, j, i-1) + {s[i]};
				current := current + 1;
				i := i + 1;
			}
		}
		j := j + 1;
	}
	assert j == |s|;
	if current > longest {
		longest := current;
	}
	return longest;
}

method Main() {
	// var acab := lengthOfLongestSubstring("abcabcbb");
	// print acab;
	// var bbbb := lengthOfLongestSubstring("bbbbb");
	// print bbbb;
	// var wke := lengthOfLongestSubstring("pwwkew");
	// print wke;
	var meString := "omgford";
	ghost var mslice := meString[2..4];
	stringToSetPartialEquiv(meString, 0, |meString|-1);
	assert stringToSetPartial(meString, 0, |meString|-1) == stringToSetPartial(meString[0..|meString|-1], 0, |meString|-2);
	// assert stringToSetPartial(meString, 2, 4) == stringToSetPartial(meString[2..4], 0, |meString[2..4]|);
}

// lemma stringToSetPartialEquiv(s: string, start: int, end: int) 
// 	requires 0 <= start < end < |s|
// 	ensures stringToSetPartial(s, start, end) == stringToSetPartial(s[start..end], 0, |s[start..end]|)
// {
// 	var left := stringToSetPartial(s, start, end);
// 	var subpiece := s[start..end];
// 	assert |subpiece| > 0;
// 	assert |subpiece| == |s[start..end]|;
// 	subsetEqual(s, subpiece, start, end);
// 	var right := stringToSetPartial(subpiece, 0, |subpiece|);

// 	calc {
// 		stringToSetPartial(subpiece, 0, |subpiece|);
// 		right;
// 		stringToSetPartial(s[start..end], 0, |s[start..end]|);
// 	}

// 	forall x | 0 <= start <= x < end < |s| 
// 		ensures s[x] in left
// 		ensures s[x] in subpiece
// 		ensures s[x] in right;
// 	{
// 		assert s[x] in left;
// 		assert s[x] in subpiece;
// 		assert s[x] in right;
// 	}
// lemma partitionSet(s: string, start: int, end: int) returns (left:set<char>, middle: set<char>, right: set<char>)
// 	requires 0 <= start < end < |s|
// 	ensures left + middle + right == stringToSetPartial(s, 0, |s|-1)
// {
// 	left := stringToSetPartial(s, 0, start);
// 	middle := stringToSetPartial(s, start, end);
// 	right := stringToSetPartial(s, end, |s|-1);
// 	var setsum := left + middle + right;
// 	forall x | 0 <= x < |s| 
// 		ensures s[x] in setsum
// 	{
// 		if 0 <= x < start {
// 			assert s[x] in left;
// 			assert s[x] in setsum;
// 		}
// 		if start <= x < end {
// 			assert s[x] in middle;
// 			assert s[x] in setsum;
// 		}
// 		if end <= x < |s| {
// 			assert s[x] in right;
// 			assert s[x] in setsum;
// 		}
// 	}

// 	assert left + middle + right == stringToSetPartial(s, 0, |s|);
// }



// lemma subsetEqual(s: string, subset: seq<char>, start: int, end: int) 
	// requires |subset| > 0 
	// requires 0 <= start < end < |s|
	// requires subset == s[start..end]
	// ensures forall x :: 0 <= start <= x < end < |s| ==> s[x] in subset
	// decreases end-start
// {
	// assert s[start..end] == s[start..(end-1)] + [s[end-1]];
	// assert subset == s[start..end];
	// assert s[end-1] in subset;
	// if start < end - 1 {
		// subsetEqual(s, s[start..(end-1)], start, end - 1);
	// } 
	// forall x | 0 <= start <= x < end < |s| 
	// 	ensures s[x] in s[start..end] ==> s[x] in subset
	// {
	// 	assert s[x] in s[start..end];
	// 	assert s[x] in subset;
	// }
// }