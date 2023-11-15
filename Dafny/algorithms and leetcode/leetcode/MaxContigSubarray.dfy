
function method max(a: int, b: int): int 
    ensures max(a,b) == if a > b then a else b
{
    if a > b then a else b
}

function method sumSeq(nums: seq<int>): int 
    ensures |nums| == 0 ==> sumSeq(nums) == 0
    ensures |nums| > 0 ==> sumSeq(nums) == nums[0] + sumSeq(nums[1..])
{
    if |nums| == 0 then 0 else nums[0] + sumSeq(nums[1..])
}

function method sumSeqTail(nums: seq<int>): int 
    ensures |nums| == 0 ==> sumSeqTail(nums) == 0
    ensures |nums| > 0 ==> sumSeqTail(nums) == sumSeqTail(nums[..(|nums|-1)]) + nums[|nums|-1]
{
    if |nums| == 0 then 0 else sumSeqTail(nums[..(|nums|-1)]) + nums[|nums| - 1]
}

function reverseSeq(nums: seq<int>): seq<int>
    ensures |reverseSeq(nums)| == |nums|
    ensures forall i :: 0 <= i < |nums| ==> reverseSeq(nums)[i] == nums[|nums|-i-1]
{
 if |nums| == 0 then [] else [nums[|nums|-1]] + reverseSeq(nums[..(|nums|-1)])
}

lemma doubleReverse(nums: seq<int>) 
    ensures reverseSeq(reverseSeq(nums)) == nums
{

}

lemma splitReverse(nums: seq<int>)
    requires |nums| > 0
    ensures nums[1..] == reverseSeq(reverseSeq(nums)[..(|nums|-1)])
{
}

// lemma revSeq(nums: seq<int>)
//     ensures sumSeq(nums) == sumSeq(reverseSeq(nums))
// {

// }

lemma multisetSequence(nums: seq<int>, ms: multiset<int>) 
    requires |nums| > 0
    requires multiset(nums[1..]) == ms;
    ensures multiset(nums) == ms + multiset{nums[0]}
{
    assert nums == [nums[0]]+nums[1..];
    var z := nums[0];
    assert z in multiset(nums);
    assert forall i :: 1 <= i < |nums| ==> nums[i] in ms;
    assert forall i :: 1 <= i < |nums| ==> nums[i] in multiset(nums);
    assert forall i :: 1 <= i < |nums| && nums[i] != nums[0] ==> multiset(nums)[nums[i]] == ms[nums[i]];
    // if nums[0] in ms {
    //     assert multiset(nums)[nums[0]] == ms[nums[0]]+1;
    // }else{
    //     assert ms[nums[0]] == 0;
    //     assert multiset(nums)[nums[0]] == 1;
    // }
}

lemma multisetSequenceRemove(nums: seq<int>, ms: multiset<int>) 
    requires |nums| > 0
    requires multiset(nums) == ms;
    ensures multiset(nums[1..]) == ms - multiset{nums[0]}
{
    assert nums == [nums[0]]+nums[1..];
}

lemma multisetSequenceSplitRemove(nums: seq<int>, ms: multiset<int>, z: int, i : int) 
    requires |nums| > 0
    requires 0 <= i < |nums|
    requires nums[i] == z;
    requires multiset(nums) == ms;
    ensures multiset(nums[..i]+nums[(i+1)..]) == ms - multiset{z}
{
    assert nums == nums[..i] + [z] + nums[(i+1)..];
}

lemma seqZ(nums: seq<int>, z: int)
    requires z in nums;
{
    assert exists i :: 0 <= i < |nums| ==> nums[i]  == z;
}

// lemma sumSeqSplit(nums: seq<int>, z: int, i: int)
//     requires |nums| > 0
//     requires 0 <= i < |nums|
//     requires nums[i] == z;
//     ensures sumSeq(nums[..i]+nums[(i+1)..]) == sumSeq(nums) - z;
// {
//     assert nums == nums[..i] + [z] + nums[(i+1)..];
//     calc {
//         sumSeq(nums);
//         ==
//         sumSeq(nums[..i]+[z]+nums[(i+1)..]);

//     }
// }

// lemma so(numsa: seq<int>, numsb: seq<int>)
//     requires |numsa| == |numsb|
//     requires multiset(numsa) == multiset(numsb)
//     ensures sumSeq(numsa) == sumSeq(numsb)
// {
//     if |numsa| > 0 {
//         assert |numsa| > 0;
//         var z := numsa[0];
//         assert multiset(numsa)[z] >= 1;
//         var bz := numsa[1..];
//         var q := multiset(numsa);
//         var j := multiset(bz);
//         multisetSequenceRemove(numsa, q);
//         assert j == q - multiset{z};
//         assert z in multiset(numsa);
//         assert z in multiset(numsb);
//         assert z in numsa;
//         assert z in numsb;
//         assert multiset(numsa) != multiset{};
//         assert multiset(numsb) != multiset{};
//         assert multiset(numsa[1..]) == multiset(numsa)-multiset{z};
//         var i :| 0 <= i < |numsb| && numsb[i] == z;
        
//         assert numsb == numsb[..i] + [z]+ numsb[(i+1)..];
//         var bmz := numsb[..i] + numsb[(i+1)..];
//         multisetSequenceSplitRemove(numsb, multiset(numsb), z, i);
//         assert j == multiset(bmz);
//         so(bz, bmz);
//         assert sumSeq(bz) == sumSeq(bmz);
//         assert sumSeq(numsa) == z + sumSeq(bz);
//         assert sumSeq(numsb) == z + sumSeq(bmz);
//         // assert sumSeq(numsb) ==
//         //ghost var x :| x in multiset(numsa);
//     }
// }

// lemma someThing(nums: seq<int>) 
//     requires |nums| >= 1
//     ensures sumSeq(nums[1..]) == sumSeq(reverseSeq(nums)[..|nums|-1])
// {

// }

// lemma reverseSum(nums: seq<int>)
//     ensures sumSeq(nums) == sumSeq(reverseSeq(nums))
// {
//     if |nums| == 0 {

//     } else if |nums| == 1 {

//     }else {
//         var rev := reverseSeq(nums);
//         var k := nums[0];
//         assert rev[|nums|-1] == k;
        
//         // assert sumSeqTail(reverseSeq(nums)) == k + sumSeqTail(rev[..(|nums|-1)]);
//         assert nums[1..] == reverseSeq(rev[..(|nums|-1)]);
//         assert sumSeq(nums) == k + sumSeq(nums[1..]);
//         calc {
//             sumSeq(reverseSeq(nums));
//             ==
//             k + sumSeq(rev[..(|nums|-1)]);
//             == 
//             k + sumSeq(nums[1..]);
//             ==
//             sumSeq(nums);
//         }
//     }
// }

// lemma sumSeqsEqual(nums: seq<int>) 
//     ensures sumSeq(nums) == sumSeqTail(nums);
// {
//     if |nums| == 0 {
//         assert sumSeq(nums) == 0 == sumSeqTail(nums);
//     }else if |nums| == 1 {
//         assert sumSeq(nums) == nums[0] == sumSeqTail(nums);
//     }else if |nums| > 1 {
//         var somenums := nums[1..];
//     }
// }

method Test() {
    var goober := [2997, 3, 3];
    var what := multiset(goober);
    assert what[3] > 1;
    var goober2 := [2997,  3];
    assert multiset(goober2) == what - multiset{3};
    assert sumSeq(goober[0..0]) == 0;
    assert sumSeq(goober[0..1]) == 2997;
    assert sumSeq(goober[0..2]) == 3000;
}

// method maxContigSubarrayNaive(nums: seq<int>) returns (maxsum: int)
//     requires |nums| >= 1
//     ensures forall i, j :: 0 <= i <= j <= |nums| ==> maxsum >= sumSeq(nums[i..j])
// {
//     var n := |nums|;
//     var maxSum := nums[0];
//     for left := 0 to n-1 
//         invariant 0 <= left <= n-1
//     {
//         for right := left to n-1 
//             invariant left <= right <= n-1;
//         {
//             var windowSum := 0;
//             ghost var wsum := sumSeq(nums[left..left]);
//             assert wsum == 0;

//             var k := left;
//             while k <= right
//                 invariant left <= right
//                 invariant left <= k <= right+1
//                 invariant windowSum == sumSeq(nums[left..k])
//             {
//                 windowSum := windowSum + nums[k];
//                 k := k + 1;
//                 wsum := sumSeq(nums[left..k]);
//             }

//             maxSum := max(maxSum, windowSum);
//         }
//     }


//     return maxSum;
// }

method maxContigSubarrayBetter(nums: seq<int>) returns (maxsum: int)
    requires |nums| >= 1
{
    var n := |nums|;
    var maxSubarraySum := 0;
    for left := 0 to n-1 {
        var runningWindowSum := 0;
        for right := left to n-1 {
            runningWindowSum := runningWindowSum + nums[right];
            maxSubarraySum := max(maxSubarraySum, runningWindowSum);
        }
    }
    return maxSubarraySum;
}

method maxContigousSubarraySum(nums: seq<int>) returns (maxsum: int)
    requires |nums| > 1
{
    var maxSoFar := nums[0];
    var maxEndingHere :=  nums[0];
    for i := 1 to |nums|-1 {
        maxEndingHere := max(maxEndingHere + nums[i], nums[i]);
        maxSoFar := max(maxSoFar, maxEndingHere);
    }
    return maxSoFar;
}

// method simpleSum(row: seq<int>, left: int, right: int) returns (sum: int) 
//     requires 0 <= left <= right < |row|
//     ensures sum == sumSeq(row[left..(right+1)])
// {
//     sum := 0;
//     var k := left; 
//     while k <= right 
//         invariant left <= k <= right+1
//         invariant sum == sumSeq(row[left..k])
//     {
//         sum := sum + row[k];
//         k := k + 1;
//     }
//     assert k == right+1;

// }

// lemma sumSeqSplit(a: seq<int>, i: int)
//     requires 0 <= i <= |a|
//     ensures sumSeq(a) == sumSeq(a[..i]) + sumSeq(a[i..])
// {
//     assert a == a[..i] + a[i..];
//     if a == [] {
//         assert a[..0] == [];
//         assert a[0..] == [];
//         assert sumSeq(a) == 0;
//     } else if i == |a| && a[i..] == [] {
//         assert a == a[..i] + [];
//         assert a == a[..i];
//         // assert sumSeq(a[i..]) == 0;
//         calc {
//             sumSeq(a);
//             == 
//             sumSeq(a[..i]) + sumSeq(a[i..]);
//             ==
//             sumSeq(a)+sumSeq([]);
//             ==
//             sumSeq(a)+0;
//             ==
//             sumSeq(a);
//         }
//     }else if a[..i] != [] {
//         var p := sumSeq(a[..i]);
//         var s := sumSeq(a[i..]);
//         assert a[..i] == a[..(i-1)] +[a[i-1]];
//         assert a[(i-1)..] == [a[i-1]]+a[i..];
//         assert s + a[i-1] == sumSeq(a[(i-1)..]);
//         sumSeqSplit(a[..(i-1)],i-1);
//         assert sumSeq(a[..(i-1)]) == sumSeq(a[..(i-1)]) + sumSeq([a[i-1]]);

//     }
// }

// lemma sumSeqConcat(a: seq<int>, b: seq<int>)
//     ensures sumSeq(a+b) == sumSeq(a) + sumSeq(b)
// {
//     if a == [] {
//         assert sumSeq(a) + sumSeq(b) == sumSeq(a+b);
//     }else if b == [] {
//         assert sumSeq(a) + sumSeq(b) == sumSeq(a+b);
//     }else if |a| == 1 {
//         assert sumSeq(a) == a[0];
//         assert sumSeq(a+b) == a[0] + sumSeq(b);
//     }else{
//         calc {
//             sumSeq(a+b);
//             == 
//             sumSeq(a[..(|a|-1)]+[a[|a|-1]]+ b);
//             == 
//             sumSeq(a[..(|a|-1)]) + sumSeq([a[|a|-1]]+ b);
//         }
//     }
// }


// lemma sumSeqCommut(row: seq<int>, k: int)
//     requires |row| >= 1
//     requires row[|row|-1] == k
//     ensures sumSeq(row[..|row|-1]) == sumSeq(row)-k
// {
//    assert row == row[..|row|-1]+[k];
// }

lemma somethings(nums: seq<int>, sum: int, k: int)
    requires sum == sumSeq(nums)
    ensures sumSeq([sum,k]) == sumSeq([k]+nums)
{

}

//    ([1,2,3]+[4]) == 10 == (1+(2+(3+(4))))
//    ([4]+[1,2,3]) == 10 == (4+(1+(2+(3))))
// lemma sumSeqCommut(row: seq<int>, k: int)
//     ensures sumSeq(row+[k]) == sumSeq([k]+row)
// {
//     if row == [] {
//         assert sumSeq([]+[k]) == sumSeq([k]+[]);
//     }else if |row| == 1 {
//         assert row == [row[0]];
//         // assert sumSeq([row[0]]+[k]) == sumSeq([k]+[row[0]]);
//         calc {
//             sumSeq(row+[k]);
//             ==
//             sumSeq([row[0]]+[k]);
//             ==
//             row[0]+sumSeq([k]);
//             ==
//             row[0]+k;
//             ==
//             k+row[0];
//             ==
//             k+sumSeq([row[0]]);
//             ==
//             sumSeq([k]+[row[0]]);
//             ==
//             sumSeq([k]+row);
//         }

//     }else if |row| == 2 {
//         assert row == [row[0],row[1]];

//     }else{

//     }
//     // var oldSum := sumSeq(row);
//     // assert oldSum + k == sumSeq([k]+row);
//     // assert oldSum + k == sumSeq(row+[k]);

// }

lemma sumSeqs(row: seq<int>, left: int, k: int)
    requires 0 <= left <= k < |row|-1
    // ensures sumSeq(row[left..k+1]) == sumSeq(row[left..k]) + row[k]
{
    assert row[left..k+1] == row[left..k]+[row[k]];
    calc {
        sumSeq(row[left..k+1]);
        ==
        sumSeq(row[left..k]+[row[k]]);
    }

}