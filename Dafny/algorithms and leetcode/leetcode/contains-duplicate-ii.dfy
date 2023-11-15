/*
//Given an integer array nums, return true if any value appears at least twice in the array, and return false if every element is distinct.

 https://leetcode.com/problems/contains-duplicate/

function containsDuplicate(nums: number[]): boolean {
    let m = new Set();
    for(let elem of nums) {
        if(m.has(elem)) {
            return true;
        }
        m.add(elem);
    }
    return false;
};
*/
function method seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}

method containsDuplicateI(nums: seq<int>) returns (containsDuplicate: bool)
    ensures containsDuplicate ==>  exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
{
    // var windowGhost: set<int> := {};
    var windowSet: set<int> := {};
    for i:= 0 to |nums| 
        // invariant 0 <= i <= |nums|
        // invariant forall j :: 0 <= j < i < |nums|  ==> nums[j] in windowSet
        invariant forall x :: x in windowSet ==> x in nums[0..i]
        // invariant seqSet(nums, i) <= windowSet
    {
        // windowGhost := windowSet;
        if nums[i] in windowSet { // does not verify
        // if nums[i] in seqSet(nums, i) { //verifies
            return true;
        }
        windowSet := windowSet + {nums[i]};
    }
    return false;
}

function max(a: nat, b: int): nat 
    ensures max(a,b) == if a < b then b else a
{
    if a < b then b else a
} 

/*
https://leetcode.com/problems/contains-duplicate-ii/
Given an integer array nums and an integer k, return true if there are two distinct indices i and j in the array such that nums[i] == nums[j] and abs(i - j) <= k.

function containsNearbyDuplicate(nums: number[], k: number): boolean {
    let windowSet = new Set();
    const n = nums.length;
    if(k == 0) return false;
    for(let i = 0; i < n; i++) {
        if(windowSet.has(nums[i])) {
            return true;
        }
        if(i >= k) {
            windowSet.delete(nums[i-k]);
        }
        windowSet.add(nums[i]);
    }
    return false;
};

*/
method {:verify  true} containsNearbyDuplicateExtra(nums: seq<int>, k: nat) returns (containsDuplicate: bool) 
    requires k <= |nums|
    requires |nums| < 10
    ensures containsDuplicate ==> exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    var windowSet: set<int> := {};
    // ghost var windowIndices: set<nat> := {};
    // ghost var windowGhost: set<int> := {};
    // ghost var removed: set<int> := {};
    if k == 0 {
        return false;
    }

    // TBU -- true but unneeded invariants 
    //    invariant i < k ==> removed == {} // --TBU
    //    invariant forall j  :: 0 <= j < i-k  ==> nums[j] in removed // TBU
    //    invariant forall j  :: 0 <= j < i  ==> nums[j] in windowGhost //TBU
    //    invariant forall x :: x in windowGhost ==> x in nums[0..i] //TBU
    // True but hard to prove
    // invariant |windowSet| <= k
    // wrong
    // invariant windowSet == windowGhost - removed; -- wrong [1,2,3,4,1],k = 2, windowSet = {4,1}, removed = {1,2,3}

    for i: nat := 0 to |nums| 
        invariant 1 <= k <= |nums|
        // invariant k <= i < |nums| && nums[i] !in windowSet ==> windowSet == windowGhost - {nums[i-k]} + {nums[i]}
        // invariant k <= i ==> forall x :: x in removed ==> x in nums[0..(i-k)]
        // invariant 0 < i <= k  ==> forall j  :: 0 <= j < i ==> nums[j] in windowSet
        // invariant i == k ==> forall j :: i-k <= j < i ==> nums[j] in windowSet

        // invariant forall j ::  0 <= j < i ==> j in windowGhost
        // invariant forall x :: x in windowGhost ==> 0 <= x < |nums|
        // invariant i < k ==> removed == {}
        // invariant k <= i ==> removed == set x | 0 <= x < i-k
        // invariant windowIndices == windowGhost - removed
        invariant windowSetValid(nums, k, i, windowSet)
        // invariant i < |nums| ==> |windowGhost| == i
        // invariant forall x :: x in windowIndices ==> nums[x] in windowSet
        // invariant forall x :: x in windowIndices ==> 0 <= x < |nums|
        // invariant forall x :: x in windowIndices ==> nums[x] in windowSet
        // invariant i > k ==> nums[i-k-1] !in windowSet
        // invariant i > k ==> forall j :: i-k+1 < j < i ==> nums[j] in windowSet
        // invariant k <= i ==> forall j :: i-k <= j < i ==> nums[j] in windowSet
        // invariant k <= i ==> forall x :: x in windowSet ==> x in nums[(i-k)..i]
        // invariant windowSet == set(nums[(max(0, i-k))..i])
    {
        if nums[i] in windowSet {
            windowSetValidIsSufficient(nums, k, i, windowSet);
            return true;
        }
        // if i >= k {
        //     windowIndices := windowIndices - {i-k};
        //     removed := removed + {i-k};
        // }
        windowSet := if i >= k then (windowSet -{nums[i-k]}) + {nums[i]} else windowSet + {nums[i]};
        assert nums[i] in windowSet;
        // windowIndices :=  windowIndices + {i};
        // windowGhost := windowGhost + {i};
    }
    return false;
}

method {:verify  true} containsNearbyDuplicate(nums: seq<int>, k: nat) returns (containsDuplicate: bool) 
    requires k <= |nums|
    requires |nums| < 10
    ensures containsDuplicate ==> exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    var windowSet: set<int> := {};
    if k == 0 {
        return false;
    }

    for i: nat := 0 to |nums| 
        invariant 1 <= k <= |nums|
        invariant windowSetValid(nums, k, i, windowSet)
    {
        if nums[i] in windowSet {
            windowSetValidIsSufficient(nums, k, i, windowSet);
            return true;
        }
        windowSet := if i >= k then (windowSet -{nums[i-k]}) + {nums[i]} else windowSet + {nums[i]};
    }
    return false;
}

method {:verify  true} containsNearbyDuplicateTest(nums: seq<int>, k: nat) returns (containsDuplicate: bool) 
    requires k <= |nums|
    requires |nums| < 10
    ensures containsDuplicate ==> exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    var windowSet: set<int> := {};
    if k == 0 {
        return false;
    }

    for i: nat := 0 to |nums| 
        invariant 1 <= k <= |nums|
        // invariant windowSetValid(nums, k, i, windowSet)
        invariant i < k ==> forall x :: x in windowSet ==> x in nums[0..i] 
        invariant i >= k ==> forall x :: x in windowSet ==> x in nums[i-k..i]
        // invariant if i < k then forall x :: x in windowSet ==> x in nums[0..i] else forall x :: x in windowSet ==> x in nums[i-k..i]

    {
        if nums[i] in windowSet {
            return true;
        }
        windowSet := if i >= k then (windowSet -{nums[i-k]}) + {nums[i]} else windowSet + {nums[i]};
    }
    return false;
}

predicate windowSetValid(nums: seq<int>, k: nat, i: nat, windowSet: set<int>) 
    requires 0 <= i <= |nums|
    requires 0 < k <= |nums|
{
    if i < k then forall x :: x in windowSet ==> x in nums[0..i]
    else forall x :: x in windowSet ==> x in nums[i-k..i]
}

function cd(nums: seq<int>, k: nat, i: nat, windowSet: set<int>): bool
    requires 0 <= i <= |nums|
    requires 0 < k <= |nums|
    requires windowSetValid(nums, k, i, windowSet)
    ensures cd(nums, k, i, windowSet) ==> exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
    decreases |nums| - i
{
    if i == |nums| then false
    else if nums[i] in windowSet then windowSetValidIsSufficient(nums, k, i, windowSet); true
    else if i < k then cd(nums, k, i+1, windowSet + {nums[i]})
    else cd(nums, k, i + 1, (windowSet - {nums[i-k]}) + {nums[i]})
}

lemma windowSetValidIsSufficient(nums: seq<int>, k: nat, i: nat, windowSet:set<int>)  
    requires 0 <= i < |nums|
    requires 0 < k <= |nums|
    requires windowSetValid(nums, k, i, windowSet)
    requires nums[i] in windowSet
    ensures exists i,j :: 0 <= i < j < |nums| && j-i <= k && nums[i] == nums[j]
{
    if i < k {
        assert nums[i] in windowSet;
        assert forall x :: x in windowSet ==> x in nums[0..i];
    }else{
        assert nums[i] in windowSet;
        assert forall x :: x in windowSet ==> x in nums[i-k..i];
    }
}