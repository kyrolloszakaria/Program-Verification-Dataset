/*
https://leetcode.com/problems/two-sum/
function twoSum(nums: number[], target: number): number[] {
    const n = nums.length;
    for(let i = 0; i < n; i++) {
        for(let k = i+1; k < n; k++) {
            if(nums[i] + nums[k] == target) return [i,k]; 
        }
    }
};
*/
predicate summingPair(i: nat, j: nat, nums: seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    pair := (0,0);
    var i: nat := 0;
    while i < |nums| 
        invariant i <= |nums|
        invariant forall z: nat, j: nat :: 0 <= z < i  && z+1 <= j < |nums| ==> !summingPair(z, j, nums, target)
    {
        var k: nat := i + 1;
        while k < |nums| 
            invariant i + 1 <= k <= |nums|
            // invariant forall q: nat :: i+1 <= q < k < |nums| ==> !summingPair(i,q, nums, target) //this fails to verify
            invariant forall q: nat :: i+1 <= q < k <= |nums| ==> !summingPair(i,q, nums, target) //this verifies
        {
            // assert i < k < |nums|;
            if nums[i] + nums[k] == target {
                pair := (i,k);
                return pair;
            }
            k := k + 1;
        }
        i := i + 1;
    }
}

/*
function twoSum(nums: number[], target: number): number[] {
    const n = nums.length;
    const visitedMap: Map<number, number> = new Map();
    for(let i = 0; i < n; i++) {
        if(visitedMap.has(target-nums[i])) {
            return [visitedMap.get(target-nums[i]), i];
        }
        visitedMap.set(nums[i], i);
    }
};
*/

lemma MergeMapSets<T>(left: map<T, nat>, right: map<T,nat>, k: nat)
    requires (forall l :: l in left.Values ==> l < k-1 ) && (forall r :: r in right.Values ==> r < k)
    ensures forall x :: x in (left+right).Values ==> x < k
{
    var result := left + right;
    forall x | x in result 
        ensures result[x] < k
    {
        assert x in left || x in right;
        if x in left {
            assert left[x] in left.Values;
            assert left[x] < k;
        }
        if x in right {
            assert right[x] in right.Values;
            assert right[x] < k;
        }

        assert result[x] < k;
    }
}

predicate InjectiveMap<T,U>(f: map<T, U>)
{
    forall x, y :: x in f && y in f && x != y ==> f[x] != f[y]
}

predicate mapsToNum(amap: map<int, nat>, nums: seq<int>, anum: int)
    requires anum in amap
{
    amap[anum] < |nums| && nums[amap[anum]] == anum
}

function lessThanI(i: nat): set<nat>
{
    set x: nat | 0 <= x < i
}

method twoSumBetter(nums: seq<int>, target: int) returns (pair: (nat,nat))
    requires exists i:nat,j:nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target)
{
    // ghost var oldMap := visitedMap;
    var visitedMap: map<int, nat> := map[];
    // for i: nat := 0 to |nums|
    var i: nat := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall j :: 0 <= j < i < |nums| ==> nums[j] in visitedMap
        // invariant InjectiveMap(visitedMap);
        invariant forall x :: x in visitedMap ==> x in nums[0..i]
        invariant forall x :: x in visitedMap.Values ==> x < i
        invariant forall nj :: nj in visitedMap ==> mapsToNum(visitedMap, nums, nj)
        invariant forall x,y :: x in visitedMap && y in visitedMap ==> !summingPair(visitedMap[x], visitedMap[y], nums, target)
        // invariant forall z :: z < i ==> forall k :: k < z ==> !summingPair(k,z, nums, target)
    {
        // assert forall k:nat :: k in oldMap.Values ==> k in lessThanI(i+1);
        if (target-nums[i]) in visitedMap {
            // assert nums[i] !in visitedMap;
            assert target-nums[i] in nums[0..i];
            var j := visitedMap[target-nums[i]];
            assert j < i < |nums|;
            assert exists je :: 0 <= je < i && nums[je] == target-nums[i];
            // assert exists je :: 0 <= je < i && nums[je] == target-nums[i] && visitedMap[target-nums[i]] == je;
            // assert target-nums[i] != nums[i];
            // assert mapsToNum(visitedMap, nums, target-nums[i]);
            assert nums[j] == target-nums[i];
            assert nums[j] + nums[i] == target;
            assert j < |nums|;
            pair := (j,i);
            assert 0 <= pair.0 < |nums|;
            assert 0 <= pair.1 < |nums|;
            assert pair.0 != pair.1;
            // assert j != i;
            return pair;
        }
        MergeMapSets(visitedMap, map[nums[i] := i], i+1);
        visitedMap := visitedMap + map[nums[i] := i];
        i := i + 1;
        assert forall x :: x in visitedMap.Values ==> x < i;
        // assert forall k :: k in map[nums[i] := i].Values ==> k < i;
        // assert visitedMap == oldMap + map[nums[i]:= i];
        // assert visitedMap.Values == oldMap.Values + (map[nums[i]:= i]).Values;
        // assert forall k:nat :: k in visitedMap.Values ==> 0 <= k < |nums|;
        // assert visitedMap[nums[i]] == i;
        // assert mapsToNum(visitedMap, nums, nums[i]);
    }
}

/*

    // invariant !summingPair(pair.0, pair.1, nums, target) ==> pair == (0,0)
    // invariant exists j: nat :: (i < j < |nums| && summingPair(i, j, nums, target) ==> pair == (i,j))
    // invariant exists k :: (i < k <|nums| && summingPair(i, k, nums, target) ==> pair.0 == i && pair.1 == k)

    // invariant k < |nums| ==> summingPair(i,k, nums, target) ==> pair.0 == i && pair.1 == k
    // invariant forall z: nat :: z < i ==> forall j :: z+1 <= j < |nums| ==> !summingPair(z, j, nums, target)

    // assert k == |nums|;
    // assert forall p :: i + 1 <= p < k <= |nums| ==> !summingPair(i,p, nums, target);

    // assert i == |nums|;
    // assert !(exists k :: (i < k <|nums| && nums[i] + nums[k] == target ==> pair.0 == i && pair.1 == k));
    // assert pair == (0,0);
    // assert forall i:nat,j:nat :: i < j < |nums| && !summingPair(i,j, nums, target);
    // assert nums[pair.0] + nums[pair.1] != target;

    // assert 0 <= i < |nums|;
    // assert 1 <= k < |nums|;
    // assert nums[pair.0] + nums[pair.1] == target;
*/