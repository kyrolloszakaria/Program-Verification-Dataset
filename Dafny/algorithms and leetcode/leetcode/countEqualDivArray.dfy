// https://leetcode.com/problems/count-equal-and-divisible-pairs-in-an-array/
/*
function countPairs(nums: number[], k: number): number {
    let count = 0;
    for(let i = 0; i < nums.length-1; i++) {
        for(let j = i+1; j < nums.length; j++) {
            if(nums[i] == nums[j] && (i*j) % k == 0) {
                count++;
            }
        }
    }
    return count;
};
*/

function matchPairs(nums: seq<nat>, k: nat): nat 
    requires k > 0
{
    |set x,y | 0 <= x < y < |nums| && nums[x] == nums[y] && (x*y) % k == 0 :: (x,y)|
}

function method pairs(nums: seq<nat>, k: nat): set<(int, int)> 
    requires k > 0
{
    set x,y | 0 <= x < y < |nums| && nums[x] == nums[y] && (x*y) % k == 0 :: (x,y)
}

function method pairsI(nums: seq<nat>, k: nat, i: nat): set<(nat, nat)> 
    requires k > 0
    requires 0 <= i < |nums|
    ensures forall x,y :: 0 <= x < i && x <= y < |nums| && satPairs(nums, k, x, y) ==> (x,y) in pairsI(nums, k, i)
{
    set x: nat,y:nat | 0 <= x < i && x <= y < |nums| && satPairs(nums, k, x, y) :: (x,y)
}

// function method pairsIrec(nums: seq<nat>, k: nat, i: int): set<(nat, nat)> 
//     requires k > 0
//     requires -1 <= i < |nums|
//     ensures pairsIrec(nums, k, i) == (set x: nat, y:nat | 0 <= x < i && 0 <= y < |nums| && satPairs(nums, k, x, y) :: (x,y))  + set z: nat | 0 <= z  <= i && satPairs(nums, k, z, i) :: (i,z)
//     // ensures forall x,y :: 0 <= x < y < i && satPairs(nums, k, x, y) ==> (x,y) in pairsIrec(nums, k, i)
// {
//     if i == -1 then {} else pairsIrec(nums, k, i-1) + set x: nat | 0 <= x  <= i && satPairs(nums, k, x, i) :: (i,x)
// }



method Test2() {
    var test := [3,1,2,2,2,1,3];
    var pairs := pairsI(test, 2, 0);
    assert pairs == {};

}

function method satPairs(nums: seq<nat>, k: nat, a: nat, b: nat): bool
    requires k > 0
    requires a <= b < |nums| 
{
    nums[a] == nums[b] && (a*b) % k == 0
}

function countSeqPairs(nums: seq<nat>, k: nat, start: nat,  stop: nat): nat 
    requires k > 0
    requires start <= stop <= |nums|
    decreases |nums|-start, |nums|-stop
{
    if start > stop || stop >= |nums| || start >= |nums| then 0 else 
    if stop < |nums| then (if satPairs(nums, k, start, stop) then 1 + countSeqPairs(nums, k, start, stop+1) else countSeqPairs(nums, k, start, stop+1)) else countSeqPairs(nums, k, start+1, stop+2)

}

function countSeqSlice(nums: seq<nat>, k: nat, start: nat, stop: nat): nat 
    requires k > 0
    requires start <= stop <= |nums|
    decreases |nums| - stop
{
    if start > stop || stop >= |nums| then 0
    else if satPairs(nums, k, start, stop) then 1 + countSeqSlice(nums, k, start, stop+1) else countSeqSlice(nums, k, start, stop+1)
}

// function countSeqSlices(nums: seq<nat>, k: nat, begin: nat, end: nat): nat
//     requires k > 0
//     requires 0 <= begin < |nums|
//     requires 0 <= end <= |nums|
//     ensures countSeqSlices(nums, k, begin, end) == countSeqSlices(nums, k, begin+1, end) + countSeqSlice(nums, k, begin, |nums|) 
//     decreases end-begin
// {
//     if begin >= end || end <= 0 then 0 else countSeqSlices(nums, k, begin+1, end) + countSeqSlice(nums, k, begin, |nums|)    
// }


method countPairs(nums: seq<nat>, k: nat) returns (count: nat) 
    requires k > 0
    requires |nums| >= 2;
{
    count := 0;
    //ghost var cpairs: set<(nat, nat)> := {};
    for i : nat := 0 to |nums|-2 
        invariant count >= 0
        //invariant cpairs == pairsI(nums, k, i)
    {
        // ghost var occount := count;
        // ghost var increment := 0;
        for j : nat := i+1 to |nums|-1 
            invariant count >= 0
            // invariant count == occount + increment
            // invariant satPairs(nums, k, i, j) ==> increment == increment + 1 
            // invariant count == 0 || satPairs(nums, k, i, j) ==> count == count + 1
            //invariant cpairs == pairsI(nums, k, i) + set z: nat | i+1 <= z <= j && satPairs(nums, k, i, z) :: (i, z)
        {
            // ghost var currcount := count;
            // if nums[i] == nums[j] && (i*j)% k == 0 {
            if  i+1 <= j <= j && satPairs(nums, k, i, j) {
                // increment := increment + 1;
                //cpairs := {(i,j)}+cpairs;
                count := count + 1;
            }
        }
    }
}

// method Test() {
//     //                0 1 2 3 4 5 6
//     var something := [3,1,2,2,2,1,3];
//     var what := pairs(something, 2);
//     assert (0,6) in what;
//     assert (2,3) in what;
//     assert (2,4) in what;
//     assert (3,4) in what;

//     assert (0,4) !in what;
//     assert (0,0) !in what;
//     assert (0,1) !in what;
//     assert (0,2) !in what;
//     assert (0,3) !in what;
//     assert (0,5) !in what;
//     assert (2,6) !in what;
//     assert (1,0) !in what;
//     assert (1,1) !in what;
//     assert (1,2) !in what;
//     assert (1,3) !in what;
//     assert (1,4) !in what;
//     assert (1,5) !in what;
//     assert (1,6) !in what;
//     assert (2,1) !in what;
//     assert (2,2) !in what;
//     assert (2,5) !in what;
//     assert (2,6) !in what;

//     assert (3,0) !in what;
//     assert (3,1) !in what;
//     assert (3,2) !in what;
//     assert (3,3) !in what;
//     assert (3,5) !in what;
//     assert (3,6) !in what;

//     assert (4,0) !in what;
//     assert (4,1) !in what;
//     assert (4,2) !in what;
//     assert (4,3) !in what;
//     assert (4,4) !in what;
//     assert (4,5) !in what;
//     assert (4,6) !in what;

//     assert (5,0) !in what;
//     assert (5,1) !in what;
//     assert (5,2) !in what;
//     assert (5,3) !in what;
//     assert (5,4) !in what;
//     assert (5,5) !in what;
//     assert (5,6) !in what;

//     assert (6,0) !in what;
//     assert (6,1) !in what;
//     assert (6,2) !in what;
//     assert (6,3) !in what;
//     assert (6,4) !in what;
//     assert (6,5) !in what;
//     assert (6,6) !in what;
//     assert (7,0) !in what;
//     assert (7,1) !in what;
//     assert (7,2) !in what;
//     assert (7,3) !in what;
//     assert (7,4) !in what;
//     assert (7,5) !in what;
//     assert (7,6) !in what;
//     assert (7,7) !in what;

//     assert |what| == matchPairs(something,2);
//     // assert |what| == 4;
//     assert matchPairs(something, 2) == 4;
// }