function method satPairs(nums: seq<nat>, k: nat, a: nat, b: nat): bool
    requires k > 0
    requires a <= b < |nums| 
{
    nums[a] == nums[b] && (a*b) % k == 0
}

function matchPairsHelper(nums: seq<nat>, k: nat, bound: int): set<(int, int)>
  requires k > 0
  requires bound <= |nums|
{
    set x,y | 0 <= x < bound && x < y < |nums| && satPairs(nums, k, x, y) :: (x,y)
}

function matchPairs(nums: seq<nat>, k: nat): set<(int, int)>
  requires k > 0
{
  matchPairsHelper(nums, k, |nums|)
}

function innerMatchPairsHelper(nums: seq<nat>, k: nat, outer: int, inner_bound: int): set<(int, int)>
  requires k > 0
  requires inner_bound <= |nums|
{
    set y | 0 <= outer < y < inner_bound && satPairs(nums, k, outer, y) :: (outer,y)
}

method countPairs(nums: seq<nat>, k: nat) returns (count: nat) 
    requires k > 0
    requires |nums| >= 2
    ensures count == |matchPairs(nums, k)|
{
  count := 0;
  for i : nat := 0 to |nums|
    invariant count == |matchPairsHelper(nums, k, i)|
  {
    for j : nat := i+1 to |nums|
      invariant count == |matchPairsHelper(nums, k, i)| + |innerMatchPairsHelper(nums, k, i, j)|
    {
      assert innerMatchPairsHelper(nums, k, i, j+1) ==
        (if satPairs(nums, k, i, j) then {(i, j)} else {}) + innerMatchPairsHelper(nums, k, i, j);
      if satPairs(nums, k, i, j) {
        count := count + 1;
      } 
    }
    assert matchPairsHelper(nums, k, i+1) == matchPairsHelper(nums, k, i) + innerMatchPairsHelper(nums, k, i, |nums|);
  }
}