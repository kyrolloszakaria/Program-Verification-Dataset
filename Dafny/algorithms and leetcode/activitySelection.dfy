

method recursiveActivitySelector(start: seq<nat>, finish: seq<nat>, k: nat, n: nat) returns (a: set<nat>)
    requires |start| == n
    requires |finish| == n
    requires 1 < k <= n
    requires forall i :: 0 <= i < n ==> start[i] < finish[i]
    requires forall i :: 0 <= i < n-1 ==> finish[i] <= finish[i+1]
    decreases n-k;
{
    var m := k+1;
    while m <= n && start[m-1] < finish[k-1] 
    {
        m := m + 1;
    }
    if m <= n {
        var res := recursiveActivitySelector(start, finish, k+1, n);
        return {m} + res;
    }else{
        return {};
    }
}

function substructure(start: seq<nat>, finish: seq<nat>, k: nat): set<nat>
    requires |finish| >= 1
    requires |start| == |finish|
    requires 0 <= k < |finish|
    requires forall i :: 0 <= i < |finish| ==> start[i] < finish[i]
    requires forall i,j :: 0 <= i <= j < |finish| ==> i <= j ==> finish[i] <= finish[j]
{
    set x | 0 <= x < |finish| && start[x] >= finish[k]
}

predicate activitySet(start: seq<nat>, finish: seq<nat>, compatible: set<nat>) 
    requires |finish| >= 1
    requires |start| == |finish|
    requires forall i :: i in compatible ==> 0 < i <= |finish|
    requires forall i :: 0 <= i < |finish| ==> start[i] < finish[i]
    requires forall i,j :: 0 <= i <= j < |finish| ==> i <= j ==> finish[i] <= finish[j]
{
    forall i, j :: i in compatible && j in compatible && finish[i-1] != finish[j-1] && finish[i-1] < finish[j-1] ==> start[i-1] < start[j-1] && start[j-1] > finish[i-1]
}

method Test() {
    /*
    i  1 2 3 4 5 6 7 8 9 10 11 
    si 1 3 0 5 3 5 6 8 8 2 12 
    fi 4 5 6 7 9 9 10 11 12 14 16
    */
    var start :=  [1,3,0,5,3,5,6,8,8,2,12];
    var finish := [4,5,6,7,9,9,10,11,12,14,16];
    assert activitySet(start, finish, {1,4,8,11});
}

method activitySelector(start: seq<nat>, finish: seq<nat>) returns (A: set<nat>)
    requires |finish| >= 1
    requires |start| == |finish|
    requires forall i :: 0 <= i < |finish| ==> start[i] < finish[i]
    requires forall i,j :: 0 <= i <= j < |finish| ==> i <= j ==> finish[i] <= finish[j]
    ensures forall x :: x in A ==> 1 <= x <= |finish|
    // ensures forall x,y :: x in A && y in A && x < y ==> finish[x-1] < start[y-1]
    ensures activitySet(start, finish, A);
{
    var n := |finish|;
    A := {1};
    var k := 1;
    var m := 2;
    while m <= n 
        invariant k < m <= n+1
        invariant 2 <= m <= n+1
        invariant forall x :: x in A ==> 1 <= x <= |finish| && finish[k-1] >= finish[x-1]
        invariant activitySet(start, finish, A);
    {
        if start[m-1] >= finish[k-1] {
            assert 2 <= m <= n;
            assert forall x :: x in A ==> 1 <= x <= |finish| && finish[k-1] >= finish[x-1] ==> forall x :: x in A ==> start[m-1] >= finish[x];
            // assert activitySet(start, finish, A+{m});
            A := A + {m};
            k := m;
        }
        m := m + 1;
    }
    return A;
}