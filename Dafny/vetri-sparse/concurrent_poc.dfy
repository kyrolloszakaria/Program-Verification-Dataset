datatype Process = Process(value: int)
datatype PState = Waiting | WaitingToUpdateResult | UpdatingResult | Done
// datatype PState = Waiting | WaitingToUpdateResult | UpdatingResult(idx : nat) | Done

class MatrixVectorMultiplier
{
    var nextRowIndex: nat
    var curRowIndex: nat // curRowIndex can be arbirtaty chosen by at each moment at the time 

    var P: set<Process>

    var ps: map<Process, PState>
    var r: map<Process, nat>

    var M: array2<int>
    var x: array<int>
    var y: array<int>

    var numRows: nat

    predicate Valid 
        reads this
    {
        P == ps.Keys == r.Keys &&
        M.Length0 == y.Length &&
        M.Length1 == x.Length &&
        curRowIndex <= nextRowIndex &&
        forall p :: p in P && ps[p] != Waiting ==> curRowIndex <= r[p] < nextRowIndex &&
        (forall p,q ::
            p in P && q in P && p != q && ps[p] != Waiting && ps[q] != Waiting
            ==> r[p] != r[q]) &&
        forall p :: p in P && ps[p] == UpdatingResult ==> r[p] == curRowIndex
    }

    lemma MutualExclusion(p: Process, q: Process)
        requires Valid() && p in P && q in P
        requires ps[p] == UpdatingResult && ps[q] == UpdatingResult
        ensures p == q
    {
    }

    constructor (processes: set<Process>, M_: array2<int>, x_: array<int>)
        requires M_.Length0 > 0
        requires x_.Length > 0
        requires M_.Length1 == x_.Length
        ensures Valid()
        ensures P == processes
    {
        P := processes;
        nextRowIndex, curRowIndex := 0, 0;
        ps := map p | p in processes :: Waiting;
        r := map p | p in processes :: 0;
        M := M_;
        x := x_;
        numRows := M_.Length0;
        y := new int[M_.Length0];
    }

    // function dot_product(arr1: seq<int>, arr2: seq<int>) : (r: int)
    //     requires |arr1| == |arr2|
    //     ensures r == dot_product(arr1[1..], arr2[1..]) + arr1[0] * arr2[0]
    // {
    //     if |arr1| == 0 then
    //         0
    //     else
    //         dot_product(arr1[1..], arr2[1..]) + arr1[0] * arr2[0]
    // }

    method DotProduct(arr1: array<int>, arr2: array<int>) returns (result: int)
        requires arr1.Length == arr2.Length
        // ensures result == dot_product(arr1[..], arr2[..])
    {
        result := 0;
        var i: int := 0;
        while i < arr1.Length
            invariant 0 <= i <= arr1.Length
            // invariant result + dot_product(arr1[i..], arr2[i..]) == dot_product(arr1[..], arr2[..])
        {
            result := result + arr1[i] * arr2[i];
            i := i + 1;
        }
    }

    method GetSpecifiedRow(twoDimArray: array2<int>, rowIndex: nat) returns (specifiedRow: array<int>)
        requires rowIndex < twoDimArray.Length0
        ensures specifiedRow.Length == twoDimArray.Length1
        ensures forall i :: 0 <= i < twoDimArray.Length1 ==> specifiedRow[i] == twoDimArray[rowIndex, i]
    {
        var numRows := twoDimArray.Length0;
        var numCols := twoDimArray.Length1;
        
        specifiedRow := new int[numCols];

        for i := 0 to numCols
            invariant 0 <= i <= numCols
            invariant forall j :: 0 <= j < i ==> specifiedRow[j] == twoDimArray[rowIndex, j]
        {
            specifiedRow[i] := twoDimArray[rowIndex, i];
        }
    }


    method RequestUpdateResult(p: Process)
        requires Valid() && p in P && ps[p] == Waiting
        modifies this
        ensures Valid()
    {
        r, nextRowIndex := r[p := nextRowIndex], nextRowIndex + 1;
        ps := ps[p := WaitingToUpdateResult];

    }

    method EnterUpdateResult(p: Process)
        requires Valid() && p in P && ps[p] == WaitingToUpdateResult
        modifies this
        ensures Valid()
    {
        if r[p] == curRowIndex
        {
            ps := ps[p := UpdatingResult];
        }
    }

    function hasFalse(arr: seq<bool>) : (r: bool)
        ensures r == (exists i :: 0 <= i < |arr| && !arr[i])
    {
        if |arr| == 0 then
            false
        else
            !arr[0] || hasFalse(arr[1..])
    }

    method arrHasFalse(arr: array<bool>) returns (result: bool)
        // ensures hasFalse(arr[..])
    {
        var i := 0;
        result := false;
        while i < arr.Length
            invariant 0 <= i <= arr.Length
            invariant !hasFalse(arr[..i])
        {
            if !arr[i] {
                result := true;
                return;
            }
            i := i + 1;
        }
    }

    method UpdateResultandLeave(p: Process)
        requires Valid() && p in P && ps[p] == UpdatingResult
        requires curRowIndex < M.Length0
        modifies this, y
        ensures Valid()
    {
        // add one value, increment idx in UpdatingResult(idx : nat) by one
        // invariant should be 
           // forall i :: y[i] == \sum_{0 < k < idx} M[i, k] * v[k]
        var curRow: array<int> := GetSpecifiedRow(M, curRowIndex);
        y[curRowIndex] := DotProduct(curRow, x);
        curRowIndex := curRowIndex + 1;
        ps := ps[p := Done];
    }

    method firstFalse(arr: array<bool>) returns (index: nat)
        ensures 0 <= index <= arr.Length
        ensures index == arr.Length ==> forall i :: 0 <= i < arr.Length ==> arr[i]
        ensures index < arr.Length ==> !arr[index]
    {
        index := 0;
        while (index < arr.Length)
            invariant 0 <= index <= arr.Length
            invariant forall i :: 0 <= i < index ==> arr[i]
        {
            if (!arr[index]) {
                return;
            }
            index := index + 1;
        }
    }

}

method CreateProcessesSet(size: nat) returns (processes: set<Process>)
    ensures |processes| == size
{
    processes := {};
    var i: int := 0;
    while i < size
        invariant |processes| == i
        invariant i <= size
    {
        var newProcess := Process(i);
        processes := processes + {newProcess};
        i := i + 1;
    }
}

method Run(M: array2<int>, x: array<int>) returns (y: array<int>)
    requires x.Length > 0
    requires M.Length1 == x.Length
    decreases *
{
    var processes := CreateProcessesSet(M.Length0);
    var mv := new MatrixVectorMultiplier(processes, M, x);
    while true
        invariant mv.Valid()
        decreases *
    {
        if mv.curRowIndex == mv.numRows {break;}
        var p :| p in mv.P;
        match mv.ps[p] {
            case Waiting => mv.RequestUpdateResult(p);
            case WaitingToUpdateResult => mv.EnterUpdateResult(p);
            case UpdatingResult => mv.UpdateResultandLeave(p);
            case Done => {}
        }
    }
}

method multiply(M: array2<int>, x: array<int>) returns (y: array<int>)
    requires M.Length0 > 0
    requires M.Length1 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
{
    var N := M.Length0;
    var N2 := M.Length1;
    y := new int[N];
    var n: nat := 0;
    while n < N
        invariant n <= y.Length
    {
        y[n] := 0;
        var k: nat := 0;
        while k < N2
            invariant k <= N2
        {
            y[n] := y[n] + M[n,k] * x[k];
            k := k + 1;
        }
        n := n + 1;
    } 
}

method Main() 
{
    var M: array2<int> := new int[3, 3];


    M[0,0] := 1;
    M[0,1] := 2;
    M[0,2] := 3;

    M[1,0] := 1;
    M[1,1] := 2;
    M[1,2] := 3;

    M[2,0] := 1;
    M[2,1] := 20;
    M[2,2] := 3;

    var x := new int[3];
    x[0] := 1;
    x[1] := -3;
    x[2] := 3;

    var y := multiply(M, x);
    for i := 0 to 3 {
        print "output: ", y[i], "\n";
    }
}

