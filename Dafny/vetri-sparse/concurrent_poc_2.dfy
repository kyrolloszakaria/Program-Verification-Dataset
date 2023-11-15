type Process(==)
datatype PState = Waiting | WaitingToUpdateResult | UpdatingResult

class MatrixVectorMultiplier
{
    var nextRowIndex: nat
    var curRowIndex: nat

    var P: set<Process>

    var ps: map<Process, PState>
    var r: map<Process, nat>

    var M: array2<int>
    var x: array<int>
    var y: array<int>

    var numRows: nat

    var rowsLeft: nat

    predicate Valid 
        reads this
    {
        P == ps.Keys == r.Keys &&
        M.Length0 == y.Length &&
        M.Length1 == x.Length &&
        curRowIndex <= nextRowIndex &&
        (forall p :: (p in P && ps[p] != Waiting) ==> curRowIndex <= r[p] < nextRowIndex) &&
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
        rowsLeft := M_.Length0;
    }

    function dot_product(arr1: seq<int>, arr2: seq<int>) : (r: int)
        requires |arr1| == |arr2|
        ensures r == dot_product(arr1[1..], arr2[1..]) + arr1[0] * arr2[0]
    {
        if |arr1| == 0 then
            0
        else
            dot_product(arr1[1..], arr2[1..]) + arr1[0] * arr2[0]
    }

    method DotProduct(arr1: array<int>, arr2: array<int>) returns (result: int)
        requires arr1.Length == arr2.Length
        ensures result == dot_product(arr1[..], arr2[..])
    {
        result := 0;
        var i: int := 0;
        while i < arr1.Length
            invariant 0 <= i <= arr1.Length
            invariant result + dot_product(arr1[i..], arr2[i..]) == dot_product(arr1[..], arr2[..])
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
        requires Valid() && p in P && ps[p] == Waiting && nextRowIndex < numRows
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
        ps := ps[p := UpdatingResult];
    }

    method UpdateResultandLeave(p: Process)
        requires Valid() && p in P && ps[p] == UpdatingResult
        requires curRowIndex < M.Length0
        modifies this, y
        ensures Valid()
    {
        var curRow: array<int> := GetSpecifiedRow(M, curRowIndex);
        y[curRowIndex] := DotProduct(curRow, x);
        curRowIndex := curRowIndex + 1;
        ps := ps[p := Waiting];
    }

}

method Run(processes: set<Process>, M: array2<int>, x: array<int>) returns (y: array<int>)
    requires processes != {}
    requires x.Length > 0
    requires M.Length0 > 0
    requires M.Length1 == x.Length
    ensures M.Length0 == y.Length
    decreases *
{
    var mv := new MatrixVectorMultiplier(processes, M, x);
    while true
        invariant mv.Valid()
        decreases *
    {
        if mv.curRowIndex == mv.numRows || mv.curRowIndex >= M.Length0 {break;}
        var p :| p in mv.P && (mv.ps[p] == WaitingToUpdateResult ==> mv.r[p] == mv.curRowIndex);
        match mv.ps[p] {
            case Waiting => if mv.nextRowIndex < mv.numRows {
                    mv.RequestUpdateResult(p);
                }
            case WaitingToUpdateResult => 
                if mv.r[p] == mv.curRowIndex {
                    mv.EnterUpdateResult(p);
                }
            case UpdatingResult => mv.UpdateResultandLeave(p);
        }
    }
    y := mv.y;
}





//____________________________________________________________________
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

