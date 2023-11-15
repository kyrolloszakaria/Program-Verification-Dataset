/*
function maximumWealth(accounts: number[][]): number {
    let richest = 0;
    for(let i = 0; i < accounts.length; i++) {
        let wealth = 0;
        for(let k = 0; k < accounts[i].length; k++ ) {
            wealth += accounts[i][k];
        }
        if(wealth > richest) {
            richest = wealth;
        }
    }
    return richest;
};
*/

function sumRow(row: seq<int>): int 
    ensures |row| == 0 ==> sumRow(row) == 0
    ensures |row| != 0 ==> sumRow(row) == row[0] + sumRow(row[1..])
{
    if |row| == 0 then 0 else row[0] + sumRow(row[1..])
}


function method sumRowTail(row: seq<int>): int 
    ensures |row| == 0 ==> sumRowTail(row) == 0
    ensures |row| > 0 ==> sumRowTail(row) == sumRowTail(row[..(|row|-1)]) + row[|row|-1]
{
    if |row| == 0 then 0 else sumRowTail(row[..(|row|-1)]) + row[|row| - 1]
}

function sumRowPartial(row: seq<int>, start: nat, end: nat): int 
    requires 0 <= start <= end <= |row|
    requires 0 <= end <= |row|
    ensures sumRowPartial(row, start, end) == sumRow(row[start..end])
    decreases end-start
{
    if start == end then 0 else row[start] + sumRowPartial(row, start+1, end)
}

method sumRowTests() {
    var example := [1,2,3,4];
    assert sumRow(example) == 10;
    assert sumRowPartial(example, 0, |example|) == 10;
    assert sumRow([]) == 0;
    assert sumRowTail([]) == 0;

    assert sumRowPartial([],0,0) == 0;
    assert sumRowPartial(example,0,0) == 0;

    assert sumRowTail(example[0..1]) == 1;
    assert sumRow(example[0..1]) == 1;
    assert sumRowPartial(example,0,1) == 1;

    assert sumRowTail(example[0..2]) == 3;
    assert sumRow(example[0..2]) == 3;
    assert sumRowPartial(example,0,2) == 3;

    assert sumRowTail(example[0..3]) == 6;
    assert sumRow(example[0..3]) == 6;
    assert sumRowPartial(example,0,3) == 6;

    assert sumRowTail(example[0..4]) == 10;
    assert sumRow(example[0..4]) == 10;
    assert sumRowPartial(example,0,4) == 10;
}
/* by method {
    var x := row[start];
    for i: nat := start to end 
        invariant x == sumRow(row[start..i])
    {
        x := x + row[i];
    }
    return x;
}
*/

predicate isMax(accounts: seq<seq<int>>, end: int,  richest: int)
    requires 0 <= end <= |accounts|
{
    forall x :: 0 <= x < end ==> richest >= sumRowTail(accounts[x])
}

method maximumWealth(accounts: seq<seq<int>>) returns (richest: int) 
    ensures isMax(accounts, |accounts|, richest)
{
    if |accounts| == 0 {
        return 0;
    }
    richest := 0;
    var i := 0;
    while i < |accounts| 
        invariant 0 <= i <= |accounts|
        invariant isMax(accounts, i, richest)
    {
        var wealth := sumRowTail(accounts[i]);
        // var wealth := simpleSum(accounts[i]);
        if(wealth >= richest) {
            richest := wealth;
        }
        i := i + 1;
    }
    assert i == |accounts|;
}

/** Original proof */
// method simpleSum(rows: seq<int>) returns (sum: int)
//     // ensures sum == sumRowTail(rows)
//  {
//     sum := 0;
//     if |rows| == 0 {
//         return 0;
//     }
//     var i := 0;
//     ghost var rowSlice := rows[..i];
//     while i < |rows|
//         invariant |rows| > 0 
//         invariant 0 <= i <= |rows|
//         invariant rowSlice == rows[..i]
//         invariant sum == sumRowTail(rowSlice)
//         decreases |rows|-i
//     {
//         ghost var oldsum := sum;
//         ghost var oldslice := rowSlice;

//         assert oldslice == rows[..i];
//         assert oldsum == sumRowTail(rowSlice);

//         sum := sum + rows[i];
//         assert sum == oldsum + rows[i];
//         i := i + 1;
//         rowSlice := rows[..i];

//         assert rows[..i] == rows[..(i-1)] + [rows[i-1]];
//         calc {
//             sumRowTail(rowSlice);
//             ==
//             sumRowTail(rowSlice[..(|rowSlice|-1)]) + rowSlice[|rowSlice|-1];
//             ==
//             sumRowTail(oldslice)+rows[i-1];
//             ==
//             oldsum + rows[i-1];
//             ==
//             sum;
//         }
//     }
// }

method simpleSum(rows: seq<int>) returns (sum: int)
    ensures sum == sumRowTail(rows)
 {
    sum := 0;
    if |rows| == 0 {
        return 0;
    }
    var i := 0;
    ghost var rowSlice := rows[..i];
    while i < |rows|
        invariant |rows| > 0 
        invariant 0 <= i <= |rows|
        invariant rowSlice == rows[..i]
        invariant sum == sumRowTail(rowSlice)
        decreases |rows|-i
    {
        ghost var oldsum := sum;
        sum := sum + rows[i];
        i := i + 1;
        rowSlice := rows[..i];

        assert rows[..i] == rows[..(i-1)] + [rows[i-1]];
        calc {
            sumRowTail(rowSlice);
            ==
            sumRowTail(rowSlice[..(|rowSlice|-1)]) + rowSlice[|rowSlice|-1];
            ==
            sumRowTail(rows[..(i-1)])+rows[i-1];
            ==
            oldsum + rows[i-1];
            ==
            sum;
        }
    }
    assert rowSlice == rows;
}