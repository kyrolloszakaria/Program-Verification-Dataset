

method matrixAdd(left: array2<real>, right: array2<real>, m: nat, n: nat) returns (result: array2<real>)
    requires m > 0 && n > 0
    requires left.Length0 == right.Length0 && left.Length0 == m && left.Length1 == right.Length1 && left.Length1 == n
    ensures result.Length0 == left.Length0 && result.Length1 == left.Length1
    ensures forall i, j :: 0 <= i < m && 0 <= j < n ==> result[i,j] == left[i,j] + right[i,j]
{
    result := new real[m,n];
    for i := 0 to m
    // var i := 0;
    // while i < m
        invariant 0 <= i <= m
        invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j];
    {
        for j := 0 to n
        // var j := 0;
        // while j < n
            invariant 0 <= j <= n
            invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j];
            invariant forall x :: 0 <= x < j  <= n ==> result[i,x] == left[i,x] + right[i,x]
        {
            result[i,j] := left[i,j] + right[i,j];
            // j := j + 1;
        }
        // i := i + 1;
    }
}

// twostate function ftranspose(matrix: array2<real>): array2<real> 
//     reads matrix
//     ensures ftranspose(matrix).Length0 == matrix.Length1 && ftranspose(matrix).Length1 == matrix.Length0
//     ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> ftranspose(matrix)[i,j] == matrix[j,i]
// {
//     new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0)
// }

method transpose(matrix: array2<real>) returns (result: array2<real>)
    ensures result.Length0 == matrix.Length1 && result.Length1 == matrix.Length0
    ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
{
    result := new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0);
    assert result.Length0 == matrix.Length1;
    assert result.Length1 == matrix.Length0;
}

ghost method transpose2(matrix: array2<real>) returns (result: array2<real>)
    ensures result.Length0 == matrix.Length1 && result.Length1 == matrix.Length0
    ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
{
    result := new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0);
    assert result.Length0 == matrix.Length1;
    assert result.Length1 == matrix.Length0;
}
// for i := 0 to matrix.Length1
//     invariant 0 <= i <= matrix.Length1
//     invariant forall x, j :: 0 <= x < i <= matrix.Length1 <= result.Length0 && 0 <= j < matrix.Length0 <= result.Length1 ==> result[i,j] == matrix[j,i]

// {
//     for j := 0 to matrix.Length0 
//         invariant 0 <= j <= matrix.Length0
//         invariant forall x, j :: 0 <= x < i && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
//         invariant forall x :: 0 <= x < j <= matrix.Length0 ==> result[i,x] == matrix[x, i]

//     {
//         result[i,j] := matrix[j,i];
//     }
// }


datatype Matrix = Matrice(vals: seq<seq<real>>, rows: nat, columns: nat)

predicate isMatrix(mat: Matrix) {
    mat.rows >= 1 && mat.columns >= 1 && |mat.vals| == mat.rows && forall i :: 0 <= i < mat.rows ==> |mat.vals[i]| == mat.columns
}

function method seqTranspose(mat: Matrix): Matrix
    requires isMatrix(mat)
    ensures isMatrix(seqTranspose(mat))
    ensures seqTranspose(mat).columns == mat.rows
    ensures seqTranspose(mat).rows == mat.columns
//     ensures seqTranpose(matrix).Length0 == matrix.Length1 && ftranspose(matrix).Length1 == matrix.Length0
    ensures forall i, j :: 0 <= i < mat.columns && 0 <= j < mat.rows ==> seqTranspose(mat).vals[i][j] == mat.vals[j][i]
{
    Matrice(seq(mat.columns, i requires 0 <= i < mat.columns => seq(mat.rows, j requires 0 <= j < mat.rows => mat.vals[j][i])), mat.columns, mat.rows)
}

function method matAdd(left: Matrix, right: Matrix): Matrix
    requires isMatrix(left) && isMatrix(right)
    requires left.rows == right.rows
    requires left.columns == right.columns
    ensures isMatrix(matAdd(left,right))
    ensures matAdd(left,right).rows == left.rows && matAdd(left, right).columns == left.columns
    ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matAdd(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
{
    Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(left.columns, j requires 0 <= j < left.columns => left.vals[i][j] + right.vals[i][j])), left.rows, left.columns)
}

function method Sum(vals: seq<real>): real
{
    if |vals| == 0 then 0.0 else vals[0] + Sum(vals[1..])
}

function method matMul(left: Matrix, right: Matrix): Matrix
    requires isMatrix(left) && isMatrix(right)
    requires left.columns == right.rows
    ensures isMatrix(matMul(left,right))
    ensures matMul(left,right).rows == left.rows && matMul(left, right).columns == right.columns
    // ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matMul(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
{
    Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(right.columns, j requires 0 <= j < right.columns => Sum(seq(left.columns, k requires 0 <= k < left.columns => left.vals[i][k]*right.vals[k][j])))), left.rows, right.columns)
}


lemma matQ(mat1: Matrix, mat2: Matrix) 
    requires isMatrix(mat1)
    requires isMatrix(mat2)
    requires mat2 == seqTranspose(seqTranspose(mat1))
    requires mat2.columns == mat1.columns
    requires mat2.rows == mat1.rows
    requires |mat1.vals| == |mat2.vals|
    requires forall i :: 0 <= i < |mat1.vals| ==> |mat1.vals[i]| == |mat2.vals[i]| == mat1.columns == mat2.columns
    requires forall i,j :: 0 <= i < mat1.rows <= mat2.columns && 0 <= j < mat1.columns <= mat2.columns ==> mat2.vals[i][j] == seqTranspose(seqTranspose(mat1)).vals[i][j]
    ensures forall i :: 0 <= i < |mat1.vals| ==> mat1.vals[i] == mat2.vals[i]
{

}

lemma matTranspose(mat: Matrix) 
    requires isMatrix(mat)
    ensures seqTranspose(seqTranspose(mat)) == mat
{
    // calc {
    //     seqTranspose(mat).columns == mat.rows && seqTranspose(mat).rows == mat.columns;
    //     ==>
    //     seqTranspose(seqTranspose(mat)).columns == mat.columns && seqTranspose(seqTranspose(mat)).rows == mat.rows;
    // }
    // assert seqTranspose(seqTranspose(mat)).columns == mat.columns;
    // assert seqTranspose(seqTranspose(mat)).rows == mat.rows;

    // matQ(mat, seqTranspose(seqTranspose(mat)));
    assert forall i :: 0 <= i < |mat.vals| ==> mat.vals[i] == seqTranspose(seqTranspose(mat)).vals[i];
    // assert seqTranspose(seqTranspose(mat)).vals == mat.vals;
}

lemma seqEqual<T>(left: seq<seq<T>>, right: seq<seq<T>>, rows: nat, columns: nat)
    requires |left| == |right| == rows
    requires forall i :: 0 <= i < rows ==> |left[i]| == |right[i]| == columns
    //if all in one row i are equal then the rows are equal and if all rows are equal then all 
    requires forall i, j :: 0 <= i < rows && 0 <= j < columns ==> left[i][j] == right[i][j]
    ensures forall i :: 0 <= i < rows ==> left[i] == right[i]
    // ensures left == right
{

}

method Test() {
    var foo : Matrix := Matrice([[1.0,2.0],[3.0,4.0]],2,2);
    var boo : Matrix := seqTranspose(foo);
}