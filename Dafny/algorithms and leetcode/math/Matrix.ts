
/** 

	CONVENTIONS:
	In the documentation I refer to Integer and Doubles but this is more to indicate intent
	because all f64s in Javascript, also referred as "f64", are 64 bit floating point variables.
**/
"use strict";
/**
	Provides a mathematical matrix object
	@class
	@constructor
	@param rows {Integer} f64 of rows in the matrix
	@param columns {Integer} f64 of columns in the matrix
	@param values {Double[][]} a multidimensional array with rows and column as specified by the other parameters
**/
class Matrix {	
	rows: i32;
	columns: i32;
	values: f64[][];
	constructor(values: f64[][], rows?: i32, columns?: i32 ) 
	{
		this.rows = rows || values.length;
		this.columns = columns || values[0].length;
		this.values = values;

	}



	/**
		Subtract one matrix from another
		@param {Matrix} that The term being subtracted
		@return {Matrix} The difference matrix
	**/
	subtract(that: Matrix): Matrix
	{
		if(this.rows == that.rows && this.columns == that.columns)
		{
			var newvalues: f64[][] = new Array(this.rows);
			for(var i =0; i < this.rows; i++) {
				newvalues[i] = [];
				for(var j = 0; j < this.columns; j++) {
					newvalues[i][j] = this.values[i][j]-that.values[i][j];
				}
				
			}
			return new Matrix(newvalues, this.rows, this.columns);
		}else{
			throw new Error("Matrix size mismatch; Addition is not defined.");
		}
	}

	/**
		Multiply one matrix by another
		@param {Matrix} that The matrix being multiplied 
		@return {Matrix} The product matrix
	**/
	multiply(that: Matrix): Matrix 
	{
		if(this.columns == that.rows)
		{
			var product: f64[][] = new Array(this.rows);
			for(var i=0; i < this.rows; i++) {
				product[i] = [];
				for(var j = 0; j < that.columns; j++) {
					product[i][j] =0;
				}
			}
			for(var k=0; k < this.columns; k++) {
				for(var i = 0; i < this.rows; i++) {
					for(var j =0; j < that.columns; j++) {
						product[i][j] += this.values[i][k]*that.values[k][j];
					}
				}
			}
			
			return new Matrix(product, this.rows, that.columns);
			
		}else{
			throw new Error("Matix size mismatch; Multiplication is not allowed.");
		}
	}

	/**
		Runs a naive Gaussian elimination on a Matrix or a Matrix and a sum vector.
		Given the form Ax = b; A is the matrix and b is the sum vector; x is the result
		@param sumvector {Matrix (Nx1 sized)} An N row, 1 column vector containing the sums. 
		@return {Matrix (Nx1 sized)} The answer
		
		
	**/

	naiveGaussian(sumcolumnvector: Matrix): Matrix {
		if(! (sumcolumnvector instanceof Matrix))
		{
			throw new Error("Parameter expects a Matrix");
		}

		if(this.rows != this.columns) {
			throw new Error("Matrix incorrectly sized; Must be NxN matrix");
		}
		
		if(this.rows != sumcolumnvector.rows)
		{
			throw new Error("Sum vector row count must match the row count of the coefficient matrix");
		}
		
		var newvalues: f64[][] = new Array(this.rows);
		for(var i =0; i < this.rows; i++)
		{
			newvalues[i] = this.values[i].slice(0);
		}
		var newsums = sumcolumnvector.transpose().values.slice(0); //Probably need to address how I want to reference things for this matrix...
		//console.log(newvalues+"");
		for(var k = 0; k < this.rows-1; k++) {
			for(var i = k+1; i < this.rows; i++) {
				var xmult = newvalues[i][k]/newvalues[k][k];
				//newvalues[i][k] = xmult;
				for(var j = k+1; j < this.rows; j++) {
					newvalues[i][j] = newvalues[i][j] - (xmult*newvalues[k][j]);
				}
				newsums[i] = newsums[i] - xmult*newsums[k];
			}
			
		}
		var solutions: f64[][] = new Array(this.rows);
		for(var i = this.rows-1; i >= 0; i--) {
			var sum = newsums[i];
			for(var j = i+1; j < this.rows; j++) {
				sum = sum - newvalues[i][j]*solutions[j];
			}
			solutions[i] = [sum/newvalues[i][i]];
		}
		return new Matrix(solutions, this.rows, 1);
		
		
	}

	/**
		Runs a Gaussian elimination with scaled partial pivoting on a a Matrix and a sum vector.
		Given the form Ax = b; A is the matrix and b is the sum vector; x is the result
		@param sumvector {Matrix (Nx1 sized)} An N row, 1 column vector containing the sums. 
		@return {Matrix (Nx1 sized)} The answer
		
		P. 267
	**/

	scaledPartialPivotGaussian(sumvector: Matrix): Matrix {
		if(! (sumvector instanceof Matrix))
		{
			throw new Error("Parameter expects a Matrix");
		}

		if(this.rows != this.columns) {
			throw new Error("Matrix incorrectly sized; Must be NxN matrix");
		}
		
		if(this.rows != sumvector.rows)
		{
			throw new Error("Sum vector row count must match the row count of the coefficient matrix");
		}
		var newvalues: f64[][] = new Array(this.rows);
		for(var i =0; i < this.rows; i++)
		{
			newvalues[i] = this.values[i].slice(0);
		}
		var newsums = sumvector.values.slice(0);
		//console.log(newvalues+"");
		//Setup for scale and index vectors
		var index_vector: f64[] = [];
		var scale_vector: f64[] = [];
		for(var i = 0; i < this.rows; i++)
		{
			index_vector[i] = i;
			scale_vector[i] = 0;
			for(var j=0; j < this.rows; j++)
			{
				scale_vector[i] = Math.max(scale_vector[i], Math.abs(this.values[i][j]));
			}
		}
		//Begin Forward Elimination
		for(var k = 0; k < this.rows-1; k++) { 
			var max_ratio = 0;
			var max_index = 0;
			for(var i = k; i< this.rows; i++) {
				var ratio = Math.abs(newvalues[index_vector[i]][k]/scale_vector[index_vector[i]]);
				if(ratio > max_ratio) {
					max_index = i;
					max_ratio = ratio;
				}
			}
			var temp = index_vector[k];
			index_vector[k] = index_vector[max_index];
			index_vector[max_index] = temp;
			
			for(var i = k+1; i < this.rows; i++) {
				var xmult = newvalues[index_vector[i]][k]/newvalues[index_vector[k]][k];
				for(var j =k;j < this.columns; j++) {
					newvalues[index_vector[i]][j] = newvalues[index_vector[i]][j] - xmult*newvalues[index_vector[k]][j];
				}
				newsums[index_vector[i]] = newsums[index_vector[i]] - xmult*newsums[index_vector[k]];
			}
			
		}
		var solutions = new Array(this.rows);
		for(var i = this.rows-1; i >= 0; i--) {
			var sum = newsums[index_vector[i]];
			for(var j = i+1; j < this.columns; j++) {
				sum = sum - newvalues[index_vector[i]][j]*solutions[j];
			}
			solutions[i] = [sum/newvalues[index_vector[i]][i]];
		}
		return new Matrix(solutions, this.rows, 1);
		
	}

	/**
		An operation on graph adjacency matrix. 
		It checks if a graph contains a sink node. A node which
		has V-1 inbound edges and 0 outbound edges. 
		Running time is only O(n) 
		@return {boolean} 
	**/

	findSink(): boolean { 
		var k =0;
		for(var i=0; i < this.columns; i++) {
			if( this.values[k][i] == 1) {
				k = i;
			}
		}
		
		for(var i=0; i < this.columns; i++) {
			if(this.values[k][i] == 1) {
				return false;
			}
			if(this.values[i][k] == 0 && i != k) {
				return false;
			}
		}
		return true;
	}

	/**
		Produces two matrices, L and U, which are lower triangular
		matrice and upper triangular matrices respectively.
		@return {Matrix[]} An array of Matrix objects, L = 
	**/
	LUdecomposition(): Matrix[] {
		if(this.rows != this.columns) {
			throw new Error("Matrix incorrectly sized; Must be NxN matrix");
		}
		
		var L = new Matrix([], this.rows, this.columns);
		var U = new Matrix([], this.rows, this.columns);
		var n = this.rows;
		var zeroarray: f64[] = [];
		for(var k=0; k < n; k++) {
			zeroarray[k] = 0;
		}
		
		for(var k=0; k < n; k++) {
			L.values[k]= zeroarray.slice(0);
			U.values[k]= zeroarray.slice(0);
		}
		
		for(var k=0; k < n; k++) {
			L.values[k][k]=1;
			for(var j = k; j < n; j++) {
			
				var sum = 0;
				for(var s = 0; s < k; s++) {
					sum += L.values[k][s]*U.values[s][j];
				}
				U.values[k][j] = this.values[k][j] - sum;
			}
			
			for(var i = k+1; i < n; i++) {
				var sum =0;
				for(var s = 0; s < k; s++) {
					sum += L.values[i][s]*U.values[s][k];
				}
			
				L.values[i][k] = (this.values[i][k] - sum)/U.values[k][k];
			}
		}
		
		return [L,U];
	}

	

	/**
		simple implementation of Floyd-Warshall All-Pairs Shortest Path algorithm for weighted graphs
		@return {Matrix} The APSP matrix for a given matrix
		@note Currently this will expect matrices to be of a prepared form
		var fwtest = [[0,Infinity,Infinity,Infinity,-1,Infinity],
			      [1,0,Infinity,2,Infinity,Infinity],
			      [Infinity,2,0,Infinity,Infinity,-8],
			      [-4,Infinity,Infinity,0,3,Infinity],
			      [Infinity,7,Infinity,Infinity,0,Infinity],
			      [Infinity,5,10,Infinity,Infinity,0]];
	      var mm = new Matrix(6,6,fwtest);
	**/
	FloydWarshall(): Matrix {
		if(this.rows != this.columns) {
			throw new Error("Matrix incorrectly sized; Must be NxN matrix");
		}
		var D = this.copy(); 
		for(var k=0; k < this.rows; k++) {
			for(var i =0; i < this.rows; i++) {
				for(var j = 0; j < this.rows; j++) {
					if(D.values[i][k]+D.values[k][j] < D.values[i][j]) {
						D.values[i][j] =D.values[i][k]+D.values[k][j]; 
					}
				}
			}
			// $("body").append("D(k)=<br>"+D);
		}
		return D;
	}

	/**
		Provide a copy contructor
		@return {Matrix} A copy of the existing matrix
	**/
	copy(): Matrix {
		var retmatrix = new Matrix([], this.rows,this.columns);
		for(var i =0; i < this.rows; i++) {
			retmatrix.values[i]=[];
			for(var j =0; j < this.columns; j++) {
				retmatrix.values[i][j] = this.values[i][j];
			}
		}
		return retmatrix;
	}

	/**
		Provides the Transpose matrix operation, i.e. flips the matrix
		@return {Matrix} The transpose of the original matrix
	**/
	transpose(): Matrix {
		var retmatrix = new Matrix([], this.columns, this.rows);
		for(var i =0; i < this.columns; i++) {
			retmatrix.values[i]=[];
			for(var j =0; j < this.rows; j++) {
				retmatrix.values[i][j] = this.values[j][i];
			}
		}
		return retmatrix;
	}
	//I might rename this toHTML and create a different to string method
	toHTML(): string {
		var retstring = "";
		for(var i = 0; i < this.rows; i++) {
			retstring += "| ";
			for(var k = 0; k < this.columns; k++) {
				retstring += this.values[i][k] +" ";
			}
			retstring +="|<br />";
		}
		return retstring;
	}

}

export function toMatrix(data: f64[][]): Matrix {
	return new Matrix(data, data.length, data[0].length);
}

export function toData(mat: Matrix): f64[][] {
	return mat.values;
}
/*
var testdata = [[6,-2,2,4],
		[12,-8,6,10],
		[3,-13,9,3],
		[-6,4,1,-18]];
		
var testsumvector = [16,26,-19,-34];
var mymatrix = new Matrix(4,4,testdata);
var sumvec = new Matrix(4,1,testsumvector);

var testdata2 = [[3,-13,9,3],
		 [-6,4,1,-18],
		 [6,-2,2,4],
		 [12,-8,6,10]];
var sumvec2 = new Matrix(4,1,[-19,-34,16,26]);
var sumvec22 = new Matrix(4,1,[[-19],[-34],[16],[26]]);
var ppmatrix = new Matrix(4,4,testdata2);

var left2 = new Matrix(2,2,[[1,3],[4,4]]); //answer is [[7,17],[20,28]]
var right2 = new Matrix(2,2,[[4,2],[1,5]]);

var left1 =new Matrix(1,2,[[1,2]]); //anser is [[10]]
var right1 =new Matrix(2,1,[[4],[3]]);
var problem2 = new Matrix(3,3,[[1,-1,2],[-2,1,-1],[4,-1,2]]);
problem2.ScaledPartialPivotGaussian(new Matrix(3,1,[-2,2,1]));
var problem3 = new Matrix(3,3,[[2,4,-2],[1,3,4],[5,2,0]]);
problem3.ScaledPartialPivotGaussian(new Matrix(3,1,[6,-1,2])).values+"";

var t = [new Matrix(2,2,[[0,0],[1,0]])];
t[1] = new Matrix(2,2,[[0,1],[1,0]]);
t[2] = new Matrix(3,3,[[0,1,0],[0,0,0],[0,1,0]]);
t[3] = new Matrix(3,3,[[0,1,0],[0,0,0],[0,1,1]]);
t[4] = new Matrix(3,3,[[0,1,0],[0,0,0],[0,0,1]]);
t[5] = new Matrix(3,3,[[0,0,0],[0,0,0],[0,1,1]]);
t[6] = new Matrix(4,4,[[0,0,1,0],[0,0,1,0],[0,0,0,0],[0,0,1,0]]);
t[7] = new Matrix(4,4,[[0,1,1,1],[1,0,1,1],[0,0,0,0],[1,1,1,0]]);
t[8] = new Matrix(4,4,[[0,1,1,1],[1,0,1,1],[0,0,0,1],[1,1,1,0]]);
t[9] = new Matrix(4,4,[[0,1,1,1],[1,0,1,1],[0,0,0,0],[1,1,0,0]]);
*/


/**
	Given an array of f64s creates a row Matrix object.
	Essentially shortand for creating matrices of form [a,b,c,...]
	@param {Double[]} the matrix entries 
	@return {Matrix} a 1-by-X matrix
**/
export function rowVector(data: f64[]): Matrix {
	return new Matrix([data], 1,data.length);
}

/**
	Given an array of f64s creates a column vector Matrix object.
	Essentially shortand for creating matrices of form 
	[[a]
	 [b]
	 [...]
	 [c]]
	@param {Double[]} the matrix entries 
	@return {Matrix} a X-by-1 matrix
**/
export function columnVector(data: f64[]): Matrix {

	var columns: f64[][] = [];
	for(var i  =0; i < data.length; i++) {
		columns[i] = [data[i]];
	}
	return new Matrix(columns, data.length,1);
}


/**
	Adds one matrix to another.
	@param that {Matrix} Matrix to be added with.
	@return {Matrix} The resulting sum
**/
export function add(left: Matrix, right: Matrix): Matrix {
  if (left.rows == right.rows && left.columns == right.columns) {
    var newvalues: f64[][] = new Array(left.rows);
    for (var i = 0; i < left.rows; i++) {
      newvalues[i] = [];
      for (var j = 0; j < left.columns; j++) {
        newvalues[i][j] = left.values[i][j] + right.values[i][j];
      }
    }
    return new Matrix(newvalues, left.rows, left.columns);
  } else {
    throw new Error("Matrix size mismatch; Addition is not defined.");
  }
}

export function toString(mat: Matrix): string {
  var retstring = "[ ";
  for (var i = 0; i < mat.rows; i++) {
    retstring += "[ ";
    for (var k = 0; k < mat.columns; k++) {
      retstring += mat.values[i][k].toString() + " ";
    }
    retstring += "] ";
  }
  retstring += "]";
  return retstring;
}