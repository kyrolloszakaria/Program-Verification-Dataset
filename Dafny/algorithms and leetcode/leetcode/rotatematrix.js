


function rotationPermutation(n) {
    return function(index) {
        return index * n ** 3 % (n*n+1);
    }
}


function forwardRotationPermutation(n) {
    return function(index) {
        return index * n  % (n*n+1);
    }
}

function rotationPermLookup(n) {
    let perm = rotationPermutation(n);
    let permutation=[];
    for(let i=0; i < n*n;i++) {
        permutation[perm(i+1)-1]=i+1
    }
    return permutation;
}

function arr2pos(n, y,x) {
    return n*y+x+1;
};

function pos2arr(n, p) {
    return [Math.floor((p-1)/n), (p-1)%n]
}

function swapInPlace(mat) {
    const n = mat.length;
    const nsq = n * n;
    let perm = forwardRotationPermutation(n);
    let visited = new Set();
    for(let i=1; i <= nsq; i++) {
        if(visited.has(i)) continue;
        let temp = null;
        let k = i;
        while(!visited.has(k)) {
            console.log(k);
            visited.add(k);
            let [y,x] = pos2arr(n,k);
            let j = perm(k);
            let [a,b] = pos2arr(n, j);
            let localtemp = mat[a][b];

            mat[a][b] = temp === null ? mat[y][x] : temp;
            temp = localtemp;
            k = j;
        }
    }
}

function rotateNxNMatrix(mat) {
    const n = mat.length;
    let result = "";
    let perm = rotationPermutation(n);
    for(let i = 0; i < n; i++) {
        for(let k = 0; k < n; k++) {
            let pos = perm(arr2pos(n,i,k));
            let location = pos2arr(n, pos);
            //console.log(pos, location);
            result += ""+mat[location[0]][location[1]]+" ";
        }
        result += " \n"
    }
    console.log(result);
    //const lookup = rotationPermLookup(n);
    //for(let i = 1; i <= n*n; i++) {
        //let pos = lookup[i-1]
        //let location = pos2arr(n, pos);
        ////console.log(pos, location);
        //result += ""+mat[location[0]][location[1]]+" ";
        //if(((i) % n) == 0) {
            //result += "\n";
        //}
            ////let location = pos2arr(n, pos);
    //}
    //console.log(result);
}

function matrixToProxy(mat) {
    let rows = {};
    return new Proxy(mat, {
        get: function(oTarget, index) {
            if(index === "length") {
                return mat.length;
            }
            if(typeof index !== "string") {
                return oTarget[index];
            }
            //console.log("got here top level", index);
            if(index < 0 || index >= mat.length) {
                return undefined;
            }
            if(rows[index]) return rows[index];
            
            rows[index] = rowProxy(mat, index);
            return rows[index];
            //return rowProxy(mat, index);
        }
    });
}

function rowProxy(mat, row) {
    let startIndex = Number(row)*mat.length;
    let perm = rotationPermutation(mat.length);
    return new Proxy(mat, {
        get: function (oTarget, index)  {
            if(index === "length") {
                return mat.length;
            }
            if(typeof index !== "string") {
                return oTarget[index];
            }
            let iIndex = Number(index);
            if(iIndex < 0 || iIndex >= mat.length) {
                return undefined;
            }
            let [y,x] = pos2arr(mat.length, perm(startIndex+iIndex+1));
            return oTarget[y][x]
        }
    });
}

function rowProxyInPlace(mat, rows, row, perm) {
    let startIndex = Number(row)*mat.length;
    return new Proxy(mat, {
        get: function (oTarget, index)  {
            if(index === "toJSON") {
                return () => {
                    let result = [];
                    for(let i=0; i<mat.length; i++) {
                        let [y,x] = pos2arr(mat.length, perm(startIndex+i+1));
                        result.push(rows[y][x]);
                    }
                    return result;
                }
            }
            if(index === "length") {
                return mat.length;
            }
            if(typeof index !== "string") {
                return oTarget[index];
            }
            let iIndex = Number(index);
            if(iIndex < 0 || iIndex >= mat.length) {
                return undefined;
            }
            let [y,x] = pos2arr(mat.length, perm(startIndex+iIndex+1));
            return rows[y][x]
        }
    });
}

function rotateLookups(mat) {
    let perm = rotationPermutation(mat.length);
    let rows = [];
    let proxyRows = [];
    for(let i = 0; i < mat.length; i++) {
        let value = mat[i];
        rows[i] = value;
        ((k,proxy) => {
        proxyRows[k] = proxy;
        Object.defineProperty(mat, k, {get: function() {
            return proxy;
        }})})(i, rowProxyInPlace(mat, rows, i, perm));
    }

    mat.toJSON = function() {
       return proxyRows
    }
}

let test1 = [
    [1,2,3],
    [4,5,6],
    [7,8,9]
]
console.log(test1);
rotateNxNMatrix(test1);
//let ex = matrixToProxy(test1);
//printMatrix(ex);
rotateLookups(test1);
printMatrix(test1);

function printMatrix(mat) {
    let n = mat.length;
    let result = "";
    for(let i = 0; i < n; i++) {

        for(let j = 0; j < n; j++) {
            result += mat[i][j]+" ";
        }
        result += "\n";
    }
    console.log(result);
}

let test2 = [
    [1,2,3,4],
    [5,6,7,8],
    [9,10,11,12],
    [13,14,15,16]
];


//function swapInPlace(mat) {
    //const n = mat.length;
    //const limit = Math.ceil(n*n/2);
    //let perm = forwardRotationPermutation(n);
    //let generators = new Set();
    //for(let i=1;i < n; i++) {
        //generators.add(i);
        //for(let k=1; k < i; k++) {
            //if(k*n+i <= limit) {
                //let pot = 
                //generators.add(k*n+i);
            //}
        //}
    //}
    //console.log(generators);
    //for(let i of generators) {
    ////for(let i=1; i < n; i++) {
        //let temp = null;
        //let k = i;
        //while(k !== i || temp == null) {
            ////console.log(k);
            //let j = perm(k);
            //let [y,x] = pos2arr(n,k);
            //let [a,b] = pos2arr(n, j);
            //let localtemp = mat[a][b];

            //mat[a][b] = temp === null ? mat[y][x] : temp;
            //temp = localtemp;
            //k = j;
        //}
    //}
//}



//rotateNxNMatrix(test1);
//swapInPlace(test1);
//console.log(test1);

//rotateNxNMatrix(test2);
//swapInPlace(test2);
//console.log(test2);


let test3=[[1,2,3,4,5],[6,7,8,9,10],[11,12,13,14,15],[16,17,18,19,20],[21,22,23,24,25]];

console.log(test3);
rotateNxNMatrix(test3);
let ex3 = matrixToProxy(test3);
printMatrix(ex3);
//swapInPlace(test3);

//let test4=[
    //[2,29,20,26,16,28], //1->5 (0-5)
    //[12,27,9,25,13,21], //(1->3)
    //[32,33,32,2,28,14], //(2->3)
    //[13,14,32,27,22,26], //
    //[33,1,20,7,21,7],
    //[4,24,1,6,32,34]]

//rotateNxNMatrix(test4);
//swapInPlace(test4);
//console.log(test4);

