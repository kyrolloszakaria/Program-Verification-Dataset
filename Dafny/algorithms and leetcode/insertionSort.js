
function insSort(a) {
    for(let j = 1; j < a.length; j++) {
        var key = a[j];
        console.log(`key: ${key}, j: ${j}`)
        console.log("begin", a);
        let i = j - 1;
        while(i >= 0 && a[i] > key) {
            a[i+1] = a[i];
            console.log("inner", a);
            i = i - 1;
        }
        console.log("post inner while", a);
        a[i+1] = key;
    }
}

let test = [5,4,3,2,1];
console.log(test);
insSort(test);
console.log("final: ", test);





//let test2 = [5];
//console.log(test2);
//insSort(test2);
//console.log("final: ", test2);


//let test3 = [1,0];
//console.log(test3);
//insSort(test3);
//console.log("final: ", test3);


//let test4 = [0,1,3,6,5,4];
//console.log(test4);
//insSort(test4);
//console.log("final: ", test4);
