
function twoPow(x: number): number {
    return 1 << x;
}

function oneMask(n: number): number {
    return twoPow(n)-1;
}

function countOneBits(n: number): number {
    return n === 0 ? 0 : (n & 1) + countOneBits(n >> 1)
}

function hammingWeight(n: number): number {
    if(n < 0 || n > 256) throw new Error("out of range")
    console.log(`n: ${n} also ${n.toString(2)}`)
    let count = 0;
    let i = 0;
    let nprime = n;
    console.log("beforeloop",`i: ${i}`, `n' = ${nprime}`, `count: ${count}`, `oneMask: ${oneMask(i)}`, `cb: ${countOneBits(n & oneMask(i))}`)
    console.log("invariants", i >= 0 && i <= 8, nprime == n >> i, count == countOneBits(n & oneMask(i)));
    while (i < 8) {
        console.log("");
        console.log('before',`i: ${i}`, `n' = ${nprime}`, `count: ${count}`, `oneMask: ${oneMask(i)}`, `cb: ${countOneBits(n & oneMask(i))}`)
        console.log("invariants", i >= 0 && i <= 8, nprime == n >> i, count == countOneBits(n & oneMask(i)));
        count += nprime & 1;
        nprime = nprime >> 1;
        i++;
        console.log('Afterloop',`i: ${i}`, `n' = ${nprime}`, `count: ${count}`, `oneMask: ${oneMask(i)}`, `cb: ${countOneBits(n & oneMask(i))}`)
        console.log("invariants", i >= 0 && i <= 8, nprime == n >> i, count == countOneBits(n & oneMask(i)));
    }
    return count;
};

// hammingWeight(160);
let nums: [number, number][][] = new Array(256);
function hammingWeight2(n: number): number {
    if(n < 0 || n > 256) throw new Error("out of range")
    console.log(`n: ${n} also ${n.toString(2)}`)
    let count = 0;
    let nprime = n;
    console.log("beforeloop",`n' = ${nprime}`, `count: ${count}`, `cb: ${countOneBits(n - nprime)}`)
    console.log("invariants",nprime  >= 0 && nprime <= 255, count == countOneBits(n - nprime) );
    nums[n] = [];
    nums[n].push([nprime, countOneBits(nprime)]);

    while (nprime > 0) {
        console

        let gv = nprime;
        console.log("beforeloop",`n' = ${nprime}`, `count: ${count}`, `cb: ${countOneBits(n - nprime)}`)
        console.log("invariants",nprime  >= 0 && nprime <= 255, count == countOneBits(n - nprime) );
        console.log("");
        count += 1;
        nprime = nprime & (nprime-1);
        nums[n].push([nprime, countOneBits(nprime)]);
        console.log("afterloop",`n' = ${nprime}`, `count: ${count}`, `cb: ${countOneBits(n - nprime)}`)
        console.log("invariants",nprime  >= 0 && nprime <= 255, count == countOneBits(n - nprime) );
        console.log("WHAT", gv, nprime, nprime < gv)
        console.log("a",nprime)
        console.log("b",countOneBits(nprime))
    }
    return count;
};
// for(let i = 0; i < 256; i++) {

console.log(   hammingWeight2(240));
// }
// console.log(nums[255]);
// console.log(nums.every(num => num.every(step => step.every(elem => elem))));