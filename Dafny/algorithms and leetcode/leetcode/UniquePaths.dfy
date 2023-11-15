/*
https://leetcode.com/problems/unique-paths/
function factorial(n: number):number {
    if (n <= 1) {
        return 1;
    }else{
       let fact = 1;
       for(let k = 1; k <= n; k++) {
           fact = fact * k;
       }
        return fact;
    }
}

function choose(n: number, k: number): number {
    if(n * k == 0) return 1;
   let base = n;
    for(let i = n-1; i > (n-k); i--) {
        base = base * i;
    }
    return base/factorial(k);
}

function uniquePaths(m: number, n: number): number {
    return choose(m+n-2,Math.max(m,n)-1);
};
*/
include "../math/factorial.dfy"
import opened Factorial


method choosem(n: nat, k: nat) returns (res: nat) 
  requires 0 <= k <= n  
  ensures res == choose(n,k)
{
    if n <= 0 {
        return 1;
    }
    res := n;
    var i := n-1;
    factorialFacts(n);
    while i > (n-k)
        invariant n-k <= i <= n-1
        invariant res == factorial(n)/factorial(i)
    {
        res := res * i;
        i := i - 1;
    }
    assert res == factorial(n)/factorial(n-k);
    return res / factorial(k);
}