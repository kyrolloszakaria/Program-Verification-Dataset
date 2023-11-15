/*
https://leetcode.com/problems/add-two-numbers/
You are given two non-empty linked lists representing two non-negative integers. The digits are stored in reverse order, and each of their nodes contains a single digit. Add the two numbers and return the sum as a linked list.

You may assume the two numbers do not contain any leading zero, except the number 0 itself.

Input: l1 = [2,4,3], l2 = [5,6,4]
Output: [7,0,8]
Explanation: 342 + 465 = 807.

 class ListNode {
 *     val: number
 *     next: ListNode | null
 *     constructor(val?: number, next?: ListNode | null) {
 *         this.val = (val===undefined ? 0 : val)
 *         this.next = (next===undefined ? null : next)
 *     }
 * }
*/

datatype ListNode = Nil | Cons(val: int, tail: ListNode)
function method power(A:nat, N:nat): nat
{
	if (N==0) then 1 else A * power(A,N-1)
}

function toNum(ls: ListNode, n: nat): int {
    match ls
    case Nil => 0
    case Cons(val, tail) => val*power(10, n) + toNum(tail, n+1)
}

function method getVal(ls: ListNode): int {
    match ls
    case Nil => 0
    case Cons(val, tail) => val
}

function method getTail(ls: ListNode): ListNode {
    match ls
    case Nil => Nil
    case Cons(val, tail) => tail
}

function method size(ls: ListNode): nat {
    match ls
    case Nil => 0
    case Cons(val, tail) => 1+size(tail)
}

method addTwoNumbersR(l1: ListNode, l2: ListNode, carry: nat) returns (head: ListNode)
     ensures toNum(head, 0) == toNum(l1, 0) + toNum(l2, 0)
     decreases size(l1), size(l2)
{
    if l1 == Nil && l2 == Nil {
        head := if carry > 0 then Cons(carry, Nil) else Nil;
    }
    var sum := getVal(l1)+getVal(l2)+carry;
    var booger := addTwoNumbersR(getTail(l1), getTail(l2), if sum >= 10 then 1 else 0);
    head := Cons(sum%10, booger);
}

// method addTwoNumbers(l1: ListNode, l2: ListNode) returns (head: ListNode) 
//     ensures toNum(head, 0) == toNum(l1, 0) + toNum(l2, 0)
// {
//     head := Nil;
//     var result := Nil;
//     var currentLeft := l1;
//     var currentRight := l2;
//     var carry := 0;
//     while currentLeft != Nil || currentRight != Nil 
//     {
//         var sum := getVal(currentLeft) + getVal(currentRight) + carry;
//         carry := if sum >= 10 then 1 else 0;
//         match result {
//             case Nil => 

//         }
//     }

// }

method TestMain() returns (x: bool) {
    var foo := Cons(1, Nil);
    var boo := Cons(2, Cons(1, Nil));
    assert toNum(boo, 0) == 12;
    if(boo == Nil) {
        return true;
    }
    return false;
}

/*
function getVal(l: ListNode | null): number {
    return l !== null ? l.val : 0;
}

function addTwoNumbers(l1: ListNode | null, l2: ListNode | null): ListNode | null {
    let resultHead = null;
    let result = null;
    let currentLeft = l1;
    let currentRight = l2;
    let carry = 0;
    while(currentLeft !== null || currentRight !== null) {
        let sum = getVal(currentLeft) + getVal(currentRight) + carry;
        carry = sum >= 10 ? 1 : 0;
        if(result) {
            result.next = new ListNode(sum%10);
            result = result.next;
        }else{
            resultHead = new ListNode(sum%10);
            result = resultHead;
        }
        
        if(currentLeft) {
            currentLeft = currentLeft.next;
        }
        if(currentRight) {
            currentRight = currentRight.next;
        }
    }
    if(carry > 0) {
        result.next = new ListNode(carry);
    }
    return resultHead;
};

function getTail(l1: ListNode | null): ListNode | null {
    return l1 !== null ? l1.next : null; 
}

function addTwoNumbers(l1: ListNode | null, l2: ListNode | null, carry: number = 0): ListNode | null {
   if(l1 == null && l2 == null) {
       return carry > 0 ? new ListNode(carry) : null;
   }
   let sum = (getVal(l1)+getVal(l2)+carry)
   return new ListNode(sum%10, addTwoNumbers(getTail(l1),getTail(l2), sum >= 10 ? 1 : 0))
};
*/
