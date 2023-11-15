
module PriorityQueue {
    type PQueue
    function Empty(): PQueue
    predicate IsEmpty(pq: PQueue)
    function Insert(pq: PQueue, y: int): PQueue
    function RemoveMin(pq: PQueue): (int, PQueue)
        requires Valid(pq) && !IsEmpty(pq)
    ghost function Elements(pq: PQueue): multiset<int>
    ghost predicate Valid(pq: PQueue)
    lemma EmptyCorrect()
        ensures var pq:=Empty(); Valid(pq) && Elements(pq) == multiset{}
    lemma IsEmptyCorrect(pq: PQueue)
        requires Valid(pq)
        ensures IsEmpty(pq) <==> Elements(pq) == multiset{}
    lemma InsertCorrect(pq: PQueue, y: int)
        requires Valid(pq)
        ensures Elements(Insert(pq, y)) == Elements(pq) + multiset{y}
    ghost predicate IsMin(y: int, s: multiset<int>) {
        y in s && forall x :: x in s ==> y <= x
    }
    lemma RemoveMinCorrect(pq: PQueue)
        requires Valid(pq) && !IsEmpty(pq)
        ensures var (y, pq') := RemoveMin(pq);
            Valid(pq') &&
            IsMin(y, Elements(pq)) &&
            Elements(pq') + multiset{y} == Elements(pq)

    //Provides export signature only
    //reveals exports signature and body
    export
        provides PQueue, Empty, IsEmpty, Insert, RemoveMin, Valid
        provides Elements
        provides EmptyCorrect, IsEmptyCorrect
        provides InsertCorrect, RemoveMinCorrect
        reveals IsMin
}

module BTreePQ refines PriorityQueue {
    datatype BraunTree = Leaf | Node(x: int, left: BraunTree, right: BraunTree)
    type PQueue = BraunTree

    ghost predicate IsBinaryHeap(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(x, left, right) =>
            IsBinaryHeap(left) && IsBinaryHeap(right) &&
            (left == Leaf || x <= left.x) &&
            (right == Leaf || x <= right.x)
    }

    ghost predicate IsBalanced(pq: PQueue) {
        match pq
        case Leaf => true
        case Node(_, left, right) => 
        IsBalanced(left) && IsBalanced(right) &&
        var L, R := |Elements(left)|, |Elements(right)|;
        L == R || L == R + 1
    }

    ghost predicate Valid ... {
        IsBinaryHeap(pq) && IsBalanced(pq)
    }

    lemma BraunTreeValid(pq: PQueue)
        requires Valid(pq)
        ensures IsBinaryHeap(pq) && IsBalanced(pq)
    {}

    lemma {:induction false} ChildrenValid(pq: PQueue)
        requires Valid(pq)
        requires pq != Leaf
        ensures Valid(pq.left) && Valid(pq.right)
    {}

    ghost function Elements ... {
        match pq
        case Leaf => multiset{}
        case Node(x, left, right) => multiset{x} +  Elements(left) +  Elements(right)
    }

    function Empty ... {
        Leaf
    }

    predicate IsEmpty ... {
        pq == Leaf
    }

    lemma EmptyCorrect ... {

    }

    lemma IsEmptyCorrect ... {

    }

    lemma {:induction false} BinaryHeapStoresMinimum(pq: PQueue, y: int)
        requires IsBinaryHeap(pq) && y in Elements(pq)
        ensures pq.x <= y

    function Insert(pq: PQueue, y: int): PQueue {
        match pq
        case Leaf => Node(y, Leaf, Leaf)
        case Node(x, left, right) => 
            if y < x then
                Node(y, Insert(right, x), left)
            else
                Node(x, Insert(right, y), left)
    }

    lemma InsertCorrect ... {

    }

    function RemoveMin ...
    {
        (pq.x, DeleteMin(pq))
    }


    function DeleteMin(pq: PQueue): PQueue
        requires Valid(pq) && !IsEmpty(pq)
    {
        if pq.left == Leaf || pq.right == Leaf  then pq.left 
        else if pq.left.x <= pq.right.x then Node(pq.left.x, pq.right, DeleteMin(pq.left))
        else Node(pq.right.x, ReplaceRoot(pq.right, pq.left.x), DeleteMin(pq.left))
    }



    function ReplaceRoot(pq: PQueue, y: int): PQueue
        requires !IsEmpty(pq)
    {
        if pq.left == Leaf || (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x)) then
            Node(y, pq.left, pq.right)
        else if pq.right == Leaf then
            Node(pq.left.x, Node(y, Leaf, Leaf), Leaf)
        else if pq.left.x < pq.right.x then
            Node(pq.left.x, ReplaceRoot(pq.left, y), pq.right)
        else
            Node(pq.right.x, pq.left, ReplaceRoot(pq.right, y))
    }

    lemma ReplaceRootHelper(pq: PQueue, y: int, pq': PQueue, right: PQueue)
        requires Valid(pq) && !IsEmpty(pq)
        requires Valid(pq.right)
        requires pq.right != Leaf && pq.left.x >= pq.right.x
        requires right == ReplaceRoot(pq.right, y)
        requires !(pq.left == Leaf  || (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x)))
        requires Valid(right)
        requires |Elements(right)| == |Elements(pq.right)|
        requires Elements(pq.right) + multiset{y}  == Elements(right) + multiset{pq.right.x}
        requires pq' == Node(pq.right.x, pq.left, right)
        ensures Valid(pq')
    {}

    lemma {:induction false} ReplaceRootCorrect(pq: PQueue, y: int) 
        requires Valid(pq) && !IsEmpty(pq)
        ensures var pq' := ReplaceRoot(pq, y);
        Valid(pq') && Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x} && |Elements(pq)| == |Elements(pq')|
        //Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x} && |Elements(pq)| == |Elements(pq')|
    {
        if pq.left == Leaf  || (y <= pq.left.x && (pq.right == Leaf || y <= pq.right.x)) {
            var pq' := Node(y, pq.left, pq.right);
            assert pq' == ReplaceRoot(pq, y);
            assert Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq)| == |Elements(pq')|;
            assert Valid(pq');
        } else if pq.right == Leaf {
            var pq' := Node(pq.left.x, Node(y, Leaf, Leaf), Leaf);
            assert Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq)| == |Elements(pq')|;
            assert Valid(pq');
        } else if pq.left.x < pq.right.x {
            var left := ReplaceRoot(pq.left, y);
            var pq' := Node(pq.left.x, left, pq.right);
            assert pq' == ReplaceRoot(pq, y);
            ChildrenValid(pq);
            ReplaceRootCorrect(pq.left, y);
            calc {
                Elements(pq) + multiset{y};
                multiset{pq.x} + Elements(pq.left) + Elements(pq.right) + multiset{y};
                Elements(pq.left) + multiset{y} + Elements(pq.right) + multiset{pq.x};
                == {assert Elements(pq.left) + multiset{y} == Elements(left) + multiset{pq.left.x};}
                multiset{pq.left.x} + Elements(left) + Elements(pq.right) + multiset{pq.x};
                ==
                Elements(pq') + multiset{pq.x};
            }
            assert Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq)| == |Elements(pq')|;
            assert Valid(pq');
        } else {
            var right := ReplaceRoot(pq.right, y);
            var pq' := Node(pq.right.x, pq.left, right);
            assert pq' == ReplaceRoot(pq, y);
            ReplaceRootCorrect(pq.right, y);
            ChildrenValid(pq);
            ReplaceRootHelper(pq, y, pq', right);
            calc {
                Elements(pq) + multiset{y};
                multiset{pq.x} + Elements(pq.left) + Elements(pq.right) + multiset{y};
                Elements(pq.right) + multiset{y} + Elements(pq.left) + multiset{pq.x};
                == {assert Elements(pq.right) + multiset{y} == Elements(right) + multiset{pq.right.x};}
                multiset{pq.right.x} + Elements(pq.left) + Elements(right) + multiset{pq.x};
                ==
                Elements(pq') + multiset{pq.x};
            }
            assert Elements(pq) + multiset{y} == Elements(pq') + multiset{pq.x};
            assert |Elements(pq)| == |Elements(pq')|;
            assert Valid(pq');
        }
    }

    lemma RemoveMinCorrect ... {
        DeleteMinCorrect(pq);       
    }

    lemma {:induction false} DeleteMinCorrect(pq: PQueue)
        requires Valid(pq) && pq != Leaf
        ensures var pq' := DeleteMin(pq);
        Valid(pq') && Elements(pq') + multiset{pq.x} == Elements(pq) &&
        |Elements(pq')| == |Elements(pq)| - 1
    {
        BraunTreeValid(pq);
        assert IsBalanced(pq);
        if pq.left == Leaf || pq.right == Leaf {
            var pq' := pq.left;
            assert DeleteMin(pq) == pq';
            assert Valid(pq');
            assert Elements(pq') + multiset{pq.x} == Elements(pq);
        } else if pq.left.x <= pq.right.x {
            // assert IsBalanced(pq);
            // BraunTreeValid(pq.left);
            // ChildrenValid(pq);
            var pq' := Node(pq.left.x, pq.right, DeleteMin(pq.left));
            assert pq' == DeleteMin(pq);
            DeleteMinCorrect(pq.left);
            calc {
                Elements(pq') + multiset{pq.x};
                multiset{pq.left.x} + Elements(pq.right) + Elements(DeleteMin(pq.left)) + multiset{pq.x};
                == {assert Elements(DeleteMin(pq.left))  == Elements(pq.left) - multiset{pq.left.x};}
                multiset{pq.left.x} + Elements(pq.right) + Elements(pq.left) - multiset{pq.left.x} + multiset{pq.x};
                Elements(pq.right) + Elements(pq.left) + multiset{pq.x};
                multiset{pq.x} + Elements(pq.right) + Elements(pq.left);
                multiset{pq.x} + Elements(pq.left) + Elements(pq.right);
                Elements(pq);
            }

            assert DeleteMin(pq) == pq';
            assert Valid(pq');
            assert Elements(pq') + multiset{pq.x} == Elements(pq);
        } else {
            // assert IsBalanced(pq);
            ChildrenValid(pq);
            // BraunTreeValid(pq.left);
            var left, right := ReplaceRoot(pq. right, pq.left.x), DeleteMin(pq.left);
            var pq' := Node(pq.right.x, left, right);

            DeleteMinCorrect(pq.left);
            assert pq' == DeleteMin(pq);
            ReplaceRootCorrect(pq.right, pq.left.x);
            calc {
                Elements(pq') + multiset{pq.x};
                ==
                multiset{pq.right.x} + Elements(left) + Elements(right) + multiset{pq.x};
                ==
                Elements(left) + multiset{pq.right.x} + Elements(right) + multiset{pq.x};
                == {assert Elements(left) + multiset{pq.right.x} ==  Elements(pq.right) + multiset{pq.left.x};}
                Elements(pq.right) + multiset{pq.left.x} + Elements(right) + multiset{pq.x};
                ==
                Elements(right) + multiset{pq.left.x} + Elements(pq.right) + multiset{pq.x};
                == {}
                Elements(pq.left) + Elements(pq.right) + multiset{pq.x};
                ==
                multiset{pq.x} + Elements(pq.left) + Elements(pq.right);
                ==
                Elements(pq);
            }

            assert Valid(pq');
            assert Elements(pq') + multiset{pq.x} == Elements(pq);
        }
    }
}