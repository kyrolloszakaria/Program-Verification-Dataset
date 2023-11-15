
function method parent(i: int): int 
{
    i/2
}

function method left(i: int): int
{
    2*i
}

function method right(i: int): int
{
    2*i+1
}

predicate method MaxHeapC(data: array<int>, i: int)
    reads data
    requires 1 <= i
{
    (left(i) > data.Length || data[i-1] >= data[left(i)-1]) && (right(i) > data.Length || data[i-1] >= data[right(i)-1])
}

predicate method MaxHeapSeq(data: seq<int>, i: int)
    requires 1 <= i
{
    (left(i) > |data| || data[i-1] >= data[left(i)-1]) && (right(i) > |data| || data[i-1] >= data[right(i)-1])
}

class MaxHeap {
    var data: array<int>
    ghost var repr: set<object>

    constructor(data: array<int>) 
        ensures this.data == data
        ensures this in repr
    {
        this.data := data;
        this.repr := {this};
    }

    // predicate MaxHeap(i: int)
    //     reads this
    //     requires 1 <= i <= this.data.Length
    // {
    //     this.data[parent(i)-1] > this.data[i-1]
    // }
    
    predicate method MaxHeapChildren(i: int)
        reads this, this.data
        requires 1 <= i
    {
        (left(i) > this.data.Length || this.data[i-1] >= this.data[left(i)-1]) && (right(i) > this.data.Length || this.data[i-1] >= this.data[right(i)-1])
    }

    // method heapify(i: int) returns (largest: int)
    //     modifies this.data
    //     // requires left(i) <= this.data.Length ==> 
    //     requires 1 <= i <= this.data.Length
    //     requires forall x :: i < x <= this.data.Length ==> MaxHeapChildren(x)
    //     ensures 1 <= largest <= this.data.Length
    //     ensures this.data[i-1] >= this.data[largest-1]
    //     ensures multiset(this.data[..]) == multiset(old(this.data[..]))
    //     ensures forall x :: i <= x <= this.data.Length  ==> MaxHeapChildren(x)
    //     decreases this.data.Length - i
    // {
    //     var l := left(i);
    //     var r := right(i);
    //     largest := i;
    //     if l <= this.data.Length && this.data[l-1] > this.data[i-1] {
    //         largest := l;
    //     }

    //     if r <= this.data.Length && this.data[r-1] > this.data[largest-1] {
    //         assert largest == i ==> this.data[l-1] <= this.data[i-1];
    //         assert largest == l ==> this.data[l-1] > this.data[i-1];
    //         largest := r;
    //         assert this.data[r-1] > this.data[l-1];
    //     }
    //     if largest != i {
    //         assert largest == l || largest == r;
    //         assert largest == r ==> this.data[r-1] >= this.data[i-1];
    //         assert largest == r ==> this.data[r-1] >= this.data[l-1];
    //         // assert largest == l ==> this.data[l-1] >= this.data[i-1] && this.data[l-1] >= this.data[r-1];
    //         // assert !(largest == r) ==> (r > this.data.Length || this.data[r-1] <= this.data[l-1]);
    //         assert (largest == l) ==> (r > this.data.Length || this.data[r-1] <= this.data[l-1]);
    //         // assert this.data[i-1] <= this.data[largest-1];
    //         // assert temp <= this.data[largest-1];
    //         // assert this.data[i-1] >= temp;
    //         assert forall x :: i <  x <= this.data.Length ==> MaxHeapChildren(x);
    //         var temp := this.data[i-1];
    //         this.data[i-1] := this.data[largest-1];
    //         this.data[largest-1] := temp;
    //         assert 1 <= largest <= this.data.Length;
    //         assert this.data[i-1] > old(this.data[i-1]);
    //         assert this.data[i-1] >= this.data[largest-1];
    //         assert this.data[i-1] >= this.data[l-1];
    //         assert r > this.data.Length || this.data[i-1] >= this.data[r-1];
    //         assert largest > i;
    //         assert MaxHeapChildren(i);

    //         assert largest-1 != i+1 && i+1 < this.data.Length ==> old(this.data[i+1]) == this.data[i+1];
    //         // assert unchanged(this.data[largest..]);
    //         // assert MaxHeapChildren(largest);
    //         // assert largest +1 <= this.data.Length ==> MaxHeapChildren(largest+1);

    //         assert forall x :: i < largest < x <= this.data.Length && x != largest ==> MaxHeapChildren(x);
    //         var res := this.heapify(largest);
    //         assert this.data[i-1] >= this.data[largest-1];
    //     }
    // }
    
    /**
        length = 17
        i = 4
        left = 8, 7
        right = 9, 8
        x in 5 .. 17 :: MaxHeapChildren(x) (i+1)..17 

         0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 
        [20,18,16,3,14,12,10, 8, 6, 4, 2, 0, 1,-2, 4, 4,-5]


        i = 8
        left = 16
        right = 17
        x in i' .. i-1 :: MaxHeapChildren (4..15)
         0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 
        [20,18,16,8,14,12,10, 3, 6, 4, 2, 0, 1,-2, 4, 4,-5]


        i = 16
        left = 32
        right = 33
        x in i' .. i-1 :: MaxHeapChildren (4..16) + 17.. MaxHeapChildren
         0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 
        [20,18,16,8,14,12,10, 4, 6, 4, 2, 0, 1,-2, 4, 3,-5]
     */

    method heapify(i: int) returns (largest: int)
        modifies this.data
        // requires left(i) <= this.data.Length ==> 
        requires 1 <= i <= this.data.Length
        requires forall x :: i < x <= this.data.Length ==> MaxHeapChildren(x)
        requires forall x :: i < x <= this.data.Length ==> MaxHeapC(this.data, x)
        // ensures 1 <= largest <= this.data.Length
        // ensures this.data[i-1] >= this.data[largest-1]
        // ensures multiset(this.data[..]) == multiset(old(this.data[..]))
        ensures forall x :: i <= x <= this.data.Length  ==> MaxHeapC(this.data, x)
        decreases this.data.Length - i
    {
        var i' := i;
        ghost var oldi := i;
        largest := i;
        var l := left(i);
        var r := right(i);
        ghost var count := 0;
        ghost var count' := 1;
        while !MaxHeapC(this.data, i')
            invariant count' == count + 1;
            invariant 1 <= largest <= this.data.Length
            invariant l == left(i')
            invariant r == right(i')
            invariant 1 <= i' <= this.data.Length
            invariant i' == i || i' == left(oldi) || i' == right(oldi)
            invariant largest == i'
            invariant count == 0 ==> oldi == i
            invariant oldi > 0
            invariant count > 0 ==> oldi == parent(i')
            invariant count > 0 ==> MaxHeapChildren(oldi)
            invariant count > 0 ==> forall x :: i <= x < i' ==> old(this.data)[x] == this.data[x]
            invariant count > 0 ==> forall x :: i <= x < i' && left(x+1) < this.data.Length ==> old(this.data)[left(x+1)] == this.data[left(x+1)]
            invariant count > 0 ==> forall x :: i <= x < i' && right(x+1) < this.data.Length ==> old(this.data)[right(x+1)] == this.data[right(x+1)]
            // invariant count > 0 ==> forall x :: i <= x <= i' && left(x+1) ==> MaxHeapChildren(left(x+1))
            // invariant forall x :: i <= x <= this.data.Length && x != i' ==> MaxHeapChildren(x)
            invariant forall x :: i <= x <= this.data.Length && x != i' ==> MaxHeapC(this.data, x)
            decreases this.data.Length-i';
        {
            if l <= this.data.Length && this.data[l-1] > this.data[i'-1] {
                largest := l;
            }

            if r <= this.data.Length && this.data[r-1] > this.data[largest-1] {
                largest := r;
            }
            if largest != i' {
                ghost var olddata := this.data[..];
                assert forall x :: i <  x <= this.data.Length && x != i' ==> MaxHeapC(this.data, x);
                label BeforeChange:
                swap(this, i', largest);
                label AfterChange:
                oldi := i';
                assert MaxHeapChildren(oldi);
                // assert this.data[i'-1] > this.data[largest-1];
                // assert old@BeforeChange(this.data[i'-1]) == temp;
                // assert old@AfterChange(this.data[i'-1]) != temp;
                // assert old@BeforeChange(this.data[largest-1]) == this.data[i'-1];
                // assert old@BeforeChange(this.data) == this.data;
                i' := largest;
                assert forall x :: largest <  x <= this.data.Length && x != i' ==> MaxHeapC(this.data, x);
                l := left(i');
                r := right(i');

                
                assert forall x :: i <= x < i' ==> old@AfterChange(this.data[x]) == this.data[x] && left(x+1) < this.data.Length ==> old(this.data)[left(x+1)] == this.data[left(x+1)] && right(x+1) < this.data.Length ==> old(this.data)[right(x+1)] == this.data[right(x+1)];
            }else{
                // label AfterChange:
                // assert forall x :: i <= x < i' ==> old@AfterChange(this.data[x]) == this.data[x];
                assert MaxHeapChildren(i');
                assert MaxHeapChildren(oldi);
            }
            count := count + 1;
            count' := count' + 1;
        }
    }
}

method swap(heap: MaxHeap, i: int, largest: int) 
    modifies heap.data
    requires 1 <= i < largest <= heap.data.Length
    requires heap.data[largest-1] > heap.data[i-1]
    requires left(i) <= heap.data.Length ==> heap.data[largest-1] >= heap.data[left(i)-1]
    requires right(i) <= heap.data.Length ==> heap.data[largest-1] >= heap.data[right(i)-1]
    requires heap.data[largest-1] > heap.data[i-1]
    // requires forall x :: i <= x <= heap.data.Length && x != i ==> heap.MaxHeapChildren(x)
    requires forall x :: i <= x <= heap.data.Length && x != i ==> MaxHeapC(heap.data, x)
    ensures heap.data[i-1] == old(heap.data[largest-1])
    ensures heap.data[largest-1] == old(heap.data[i-1])
    // ensures heap.MaxHeapChildren(i)
    ensures MaxHeapC(heap.data,i)
    ensures forall x :: 1 <= x <= heap.data.Length && x != i && x != largest ==> heap.data[x-1] == old(heap.data[x-1]) 
    // ensures forall x :: i <= x <= heap.data.Length && x != largest ==> heap.MaxHeapChildren(x)
    ensures forall x :: i <= x <= heap.data.Length && x != largest ==> MaxHeapC(heap.data,x)
{
    ghost var oldData := heap.data[..];
    // var z:int :| assume i < z <= heap.data.Length && z != largest && z != i;
    // assert MaxHeapC(heap.data, z);
    // assert forall x :: i < x <= heap.data.Length && x != i ==> MaxHeapC(heap.data, x);
    // forall x | i < x <= heap.data.Length && x != i && x != largest
    //     ensures MaxHeapC(heap.data, x)
    // {
    //    if heap.data.Length > 2 {
    //      var z: int :| i < z <= heap.data.Length && z != i && z != largest && z == x;
    //      assert MaxHeapC(heap.data, z);
    //    }else{
    //    }
    // }

    var temp := heap.data[i-1];
    heap.data[i-1] := heap.data[largest-1];
    heap.data[largest-1] := temp;
    assert MaxHeapC(heap.data, i);

    // assert forall x :: i <= x <= heap.data.Length && x != largest ==> MaxHeapC(heap.data, x);
    // forall x | i < x <= heap.data.Length  && x != largest
    //     ensures MaxHeapC(heap.data, x)
    // {
    //    if heap.data.Length > 2 {
    //      var z: int :| i < z <= heap.data.Length && z != i && z != largest && z == x;
    //     var lz: int := left(z);
    //     var rz: int := right(z);
    //     assert heap.data[z-1] == old(heap.data[z-1]);
    //     assert heap.data[z-1] == old(heap.data)[z-1];
    //     assert lz != i && lz != largest && lz <= heap.data.Length ==> heap.data[lz-1] == old(heap.data[lz-1]) && heap.data[lz-1] == old(heap.data)[lz-1];
    //     assert rz != i && rz != largest && rz <= heap.data.Length ==> heap.data[rz-1] == old(heap.data[rz-1]) && heap.data[rz-1] == old(heap.data)[rz-1];
    //     assert MaxHeapC(heap.data, z);
    //    }else{

    //    }
    // }
    

    // assert MaxHeapC(old(heap.data), z);
    // assert MaxHeapC(heap.data, z);
    // assert heap.MaxHeapChildren(z);

}

lemma arrayToSeqMaxHeap(data: array<int>, sd: seq<int>, end: int) 
    requires 0 < end <= |sd| && end <= data.Length
    requires forall i :: 1 <= i <= end <= data.Length ==> MaxHeapC(data, i)
    requires sd == data[..end]
    requires |sd| == end
    ensures forall i :: 1 <= i < end <= |sd| ==> MaxHeapSeq(sd, i)
{
    forall i | 1 <= i <= end
        ensures MaxHeapSeq(sd, i)
    {
        var l := left(i);
        var r := right(i);
        assert sd[i-1] == data[i-1];
        assert l <= |sd| ==> sd[l-1] == data[l-1];
        assert r <= |sd| ==> sd[r-1] == data[r-1];
        assert MaxHeapC(data, i);
        assert MaxHeapSeq(sd, i);
    }
}

lemma seqToArraySlice(sd: seq<int>, data: array<int>, start: int, end: int)

{

}

method Test() {
    var blarg := [1,2,3,4,5];
    assert blarg[1..3] == [2,3];
}


// lemma restUnchanged(heap: MaxHeap, largest: int, bigger: int, oldData: seq<int>)
//     requires heap.data.Length == |oldData|
//     requires 2 <= largest <= heap.data.Length
//     requires largest < bigger <= heap.data.Length
//     requires forall i :: bigger <= i <= heap.data.Length ==> heap.data[i-1] == oldData[i-1]
// {

// }


twostate lemma UnchangedHeap(heap: MaxHeap, original: seq<int>, index: int, i: int, largest: int) 
    requires heap.data.Length == |original|
    requires 0 <= i < heap.data.Length
    requires 0 <= largest < heap.data.Length && i != largest
    requires forall i :: 0 <= i < heap.data.Length && i != i && largest != i ==> heap.data[i] == original[i]
    requires 1 <= index <= heap.data.Length
    requires heap.MaxHeapChildren(index)
    requires heap.data[i] == original[largest] && heap.data[largest] == original[i]
    ensures heap.MaxHeapChildren(index)
{
    swap(heap, i, largest);
}