module ModuleA {
    function Plus(x: int, y: int): int {
        x + y
    }
}

module ModuleB {
    import ModuleA
    function Double(x: int): int {
        ModuleA.Plus(x,x)
    }
}

module ModuleB2 {
    import A = ModuleA
    function Double(x: int): int {
        A.Plus(x,x)
    }
}

module ModuleC {
    export
        provides Color
        reveals Double
    datatype Color = Blue | Yellow | Green | Red
    function Double(x: int): nat
        requires 0 <= x
        ensures Double(x) % 2 == 0
    {
        if x == 0 then 0 else 2 + Double(x-1)
    }
}

module D {
    import ModuleC
    method Test() {
        var c: ModuleC.Color;
        // c := ModuleC.Yellow; //providing only provides the signature
        assert ModuleC.Double(3) == 6; //revealed allows reasoning about the function and it's value
    }
}

module ModuleE {
    export
        // all three following lines are valid, but have different behaviors
        reveals Parity, F //fully exports
        // reveals *
        // provides Parity, F //exports only signatures but no definitions
    datatype Parity = Even | Odd
    function F(x: int): Parity
    {
        if x % 2 == 0 then Even else Odd
    }
}

function reverse<A>(x: seq<A>): seq<A> 

{
    if x == [] then [] else reverse(x[1..])+[x[0]]
}

module ImmutableQueueSeq {
    type Queue<A>
    function method Empty(): Queue
    function method Enqueue<A>(q: Queue, a: A): Queue
    function method Dequeue<A>(q: Queue): (A, Queue)
        requires q != Empty()

    function Elements<A>(q: Queue): seq<A>
    function length(q: Queue): nat

    lemma EmptyCorrect<A>()
        ensures Elements(Empty<A>()) == []
    lemma EnqueueCorrect<A>(q: Queue, x: A)
        ensures  Elements(Enqueue(q, x)) == Elements(q)+[x]
    lemma DequeueCorrect<A>(q: Queue)
        requires q != Empty()
        ensures var (a, q') := Dequeue(q); [a]+Elements(q') == Elements(q)
    lemma EmptyUnique<A>(q: Queue)
        ensures Elements(q) == [] ==> q == Empty()
}

module QueueClient {
    import IQ = ImmutableQueueSeq
    method Client() {
        IQ.EmptyCorrect<int>();
        var q: IQ.Queue<int> := IQ.Empty();
        assert IQ.Elements(q) == [];
        IQ.EnqueueCorrect(q, 20);
        q := IQ.Enqueue(q, 20);

        assert IQ.Elements(q) == []+ [20];
        assert [20] == [20] + [];
        IQ.DequeueCorrect<int>(q);
        var (a, q') :=  IQ.Dequeue(q);
        assert [20]+IQ.Elements(q') == IQ.Elements(q);
        assert IQ.Elements(q') == [];
        IQ.EmptyUnique(q');
        assert q' == IQ.Empty();
        // assert a == 20;
        // assert q' == IQ.Empty();
    }
}