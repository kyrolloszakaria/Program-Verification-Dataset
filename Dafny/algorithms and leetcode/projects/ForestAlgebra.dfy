
datatype Forest = Node(alpha: string) | Context | Zero | Product(left: Forest, right: Forest) | Sum(left: Forest, right: Forest)


function method Remove(T: Forest, Q: Forest): Forest 
{
    match T {
        case Node(alpha) => if Q == T then Context else Node(alpha)
        case Context => Context
        case Zero => Zero
        case Sum(L, R) => if T == Q then Context else Sum(Remove(L, Q), Remove(R, Q))
        case Product(L, R) => if T == Q then Context else  Product(Remove(L, Q), Remove(R, Q))
    }
}


function childSet(forest: Forest): multiset<Forest> {
    match forest {
        case Node(alpha) => multiset{Node(alpha)}
        case Context => multiset{}
        case Zero => multiset{}
        case Product(L, R) => childSet(L) + childSet(R)
        case Sum(L, R) => childSet(L) + childSet(R)
    }
}

method tcs() {
    var q := Sum(Node("11"), Node("11"));
    assert childSet(q)[Node("11")] == 2;
}

function forestSet(forest: Forest): set<Forest> {
    match forest {
        case Node(alpha) => {forest}
        case Context => {Context}
        case Zero => {Zero}
        case Product(L, R) => {forest} + forestSet(L) + forestSet(R)
        case Sum(L, R) => {forest} + forestSet(L) + forestSet(R)
    }
}

function forestMultiSet(forest: Forest): multiset<Forest> {
    match forest {
        case Node(alpha) => multiset{forest}
        case Context => multiset{Context}
        case Zero => multiset{Zero}
        case Product(L, R) => multiset{forest} + forestMultiSet(L) + forestMultiSet(R)
        case Sum(L, R) => multiset{forest} + forestMultiSet(L) + forestMultiSet(R)
    }
}

predicate nodeIn(forest: Forest, tree: Forest)
    ensures nodeIn(forest, tree) == true ==> tree in forestSet(forest)
    ensures nodeIn(forest, tree) == false ==> tree !in forestSet(forest)
{
    match forest {
        case Node(alpha) => tree == forest
        case Context => tree == forest
        case Zero => tree == Zero
        case Product(L, R) => if forest == tree then true else nodeIn(L, tree) || nodeIn(R, tree)
        case Sum(L, R) => if forest == tree then true else nodeIn(L, tree) || nodeIn(R, tree)
    }
}

function method concatenation(left: Forest, right: Forest): Forest

{
    if left == Zero then right else if right == Zero then left else Sum(left, right)
}

function method composition(left: Forest, right: Forest): Forest

{
    match left {
        case Node(alpha) => Node(alpha)
        case Zero => Zero
        case Context => right
        case Product(L, R) => Product(composition(L, right), composition(R, right))
        case Sum(L, R) => Sum(composition(L, right), composition(R, right))
    }
}

lemma sumEquality(a: Forest, b: Forest, c: Forest)
    ensures Sum(a, Sum(b,c)) == Sum(Sum(a,b), c)

lemma composititionAssociative(a: Forest, b: Forest, c: Forest)
    ensures composition(a, composition(b,c)) == composition(composition(a,b), c)
{

}

lemma concatenationAssociative(a: Forest, b: Forest, c: Forest)
    ensures concatenation(a, concatenation(b,c)) == concatenation(concatenation(a,b), c)
{
    sumEquality(a,b,c);

}

lemma compositionContextIdentity(a: Forest)
    ensures composition(a, Context) == a;
{

}

lemma concatenationZeroIdentity(a: Forest)
    ensures concatenation(Zero, a) == a
    ensures concatenation(a, Zero) == a
{

}

lemma compositionZeroAnnihilates(a: Forest)
    ensures composition(Zero, a) == Zero
{

}

lemma leftDistributive(q: Forest, p: Forest, r: Forest)
    ensures composition(concatenation(p, q), r) == concatenation(composition(p,r), composition(q,r))
{
    sumEquality(p,q,r);
}

lemma NotInIdempotent(P: Forest, Q: Forest)
    requires nodeIn(P, Q) == false
    ensures Remove(P, Q) == P
{

}

lemma Inverses3(P: Forest, Q: Forest)
    requires P != Q
    requires !nodeIn(P, Context)
    ensures composition(Remove(P,Q),Q) == P
{

}

function method arity(P: Forest): nat  {
    match P {
        case Node(alpha) => 0
        case Zero => 0
        case Context => 1
        case Product(L, R) => arity(L) +  arity(R)
        case Sum(L, R) => arity(L) + arity(R)
    }
}

//     requires forestMultiSet(p)[Context] == 1
//     requires forall x :: x in childSet(r) ==> childSet(r)[x] == 1
//     requires forall x :: x in childSet(p) ==> childSet(p)[x] == 1
//     requires forall x :: x in childSet(q) ==> childSet(q)[x] == 1
//     requires |forestMultiSet(q)| <= 6
//     requires |forestMultiSet(p)| <= 6
//     requires !nodeIn(q, Context)
//     requires !nodeIn(r, Context)

lemma removeIsAssociative(p: Forest, q: Forest, r: Forest)
    requires arity(p) == 1
    requires nodeIn(p, Context)
    requires nodeIn(q, r) == true
    requires forestMultiSet(q)[r] == 1
    requires p != q
    requires q != r && !nodeIn(p,q) && !nodeIn(q, Context)
    requires p != r && !nodeIn(p, r)
    ensures composition(p, Remove(q,r)) == Remove(composition(p, q), r)
{
    assert r !in forestSet(p);
}
/* 

**/

function method apply(mut: Mutation): Forest {
    match mut {
        case Addition(p,q) => composition(p, q)
        case Subtraction(p, q, c) => c
    }
}

predicate combinesTo(prev: Mutation, succ: Mutation) {
    match prev {
        case Addition(p, q) => nodeIn(p, Context) && !nodeIn(p,q) && composition(p,q) == succ.p && nodeIn(composition(p,q), q)
        case Subtraction(p, q, c) => nodeIn(p,q) && composition(c, Zero) == Remove(p,q) && c == succ.p && !nodeIn(c, q)
    }
}

datatype Mutation = Addition(p: Forest, q: Forest) | Subtraction(p: Forest, q: Forest, c: Forest)

method summarizeChange(start: Forest, end: Forest, mutations: seq<Mutation>)
    requires |mutations| > 1
    requires forall i :: 1 <= i < |mutations| ==> combinesTo(mutations[i-1], mutations[i])
    requires mutations[0].p == start;
    requires apply(mutations[|mutations|-1]) == end
{
    var i := 1;
    while i < |mutations| 
        invariant 1 <= i <= |mutations|
    {
        var mut := mutations[i-1];
        match mut {
            case Addition(p,q) => assert mutations[i].p == composition(p,q);
            case Subtraction(p, q, c) => assert mutations[i].p == c;
        }
        i := i + 1;
    }
}

method test() {
    var best := Sum(Node("a"), Context);
    var quest := Sum(Node("a"), Context);
    assert best == quest;

}