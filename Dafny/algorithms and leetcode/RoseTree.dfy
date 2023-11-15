

class RoseTree {
    var NodeType: int
    var id: string
    var children: array<RoseTree>
    ghost var repr: set<object>
    ghost var nodeSet: set<RoseTree>

    predicate Valid()
        reads this, repr, nodeSet
        decreases repr
    {
        && this in repr
        && this in nodeSet
        && children in repr
        && (forall i | 0 <= i < children.Length :: 
            children[i] in nodeSet
            && children[i] in repr
            && children[i].repr <= repr
            && children[i].nodeSet <= nodeSet
            && this !in children[i].nodeSet
            && this !in children[i].repr
            && children[i].Valid())
    }

    constructor(nt: int, id: string, children: array<RoseTree>) 
        requires forall i | 0 <= i < children.Length :: children[i].Valid()
        ensures forall x :: 0 <= x < children.Length ==> children[x].nodeSet <= this.nodeSet 
        ensures forall x :: 0 <= x < this.children.Length ==> this.children[x].nodeSet <= this.nodeSet 
        ensures Valid()
        ensures this.id == id
        ensures this.NodeType == nt
        ensures this.children == children
    {
        this.NodeType := nt;
        this.id := id;
        this.children := children;
        if children.Length == 0 {
            this.nodeSet := {this};
        }else{
            this.nodeSet := {this}+childrenNodeSet(children);
        }
        this.repr := {this, children} + 
          (set i | 0 <= i < children.Length :: children[i]) +
          (set x, i | 0 <= i < children.Length && x in children[i].repr :: x);
    }
}

function setRosePick(s: set<set<RoseTree>>): set<RoseTree> 
    requires s != {}
{
    var x :| x in s; x
}

function setUnion(setosets: set<set<RoseTree>>) : set<RoseTree> 
    decreases setosets
{
    if setosets == {} then {} else
        var x := setRosePick(setosets);
        assert x <= x + setUnion(setosets-{x});
        x + setUnion(setosets-{x})
}

lemma setUnionDef(s: set<set<RoseTree>>, y: set<RoseTree>)
    requires y in s
    ensures setUnion(s) == y + setUnion(s - {y})
{
    var x := setRosePick(s);
    if y == x {

    }else{
        calc {
            setUnion(s);
            ==
            x + setUnion(s - {x});
            == {setUnionDef(s - {x}, y); }
            x + y + setUnion(s - {x} - {y});
            == { assert s - {x} - {y} == s - {y} - {x}; }
            y + x + setUnion(s - {y} - {x});
            == {setUnionDef(s - {y}, x); }
            y + setUnion(s - {y});

        }
    }
}

lemma setUnionReturns(s: set<set<RoseTree>>) 
   ensures s == {} ==> setUnion(s) == {}
   ensures s != {} ==> forall x :: x in s ==> x <= setUnion(s)
{
    if s == {} {
        assert setUnion(s) == {};
    } else {
        forall x | x in s 
            ensures x <= setUnion(s)
        {
            setUnionDef(s, x);
            assert x <= x + setUnion(s-{x});
        }
    }
}

function childNodeSets(children: array<RoseTree>): set<set<RoseTree>> 
    reads children
    reads set x | 0 <= x < children.Length :: children[x]
{
    set x | 0 <= x < children.Length :: children[x].nodeSet
}

function childNodeSetsPartial(children: array<RoseTree>, index: int): set<set<RoseTree>> 
    requires 0 <= index < children.Length
    reads children
    reads set x | index <= x < children.Length :: children[x]
{
    set x | index <= x < children.Length :: children[x].nodeSet
}

function childrenNodeSet(children: array<RoseTree>): set<RoseTree> 
    reads children
    reads set x | 0 <= x < children.Length :: children[x]
    ensures forall x :: x in childNodeSets(children) ==> x <= childrenNodeSet(children)
    ensures forall i :: 0 <= i < children.Length ==> children[i].nodeSet <= childrenNodeSet(children)
{
    var y := childNodeSets(children);
    setUnionReturns(y);
    setUnion(y)
} 


datatype Mutations = Added(node: RoseTree, parent: RoseTree, added: RoseTree, nextSibling: RoseTree?) | Removed(node: RoseTree, parent: RoseTree, removed: RoseTree)
predicate isMutation(mutation: Mutations) {
    match mutation {
        case Removed(node: RoseTree, parent: RoseTree, removed: RoseTree) => WellFormed(node)
        case Added(node: RoseTree, parent: RoseTree, added: RoseTree, nextSibling: RoseTree?) => WellFormed(node)
    }
}

predicate WellFormed(node: RoseTree) {
    true
}

predicate isAncestor(parent: RoseTree, node: RoseTree) 
    reads parent
{
    node in parent.nodeSet
}

predicate isParent(parent: RoseTree, node: RoseTree) 
    reads node
    reads node.children
    reads set x | 0 <= x < node.children.Length :: node.children[x]
    reads parent
    reads parent.children
    reads set x | 0 <= x < parent.children.Length :: parent.children[x]
{
    exists i :: 0 <= i < parent.children.Length && parent.children[i] == node
}

function height(node: RoseTree):nat 
    reads node
    reads node.children
    reads node.repr
    reads node.nodeSet
    reads set x | 0 <= x < node.children.Length :: node.children[x]
    requires node.Valid()
    // requires forall x :: 0 <= x < node.children.Length ==> node.children[x].nodeSet <= node.nodeSet
    decreases node.nodeSet
{
    if node.children.Length == 0 then 1 else 
        var c := set i | 0 <= i < node.children.Length :: height(node.children[i]);
        assert height(node.children[0]) in c;
        assert c != {};
        SetMax(c) + 1
}

function SetMax(s: set<int>): int 
  requires s != {}
  ensures forall x | x in s :: SetMax(s) >= x
{
  var x :| x in s;
  if s == {x} then
    x
  else
    var y := SetMax(s - {x});
    assert forall z | z in s :: z == x || (z in (s - {x}) && y >= z);
    if x > y then x else y
}

// function maxChildHeight(node: RoseTree, children: array<RoseTree>, index: nat, best: nat) : nat 
//     reads node
//     reads node.children
//     reads set x | 0 <= x < node.children.Length :: node.children[x]
//     requires children == node.children
//     requires 0 <= index < children.Length
//     requires forall x :: 0 <= x < node.children.Length ==> node.children[x].nodeSet <= node.nodeSet
//     ensures forall x :: 0 <= x <= index < children.Length ==> maxChildHeight(node, children, index, best) >= height(children[x])
//     decreases node.nodeSet - setUnion(childNodeSetsPartial(children, index)), 1
// {
//     if index == 0 then best else if height(children[index]) >= best then maxChildHeight(node, children, index-1, height(children[index])) else maxChildHeight(node, children, index-1, best)
// }

// function allNode(node: RoseTree): seq<RoseTree> 
// {
//     [node] + childNodes(node.children[..], []) 
// }

// function childNodes(children: seq<RoseTree>, acc: seq<RoseTree>): seq<RoseTree> 
//     decreases |children|
// {
//     if |children| == 0 then acc else childNodes(children[1..], allNode(children[0])) 
// }

method Test() {
    var emptychild := new RoseTree[0];
    var D := new RoseTree(1,"D", emptychild);
    var B := new RoseTree(1,"B", emptychild);
}

/*
1
2 3 4 
5 - 6 7

{1,2,3,4,5,6,7}
{1,2,3,4,5,6,7} - {4,6,7} = {1,2,3,5}
{1,2,3,4,5,6,7} - {3,4,6,7} = {1,2,5}
{1,2,3,4,5,6,7} - {2,5,3,4,6,7} = {1}


*/