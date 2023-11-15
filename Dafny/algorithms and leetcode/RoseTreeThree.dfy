class RoseTree {
    var NodeType: int
    var id: string
    var children: array<RoseTree>
    ghost var repr: set<object>

    predicate Valid()
      reads this, repr
      decreases repr
    {
      && this in repr
      && children in repr
      && (forall i | 0 <= i < children.Length :: 
            children[i] in repr 
          && children[i].repr <= repr 
          && this !in children[i].repr 
          && children[i].Valid())
    }

    constructor(nt: int, id: string, children: array<RoseTree>) 
      requires forall i | 0 <= i < children.Length :: children[i].Valid()
      ensures Valid()
      ensures this.id == id
      ensures this.NodeType == nt
      ensures this.children == children
    {
        this.NodeType := nt;
        this.id := id;
        this.children := children;
        this.repr := {this, children} + 
          (set i | 0 <= i < children.Length :: children[i]) +
          (set x, i | 0 <= i < children.Length && x in children[i].repr :: x);
    }
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

function height(node: RoseTree): nat
  requires node.Valid()
  reads node.repr
{
  if node.children.Length == 0 then 
    1 
  else 
    var c := set i | 0 <= i < node.children.Length :: height(node.children[i]);
    assert height(node.children[0]) in c;
    assert c != {};
    SetMax(c) + 1
}

method Test() {
    var children: array<RoseTree> := new RoseTree[0];
    var example := new RoseTree(1,"1", children);
    
    var childrentwo: array<RoseTree> := new RoseTree[0];
    var exampletwo := new RoseTree(1,"1", childrentwo);

    assert example != exampletwo;
    assert example.id == "1";
    assert example.NodeType == 1;
    assert example.children != exampletwo.children;
}