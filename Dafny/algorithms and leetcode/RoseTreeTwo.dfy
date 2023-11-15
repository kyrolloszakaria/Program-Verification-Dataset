datatype RoseTree = Node(children: seq<RoseTree>)

function height(r: RoseTree): int
{
  if r.children == [] then
    1
  else
    var c := set i | 0 <= i < |r.children| :: height(r.children[i]);
    assert height(r.children[0]) in c;
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