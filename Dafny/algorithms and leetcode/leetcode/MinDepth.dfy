
datatype TreeNode = Nil | Cons(val: nat, left: TreeNode, right: TreeNode)

predicate isPath(paths: seq<TreeNode>, root: TreeNode) 
{

    if |paths| == 0 then false else match paths[0] {
        case Nil => false
        case Cons(val, left, right) => if |paths| == 1 then root == paths[0] else root == paths[0] && (isPath(paths[1..], left) || isPath(paths[1..], right))
    }
}

function TreeSet(root: TreeNode): set<TreeNode> {
    match root {
        case Nil => {}
        case Cons(val, left, right) => TreeSet(left)+{root}+TreeSet(right)
    }
}

function ChildSet(root: TreeNode): set<TreeNode> {
    match root {
        case Nil => {}
        case Cons(val, left, right) => {left}+ChildSet(left)+{right}+ChildSet(right)
    }
}

function method max(a:int,b: int): int {
    if a > b then a else b
}

function method min(a:int,b: int): int {
    if a > b then b else a
}

function method boundedMin(a: int, b: int): int 
    ensures a > 0 && b == 0 ==> boundedMin(a,b) == a
    ensures a == 0 && b > 0 ==> boundedMin(a,b) == b
    ensures a > 0 && b > 0 ==> boundedMin(a,b) == (if a < b then a else b)
{
    if a == 0 then b else if b == 0 then a else min(a,b)
}

function TreeHeight(root: TreeNode): nat {
    match root {
        case Nil => 0
        case Cons(val, Nil, Nil) => 1
        case Cons(val, left, right) => 1 + max(TreeHeight(left), TreeHeight(right))
    }
}

method minDepth(root: TreeNode) returns (depth: nat) 
    requires forall node :: node in TreeSet(root) ==> node !in ChildSet(node)
    ensures depth > 0 ==> exists p: seq<TreeNode> :: isPath(p, root) && |p| == depth
    // ensures depth > 0 ==> forall ps: seq<TreeNode> :: isPath(ps, root) ==> depth <= |ps|
{
    if root == Nil {
        return 0;
    }

    if root.left == Nil && root.right == Nil {
        assert isPath([root], root) && |[root]| == 1;
        // allSeqsTreenode(root);
        return 1;
        // assert depth == 1;
        assert forall ps: seq<TreeNode> :: isPath(ps, root) ==> depth <= |ps|;
    }
    var leftDepth := minDepth(root.left);
    var rightDepth := minDepth(root.right);
    if leftDepth > 0 {
        // ghost var q: seq<TreeNode> :| isPath(q, root.left) && |q| == leftDepth && forall ps: seq<TreeNode> :: isPath(ps, root.left) ==> leftDepth <= |ps|;
        ghost var q: seq<TreeNode> :| isPath(q, root.left) && |q| == leftDepth;
        assert isPath([root]+q, root) && |[root]+q| == 1 + leftDepth;
        // assert forall ps: seq<TreeNode> :: isPath(ps, root.left) ==> isPath([root]+ps, root) && 1+leftDepth <= |[root]+ps|;
    }
    if rightDepth > 0 {
        ghost var p: seq<TreeNode> :| isPath(p, root.right) && |p| == rightDepth;
        assert isPath([root]+p, root) && |[root]+p| == 1 + rightDepth;
        // assert forall ps: seq<TreeNode> :: isPath(ps, root.right) ==> isPath([root]+ps, root) && 1+rightDepth <= |[root]+ps|;
    }
    // if leftDepth > 0 && rightDepth > 0 {
    //     assert (forall pls: seq<TreeNode> :: isPath(pls, root.left) ==> leftDepth == |pls| && isPath([root]+pls, root) && 1+leftDepth <= |[root]+pls| && 1+boundedMin(leftDepth, rightDepth) <= 1+leftDepth) &&
    //    (forall prs: seq<TreeNode> :: isPath(prs, root.right) ==> rightDepth == |prs| && isPath([root]+prs, root) && 1+rightDepth <= |[root]+prs| && 1+boundedMin(leftDepth, rightDepth) <= 1+rightDepth) ==> 
    //    forall ps: seq<TreeNode> :: isPath(ps, root) ==> 1 + boundedMin(leftDepth, rightDepth) <= |ps|;
    // }

    return 1 + boundedMin(leftDepth, rightDepth);
}

// lemma MinDepthMinimal(root: TreeNode, path: seq<TreeNode>, depth: nat) 
//     requires isPath(path, root)
//     requires depth == |path| && depth > 0
//     ensures forall ps: seq<TreeNode> :: isPath(ps, root) && ps != path ==> depth <= |ps|
// {
//     var what := minDepth(root);
// }

/**
    showing minimum
    if both |ps| == |p| == 1 then true
    assume that another path (ps, root) exists and it is not equal to path(p,root) and it is less than |p|;
    assume forall isPath(ps, root) ==> |p| <= |ps|

    then either p && ps include root and root.left in which case mindDepth root.left == root.right
    then either p && ps include root and root.right
    then either p includes root.right and ps includes root.left
    |ps| < |p| ==> |ps|+1 < |p| + 1
    rightDepth == |ps|
    leftDepth == |p|
    
    then either p includes root.left and ps includes root.right
    |ps| < |p| ==> |ps|+1 < |p| + 1
    rightDepth == |p|
    leftDepth == |ps|

 (!forall ps: seq<TreeNode> :: isPath(ps, root) ==> depth <= |ps|) 
exists ps(ps root) && depth > |ps|


 */
lemma allSeqsTreenode(node: TreeNode)
    requires node != Nil && node.left == Nil && node.right == Nil
    ensures (iset ps: seq<TreeNode> | isPath(ps, node)) == iset{[node]}
    ensures forall ps: seq<TreeNode> :: isPath(ps, node) ==> 1 <= |ps|
{
    if !((iset ps: seq<TreeNode> | isPath(ps, node)) == iset{[node]}) {
        var xs :| xs != [node] && isPath(xs, node);
        assert xs in iset ps: seq<TreeNode> | isPath(ps, node);
        assert |xs| > 0;
        if xs[0] != node {
            assert !isPath(xs, node);
        }
        else if |xs| > 1 && xs[0] == node && xs[1] != node {
            assert !isPath(xs, node);
        }
        assert false;
    }
}

lemma AllTreNode(node: TreeNode)
    requires node != Nil
    requires forall pls: seq<TreeNode> :: isPath(pls, node.left)
    requires forall prs: seq<TreeNode> :: isPath(prs, node.left)
    ensures forall ps: seq<TreeNode> :: isPath(ps, node)
{
    var xl: seq<TreeNode> :| isPath(xl, node.left);
    var xr: seq<TreeNode> :| isPath(xr, node.right);
    assert isPath([node]+xl, node);
    assert isPath([node]+xr, node);
}

method Test() {
    var t := Nil;
    assert TreeHeight(t) == 0;
    var t1 := Cons(3,Nil, Nil);
    assert TreeHeight(t1) == 1;
    var t2 := Cons(3,Nil, Cons(4, Nil, Nil));
    assert TreeHeight(t2) == 2;
}