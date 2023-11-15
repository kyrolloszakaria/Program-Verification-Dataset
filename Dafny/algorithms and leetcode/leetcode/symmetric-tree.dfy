/*
/**
 * Definition for a binary tree node.
 * class TreeNode {
 *     val: number
 *     left: TreeNode | null
 *     right: TreeNode | null
 *     constructor(val?: number, left?: TreeNode | null, right?: TreeNode | null) {
 *         this.val = (val===undefined ? 0 : val)
 *         this.left = (left===undefined ? null : left)
 *         this.right = (right===undefined ? null : right)
 *     }
 * }
 */
function isSymmetricHelper(left: TreeNode | null, right: TreeNode | null): boolean {
    if ( left === null && right === null) return true
    return left !== null && right !== null && left.val === right.val && isSymmetricHelper(left.left, right.right) && isSymmetricHelper(left.right, right.left);
}

function isSymmetric(root: TreeNode | null): boolean {
    if ( root == null || root.left === null && root.right === null) return true;

    return isSymmetricHelper(root.left, root.right);
};
Given the root of a binary tree, check whether it is a mirror of itself (i.e., symmetric around its center).
https://leetcode.com/problems/symmetric-tree/description/
*/
include "../lib/binaryTree.dfy"
import opened BinaryTree

 function TreeNodes(root: Tree): set<Tree> {
    match root {
        case Nil => {root}
        case Node(val, left, right) => {root}+TreeNodes(left)+TreeNodes(right)
    }
}

// lemma TreeNodesChildInTreeNodes(root: Tree, child: Tree) 
//     requires root != Nil
//     requires child in TreeNodes(root)
//     ensures TreeNodes(child) <= TreeNodes(root)
// {}

// lemma parentNotInTreeNodes(parent: Tree, root: Tree)
//     requires parent != Nil && parent != root && (parent.left == root || parent.right == root)
//     ensures parent !in TreeNodes(root)
// {
//     if root == Nil {} else {
//         assert TreeNodes(root) == {root}+TreeNodes(root.left)+TreeNodes(root.right);
//         parentNotInTreeNodes(root, root.left);
//         parentNotInTreeNodes(root, root.right);
//         if parent in TreeNodes(root.left) {
//             TreeNodesChildInTreeNodes(root.left, parent);
//         }else if parent in TreeNodes(root.right) {
//             TreeNodesChildInTreeNodes(root.right, parent);
//         }
//     }
// }

predicate validTree(t: Tree) {
    if t.Nil? then true else (t !in TreeNodes(t.left)
        && t !in TreeNodes(t.right)
        && (TreeNodes(t.left)-{Nil}) !! (TreeNodes(t.right)-{Nil})
        && validTree(t.left)
        && validTree(t.right))
}

predicate isLeaf(t: Tree) {
    !t.Nil? && t.left.Nil? && t.right.Nil?
}

lemma ValidTreeChildIsValid(t: Tree, n: Tree) 
    requires validTree(t)
    requires n in TreeNodes(t)
    ensures validTree(n)
{

}


// lemma AllSeparate(root: Tree)
//     requires validTree(root)
//     requires root != Nil
//     ensures forall node :: node in TreeNodes(root) && node != Nil ==> (TreeNodes(node.left)-{Nil}) !! (TreeNodes(node.right)-{Nil})
// {

// }

predicate {:verify } isSymmetricHelper(left: Tree, right: Tree)
    requires validTree(left)
    requires validTree(right)
    ensures left.Nil? && right.Nil? ==> isSymmetricHelper(left, right) == true
    ensures (left.Nil? && !right.Nil?) || (!left.Nil? && right.Nil?) ==> isSymmetricHelper(left, right) == false
    decreases TreeNodes(left)
{
    if left.Nil? && right.Nil? then true else 
        !left.Nil? 
        && !right.Nil? 
        && left.val == right.val 
        && isSymmetricHelper(left.left, right.right) 
        && isSymmetricHelper(left.right, right.left)
}

lemma ValidChildrenMinusRootValid(t: Tree)
    requires validTree(t)
    ensures forall node :: node in TreeNodes(t)-{t} ==> validTree(node)
{

}

lemma conditionalWorks(left: Tree, right: Tree)
    ensures validTree(left) && validTree(right) && isSymmetricHelper(left, right) ==> forall lnode :: validTree(lnode) && lnode in (TreeNodes(left)-{left}) ==> exists rnode :: validTree(rnode) && rnode in TreeNodes(right) && isSymmetricHelper(lnode, rnode)
{
    if validTree(left) && validTree(right) && isSymmetricHelper(left, right) {
        isSymmetricHelperWorks(left, right);
    }
}

lemma {:verify } isSymmetricHelperWorks(left: Tree, right: Tree)
    requires validTree(left)
    requires validTree(right)
    requires isSymmetricHelper(left, right)
    ensures isSymmetricHelper(left, right) ==> forall lnode :: validTree(lnode) && lnode in (TreeNodes(left)-{left}) ==> exists rnode :: validTree(rnode) && rnode in TreeNodes(right) && isSymmetricHelper(lnode, rnode)
{
    if left == Nil && right == Nil {
    } else if left != Nil && right != Nil {
        isSymmetricHelperWorks(left.left, right.right);
        isSymmetricHelperWorks(left.right, right.left);
        ValidChildrenMinusRootValid(left.left);
        ValidChildrenMinusRootValid(left.right);
        forall lnode | lnode in (TreeNodes(left)-{left}) 
            ensures exists rnode :: validTree(rnode) && rnode in TreeNodes(right) && isSymmetricHelper(lnode, rnode)
        {
            ValidTreeChildIsValid(left,lnode);
            if lnode in TreeNodes(left.left) {
                var rnode :| validTree(rnode) && rnode in TreeNodes(right.right) && isSymmetricHelper(lnode, rnode);
            } else if lnode in TreeNodes(left.right) {
                var rnode :| validTree(rnode) &&rnode in TreeNodes(right.left) && isSymmetricHelper(lnode, rnode);
            } else {
                assert false;
            }
        }
    }else{
        assert false;
    }
}

predicate {:verify } isSymmetric(root: Tree)
    requires validTree(root)
    ensures root.Nil? ==> isSymmetric(root) == true
    ensures !root.Nil? && isSymmetric(root) ==> forall lnode :: validTree(lnode) && lnode in TreeNodes(root.left) ==> exists rnode :: validTree(rnode) && rnode in TreeNodes(root.right) && isSymmetricHelper(lnode, rnode)
{
    if root.Nil? || (root.left.Nil? && root.right.Nil?) then true else 
    conditionalWorks(root.left, root.right);
    isSymmetricHelper(root.left, root.right)
}