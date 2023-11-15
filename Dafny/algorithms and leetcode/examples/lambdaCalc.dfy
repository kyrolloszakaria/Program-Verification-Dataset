datatype Nat = Zero | Succ(Pred: Nat)

function add(m: Nat, n: Nat) : Nat
decreases m
{
    match m
    case Zero => n
    case Succ(m') => Succ(add(m', n))
}

function multiply(m: Nat, n: Nat): Nat
  decreases m
{
  match m
    case Zero => Zero
    case Succ(Zero) => n
    case Succ(p) => add(n, multiply(p, n))
}

lemma CommAdd(m: Nat, n: Nat)
ensures add(m,n) == add(n, m)
{
    match m
    case Zero => Add1(n);
    case Succ(m') => CommAdd(m', n);
}

lemma Multiply1(m: Nat)
decreases m
// ensures multiply(m, Zero) == Zero
ensures multiply(m, Succ(Zero)) == m
{
//
}
// a(b + c) = ab + ac;
lemma distributiveLaw(a: Nat, b: Nat, c: Nat)
    ensures multiply(a, add(b,c)) == add(multiply(a,b), multiply(a,c))
{
    if b == Zero {

    }

}
/*
   m * n 
== S m' * n
== n + m' * n
{ using CommMulti property}
== n + n * m'
{ using distributive property }
== n * (1 + m')
== n * m
*/
// lemma CommMult(m: Nat, n: Nat)
//   ensures multiply(m, n) == multiply(n, m)
// {
//   match m
//     case Zero => {}
//     case Succ(Zero) => Multiply1(n);
//     case Succ(m') => {
//       calc {
//         multiply(Succ(m'), n);
//         // defintion of multiply
//         add(n, multiply(m', n));
//         { CommMult(m', n); }
//         add(n, multiply(n, m'));
//         { Multiply1(n); }
//         add(multiply(n, Succ(Zero)), multiply(n, m'));
//         // TODO use distributive law
//       }
//     }
// }