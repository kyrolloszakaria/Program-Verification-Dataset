predicate P(i: int)
predicate Q(i: int)

lemma PHoldEvenly()
  ensures  forall i {:trigger Q(i)} :: P(i) ==> P(i + 2) && Q(i)
//   ensures  forall i {:trigger P(i)} :: P(i) ==> P(i + 2) && Q(i) // prove PHoldsForTwo when using P as the trigger
//   ensures  forall i  :: P(i) ==> P(i + 2) && Q(i) // prove PHoldsForTwo automatically because /autoTriggers determines all possible triggers
//    ensures  forall i {:trigger Q(i)} {:trigger P(i)} :: P(i) ==> P(i + 2) && Q(i) // 

lemma PHoldsForTwo()
  ensures forall i :: P(i) ==> P(i + 4)
{
  forall j: int
    ensures P(j) ==> P(j + 4)
  {
    if P(j) {
      assert P(j); // Trivial assertion
      
      PHoldEvenly();
      // Invoking the lemma assumes `forall i :: P(i) ==> P(i + 4)`,
      // but it's not instantiated yet
      
      // The verifier sees `Q(j)`, so it instantiates
      // `forall i :: P(i) ==> P(i + 4)` with `j`
      // and we get the axiom `P(j) ==> P(j + 2) && Q(j)`
      assert Q(j);     // hence it can prove `Q(j)`
      assert P(j + 2); //   and it can prove `P(j + 2)`
    //   assert Q(j+2);     //can prove with this because not Q(i) == Q(j+2) tells pHoldEvenly that q is satisfied, verifier sees the trigger
      assert P(j + 4); // But it cannot prove this
      // because it did not instantiate `forall i :: P(i) ==> P(i + 4)` with `j+2`
    }
  }
}