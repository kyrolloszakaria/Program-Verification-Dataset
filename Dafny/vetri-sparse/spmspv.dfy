function sum(X_val : array<int>, X_crd : array<nat>,
             v_val : array<int>, v_crd : array<nat>, kX : nat, kV : nat, pX_end : nat, pV_end : nat) : (s : int) 
  reads X_val, X_crd
  requires X_val.Length == X_crd.Length
  requires pX_end <= X_crd.Length
  requires 0 <= kX <= X_crd.Length

  reads v_crd, v_val
  requires v_val.Length == v_crd.Length
  requires pV_end <= v_crd.Length
  requires 0 <= kV <= v_crd.Length

  decreases pX_end + pV_end - (kX + kV)
  {
    if pV_end <= kV || pX_end <= kX then 
      0
    else if X_crd[kX] == v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV] * X_val[kX]
    else if X_crd[kX] < v_crd[kV] then 
      sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    else sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
  }

function min(x : nat, y : nat) : nat {
  if x <= y then x else y
}

method SpMSpV(X_val : array<int>, X_crd : array<nat>, X_pos : array<nat>,
              v_val : array<int>, v_crd : array<nat>) returns (y : array<int>)
  // X requirments 
  requires X_pos.Length >= 1
  requires X_val.Length == X_crd.Length
  requires forall i, j :: 0 <= i < j < X_pos.Length ==> X_pos[i] <= X_pos[j];
  requires forall i :: 0 <= i < X_pos.Length ==> 0 <= X_pos[i] <= X_val.Length

  // v requirments
  requires v_val.Length == v_crd.Length

  ensures y.Length + 1 == X_pos.Length
  ensures 
    forall i :: 0 <= i < y.Length ==>
      y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], 0, X_pos[i+1], v_crd.Length)
  {
    var N : nat := X_pos.Length - 1;
    y := new int[N](i => 0);

    var n : nat := 0;
    var kX , pX_end : nat;
    var kV , pV_end : nat;
    var kX0, kV0    : nat;
    var k : nat;

    while n < N
      invariant n <= y.Length
      invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], 0, X_pos[i+1], v_val.Length)
      invariant forall i :: n <= i < y.Length ==> y[i] == 0
      { 
        kX     := X_pos[n];
        pX_end := X_pos[n + 1];
        kV     := 0;
        pV_end := v_crd.Length;

        while (kX < pX_end && kV < pV_end) 
        invariant X_pos[n] <= kX <= pX_end
        invariant 0 <= kV <= pV_end
        invariant forall i :: n < i < y.Length ==> y[i] == 0
        invariant forall i :: 0 <= i < n ==> y[i] == sum(X_val, X_crd, v_val, v_crd, X_pos[i], 0, X_pos[i+1], pV_end)
        invariant y[n] + sum(X_val, X_crd, v_val, v_crd, kX, kV, pX_end, pV_end) == sum(X_val, X_crd, v_val, v_crd, X_pos[n], 0, pX_end, pV_end)
        decreases pX_end + pV_end - (kX + kV)
          {
            kX0 := X_crd[kX];
            kV0 := v_crd[kV];
            k := min(kV0, kX0);
            if (kX0 == k && kV0 == k) {
              y[n] := y[n] + X_val[kX] * v_val[kV];
              kX := kX + 1;
              kV := kV + 1;
            } else if (kX0 == k) {
              kX := kX + 1;
            } else if (kV0 == k) {
              kV := kV + 1;
            }
          }
        n := n + 1;
      }
  }

function max(x : nat, y : nat) : nat {
  if x >= y then x else y
}

method Main() {
  var X_val := new int[4](i => 1);
  var X_crd := new nat[4](i => if i <= 3 then (3 - i) * 2 else 0);
  var X_pos := new nat[9];
  X_pos[0] := 0;
  X_pos[1] := 1;
  X_pos[2] := 1;
  X_pos[3] := 2;
  X_pos[4] := 2;
  X_pos[5] := 3;
  X_pos[6] := 3;
  X_pos[7] := 4;
  X_pos[8] := 4;

  var v_val := new int[4](i => 30 + i);
  var v_crd := new nat[4](i => i * 2);

  var y := SpMSpV(
    X_val,
    X_crd,
    X_pos,
    v_val,
    v_crd
  );

  var i := 0;
  while i < 8 { print y[i]; print "; "; i := i + 1; }
}
