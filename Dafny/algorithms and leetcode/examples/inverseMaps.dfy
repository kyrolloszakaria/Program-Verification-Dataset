// union on maps does not seem to be defined in Dafny
function union<U(!new), V>(m: map<U,V>, m': map<U,V>): map<U,V>
	requires m.Keys !! m'.Keys; // disjoint
	ensures forall i :: i in union(m, m') <==> i in m || i in m';
	ensures forall i :: i in m ==> union(m, m')[i] == m[i];
	ensures forall i :: i in m' ==> union(m, m')[i] == m'[i];
{
	map i | i in (domain(m) + domain(m')) :: if i in m then m[i] else m'[i]
}
 
// the domain of a map is the set of its keys  
function domain<U,V>(m: map<U,V>) : set<U>
	ensures domain(m) == set u : U | u in m :: u;
	ensures forall u :: u in domain(m) ==> u in m;
{
		set u : U | u in m :: u
}
 
// the domain of a map is the set of its values
function range<U,V>(m: map<U,V>) : set<V>
	ensures range(m) == set u : U | u in m :: m[u];
	ensures forall v :: v in range(m) ==> exists u :: u in m && m[u] == v;
{
	set u : U | u in m :: m[u]
}
 
// here a map m is smaller than m' if the domain of m is smaller than 
// the domain of m', and every key mapped in m' is mapped to the same 
// value that it is in m.   
predicate mapSmaller<U,V>(m: map<U,V>, m': map<U,V>)
	ensures mapSmaller(m,m') ==> 
		(forall u :: u in domain(m) ==> u in domain(m'));
{
	forall a :: a in m ==> a in m' && m[a] == m'[a]
}
 
// map m is the inverse of m' if for every key->value in m
// there is value->key in m', and vice versa
predicate mapsAreInverse<U,V>(m: map<U,V>, m': map<V,U>)
{
	(forall a :: a in m ==> m[a] in m' && m'[m[a]] == a) &&
	(forall a :: a in m' ==> m'[a] in m && m[m'[a]] == a) 
}
 
// map m is injective if no two keys map to the same value	
predicate mapInjective<U,V>(m: map<U,V>)
{
	forall a,b :: a in m && b in m ==> a != b ==> m[a] != m[b]
}
 
// here we prove that injective map m has an inverse, we prove
// this by calculating the inverse for an arbitrary injective map.
// maps are finite in Dafny so we have no termination problem
lemma invertMap<U(!new),V>(m: map<U,V>) returns (m': map<V,U>)
	requires mapInjective(m);
	ensures mapsAreInverse(m,m');
{
	var R := m;     // part of m left to invert
	var S := map[]; // part of m already inverted
	var I := map[]; // inverted S
 
	while R != map[]       // while something left to invert
		decreases R;   // each loop iteration makes R smaller
		invariant mapSmaller(R, m);
		invariant mapSmaller(S, m);
		invariant R.Keys !! S.Keys; // disjoint
		invariant m == union(R, S);
		invariant mapsAreInverse(S,I);
	{
		var a :| a in R;   // take something arbitrary in R
		var v := R[a];
		var r := map i | i in R && i != a :: R[i];  // remove a from R
		I := I[v:=a];
		S := S[a:=v];
		R := r;
	}
	m' := I;  // R is empty, S == m, I inverts S
}
 
// here we prove that every injective map has an inverse  
lemma injectiveMapHasInverse<U(!new),V>(m: map<U,V>)
	requires mapInjective(m);
	ensures exists m' :: mapsAreInverse(m, m'); 
{
    var m' := invertMap(m);
}
 
// here we prove that no non-injective map has an inverse  
lemma nonInjectiveMapHasNoInverse<U,V>(m: map<U,V>)
	requires !mapInjective(m);
	ensures !(exists m' :: mapsAreInverse(m, m')); 
{ }
 
// here we prove that if m' is the inverse of m, then the domain of m
// is the range of m', and vice versa  
lemma invertingMapSwapsDomainAndRange<U,V>(m: map<U,V>, m': map<V,U>)
	requires mapsAreInverse(m, m');
	ensures domain(m) == range(m') && domain(m') == range(m);
{ }
 
// a map m strictly smaller than map m' has fewer elements in its domain 
lemma strictlySmallerMapHasFewerElementsInItsDomain<U,V>(m: map<U,V>, m': map<U,V>)
	requires mapSmaller(m,m') && m != m';
	ensures domain(m') - domain(m) != {};
{
	var R,R' := m,m';
	while R != map[]
		decreases R;
		invariant mapSmaller(R,R');
		invariant R != R';
	{
		var a :| a in R && a in R';
		var v := R[a];
 
		var r := map i | i in R && i != a :: R[i];
		var r' := map i | i in R' && i != a :: R'[i];
 
		R := r;
		R' := r';
	}
	assert R == map[];
	assert R' != map[];
 
	assert domain(R) == {};
	assert domain(R') != {};
}
 
function invert<U(!new),V>(m:map<U,V>) : map<V,U>
	requires mapInjective(m); 
	ensures mapsAreInverse(m,invert(m));
{
	injectiveMapHasInverse(m);
 
	var m' :| mapsAreInverse(m,m');
	m'
}