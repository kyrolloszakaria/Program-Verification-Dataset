include "Blood.dfy"
class BloodInventory
{
    var bloodInventory: array<Blood>;
    ghost var shadowBloodInventory: seq<string>;
    var threshold: int;

    predicate Valid()
    requires bloodInventory != null
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    reads this, this`shadowBloodInventory, this.bloodInventory, set i | 0 <= i < bloodInventory.Length :: bloodInventory[i]
    {
        |shadowBloodInventory| == bloodInventory.Length &&
        forall i :: 0 <= i < |shadowBloodInventory| ==> validBloodType(shadowBloodInventory[i]) && 
        forall i  :: 0 <= i < |shadowBloodInventory| ==> shadowBloodInventory[i] == bloodInventory[i].GetBloodType()
    } 

    constructor()
    modifies this
    ensures bloodInventory != null
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures shadowBloodInventory == []
    ensures fresh(bloodInventory)
    ensures bloodInventory.Length == 0
    ensures threshold == 0
    ensures Valid()
    {
        bloodInventory := new Blood[0];
        shadowBloodInventory := [];
        threshold := 0;
    }

    method ModifyThreshold(newThreshold: int)
    modifies this`threshold
    requires newThreshold >= 0
    requires bloodInventory != null
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures bloodInventory != null
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures threshold == newThreshold
    requires Valid() ensures Valid()
    {
        threshold := newThreshold;
    }

    function GetBloodCountForBloodTypeVerification(bloodType: string, indexToCountTo: int ): int
    decreases indexToCountTo
    reads this, this.bloodInventory, set i | 0 <= i < this.bloodInventory.Length :: bloodInventory[i]
    requires bloodInventory != null
    requires indexToCountTo < bloodInventory.Length
    requires validBloodType(bloodType)
    {
        if indexToCountTo < 0 || bloodInventory[indexToCountTo] == null
        then 
            0
        else
            if bloodInventory[indexToCountTo].GetBloodType() == bloodType
            then
                1 + GetBloodCountForBloodTypeVerification(bloodType, indexToCountTo - 1)
            else
                GetBloodCountForBloodTypeVerification(bloodType, indexToCountTo - 1)

    }

    predicate VerifyLengths()
    requires bloodInventory != null
    reads this
    {
        bloodInventory.Length == |shadowBloodInventory|
    }

    function GetShadowArray(): seq<string>
    reads this
    {
        shadowBloodInventory
    }

    method GetBloodCountForBloodTypeExecution(bloodType: string) returns (count: int)
    requires validBloodType(bloodType)
    requires bloodInventory != null
    requires bloodInventory.Length == |shadowBloodInventory|
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i].GetBloodType() == shadowBloodInventory[i])
    ensures bloodInventory != null
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures bloodInventory == old(bloodInventory)
    ensures count == GetBloodCountForBloodTypeVerification(bloodType, bloodInventory.Length - 1)
    requires Valid() ensures Valid()
    {
        count := 0;
        var i := 0;

        while i < bloodInventory.Length
        invariant 0 <= i <= bloodInventory.Length
        invariant count == GetBloodCountForBloodTypeVerification(bloodType, i - 1)
        {
            if(bloodInventory[i].GetBloodType() == bloodType)
            {
                count := count + 1;
            }
            i := i + 1;
        }
    }

    function GetSizeVerificaiton(): int
    requires bloodInventory != null
    reads this, this.bloodInventory
    {
        bloodInventory.Length
    }

    function method GetThreshold(): int
    requires bloodInventory != null
    reads this, this.bloodInventory
    {
        threshold
    }

    function GetArrayVerification(): array<Blood>
    reads this
    {
        bloodInventory
    }

    method GetSize() returns (count: int)
    requires bloodInventory != null
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures bloodInventory != null
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures count == bloodInventory.Length
    requires Valid() ensures Valid()
    {
        count := bloodInventory.Length;
    }

    method RemoveExpiredBlood(currentDate: int)
    modifies this, this.bloodInventory
    requires bloodInventory != null
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures  bloodInventory != null
    ensures  forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures  forall i :: 0 <= i < old(bloodInventory.Length) ==> (old(bloodInventory[i]) != null)
    // ensures  bloodInventory[..] == FilterExpiredBlood(old(bloodInventory), old(bloodInventory.Length), currentDate)
    requires Valid()
    ensures  Valid()
    {
        var nonExpiredBlood := new Blood[bloodInventory.Length];
        ghost var nonExpiredShadow: seq<string> := [];

        var i := 0; // index for old blood inventory
        var j := 0; // index for new blood inventory
        while i < bloodInventory.Length
            invariant bloodInventory != null
            invariant 0 <= j <= i <= bloodInventory.Length
            invariant forall k :: 0 <= k < bloodInventory.Length ==> (bloodInventory[k] != null)
            invariant Valid()
            invariant bloodInventory == old(bloodInventory)
            invariant bloodInventory[..] == old(bloodInventory[..])
            invariant nonExpiredBlood[..j] == FilterExpiredBlood(bloodInventory, i, currentDate)
            invariant forall k :: 0 <= k < j ==> nonExpiredBlood[k] != null
            invariant |nonExpiredShadow| == j
            invariant forall k :: 0 <= k < |nonExpiredShadow| ==> validBloodType(nonExpiredShadow[k])
            invariant forall k :: 0 <= k < |nonExpiredShadow| ==> nonExpiredShadow[k] == nonExpiredBlood[k].GetBloodType() 
        {
            if !bloodInventory[i].IsExpired(currentDate) {
                nonExpiredBlood[j] := bloodInventory[i];
                nonExpiredShadow := nonExpiredShadow + [shadowBloodInventory[i]];
                j := j + 1;
            }
            i := i + 1;
        }

        var newBloodInventory := new Blood[j];
        forall k | 0 <= k < j
        {
            newBloodInventory[k] := nonExpiredBlood[k];
        }

        bloodInventory := newBloodInventory;
        shadowBloodInventory := nonExpiredShadow;

        assert bloodInventory[..] == FilterExpiredBlood(old(bloodInventory), old(bloodInventory.Length), currentDate);
    }

    method RemoveBloodAtIndex(idx: int) returns (blood: Blood)
    modifies this, this.bloodInventory
    requires bloodInventory != null
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    requires 0 <= idx < bloodInventory.Length
    ensures  bloodInventory != null
    ensures  forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures  bloodInventory.Length == old(bloodInventory.Length) - 1
    ensures  forall i :: 0 <= i < idx ==> bloodInventory[i] == old(bloodInventory[i])
    ensures  forall i :: idx < i < bloodInventory.Length ==> bloodInventory[i - 1] == old(bloodInventory[i])
    ensures  blood == old(bloodInventory[idx])
    ensures  fresh(bloodInventory)
    requires Valid()
    ensures  Valid()
    {
        var newBloodInventory := new Blood[bloodInventory.Length - 1];
        blood := bloodInventory[idx];

        forall i | 0 <= i < idx
        {
            newBloodInventory[i] := bloodInventory[i];
        }

        forall i | idx < i < bloodInventory.Length
        {
            newBloodInventory[i - 1] := bloodInventory[i];
        }
        
        bloodInventory := newBloodInventory;
        shadowBloodInventory := shadowBloodInventory[..idx] + shadowBloodInventory[idx + 1..];
    }

    // we can assume that we remove from our array sorted by date using our merge sort
    // to take out the oldest blood to minimise wastage
    method removeBlood(bloodType: string) returns (blood: Blood, indexOfRemoval: int)
    modifies this, this.bloodInventory
    requires bloodInventory != null
    requires bloodInventory.Length > 0
    requires |shadowBloodInventory| > 0
    requires validBloodType(bloodType)
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    requires exists i :: 0 <= i < bloodInventory.Length && bloodInventory[i].GetBloodType() == bloodType
    ensures bloodInventory != null 
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures blood == null ==> !(exists i :: 0 <= i < bloodInventory.Length && bloodInventory[i].GetBloodType() == bloodType)
    ensures blood == null ==> bloodInventory.Length == old(bloodInventory.Length) 
    ensures blood == null ==> indexOfRemoval == -1
    ensures blood != null ==> bloodInventory.Length == old(bloodInventory.Length) - 1
    ensures blood != null ==> blood.GetBloodType() == bloodType
    ensures blood != null && (0 <= indexOfRemoval < bloodInventory.Length) ==> shadowBloodInventory == old(shadowBloodInventory)[..indexOfRemoval] + old(shadowBloodInventory)[indexOfRemoval + 1..]
    ensures blood != null && (0 <= indexOfRemoval < bloodInventory.Length) ==> ((forall i :: 0 <= i < indexOfRemoval ==> bloodInventory[i] == old(bloodInventory[i])) && 
                                                                               (forall i :: indexOfRemoval < i < bloodInventory.Length ==> bloodInventory[i - 1] == old(bloodInventory[i])))
    requires Valid() ensures Valid()
    {
        blood := null;
        indexOfRemoval := -1;
        var removedFromInventory : array<Blood> := new Blood[bloodInventory.Length - 1];
        var i := 0;        
        while i < bloodInventory.Length
        invariant 0 <= i <= bloodInventory.Length
        invariant forall j :: 0 <= j < i ==> (bloodInventory[j].GetBloodType() != bloodType) 
        {
            if(bloodInventory[i].GetBloodType() == bloodType)
            {
                // we will remove it from the array
                shadowBloodInventory := shadowBloodInventory[..i] + shadowBloodInventory[i+1..];
                blood := bloodInventory[i];
                indexOfRemoval := i;
                var addLower := 0;
                var addUpper := i;
                forall k | 0 <= k < i 
                {
                    removedFromInventory[k] := bloodInventory[k];
                }
                forall k | i < k < bloodInventory.Length 
                {
                    removedFromInventory[k - 1] := bloodInventory[k];
                }
                bloodInventory := removedFromInventory;
                return;
            }
            i := i + 1;
        }
    }

    method AddBlood(blood: Blood) returns (b: bool)
    modifies this, this.bloodInventory
    requires bloodInventory != null
    requires blood != null
    requires validBloodType(blood.GetBloodType())
    requires forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures bloodInventory != null
    ensures forall i :: 0 <= i < bloodInventory.Length ==> (bloodInventory[i] != null)
    ensures bloodInventory.Length == old(bloodInventory.Length) + 1
    ensures forall i :: 0 <= i < old(bloodInventory.Length) ==> (bloodInventory[i] == old(bloodInventory[i]))
    ensures shadowBloodInventory == old(shadowBloodInventory) + [blood.GetBloodType()]
    ensures bloodInventory[old(bloodInventory.Length)] == blood
    requires Valid() ensures Valid()
    {
        var addedToInventory: array<Blood> := new Blood[bloodInventory.Length + 1];
        forall i | 0 <= i < bloodInventory.Length
        {
            addedToInventory[i] := bloodInventory[i];
        }
        // add the new blood to the inventory
        addedToInventory[bloodInventory.Length] := blood;
        bloodInventory := addedToInventory;
        shadowBloodInventory := shadowBloodInventory + [blood.GetBloodType()];
    }
} // end of BloodInventory class

predicate validBloodType(bloodType: string)
{
    bloodType == "A+" || bloodType == "B+" || bloodType == "O+" || bloodType == "AB+" ||
    bloodType == "A-" || bloodType == "B-" || bloodType == "O-" || bloodType == "AB-"
}

function FilterExpiredBlood(a: array<Blood>, end: nat, currentDate: int): seq<Blood>
reads     a
reads     set i | 0 <= i < end :: a[i]
requires  a != null
requires  0 <= end <= a.Length
requires  forall i :: 0 <= i < end ==> a[i] != null
decreases end
{
    if end < 1 then
        []
    else if !a[end - 1].IsExpired(currentDate) then
        FilterExpiredBlood(a, end - 1, currentDate) + [a[end - 1]]
    else
        FilterExpiredBlood(a, end - 1, currentDate)
}
