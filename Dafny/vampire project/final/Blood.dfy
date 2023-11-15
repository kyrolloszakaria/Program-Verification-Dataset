/*
 * Blood class
 * Verification time: < 2 seconds
 * Verified on CSE Dafny 1.9.7
 */

include "BloodType.dfy"

class Blood
{
    var bloodType: BloodType;
    var donorName: string;
    var dateDonated: int;
    var locationAcquired: string;
    var tested: bool;
    
    predicate Valid()
        reads this;
    {
        validBloodType(bloodType)
    }

    constructor(bloodType: BloodType, donorName: string, dateDonated: int,
                locationAcquired: string, tested: bool)
        modifies this;
        requires validBloodType(bloodType);
        ensures  Valid();
        ensures  this.bloodType == bloodType;
        ensures  this.donorName == donorName;
        ensures  this.dateDonated == dateDonated;
        ensures  this.locationAcquired == locationAcquired;
        ensures  this.tested == tested;
    {
        this.bloodType := bloodType;
        this.donorName := donorName;
        this.dateDonated := dateDonated;
        this.locationAcquired := locationAcquired;
        this.tested := tested;
    }

    function method GetBloodType(): BloodType
        reads this;
    {
        bloodType
    }

    function method GetDonorName(): string
        reads this;
    {
        donorName
    }

    function method GetDateDonated(): int
        reads this;
    {
        dateDonated
    }

    function method GetLocationAcquired(): string
        reads this;
    {
        locationAcquired
    }

    function method HasBeenTested(): bool
        reads this;
    {
        tested
    }

    predicate method IsExpired(currentDate: int)
        reads this;
    {
        currentDate > dateDonated + 42
    }

    method PrettyPrint()
        requires Valid();
        ensures  Valid();
    {
        print "Blood from:  ",     donorName,   "\n",
              "Received on: Day ", dateDonated, "\n",
              "Blood type:  ",     bloodType,   "\n",
              "Tested:      ",     tested,      "\n";
    }

} // end of Blood class

////////////////////////////////////////////////////////////////////////////////

method PrintBloodArray(a: array<Blood>)
    requires a != null;
    requires forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid();
{
    print "===============================\n";

    var i := 0;
    while i < a.Length
    {
        a[i].PrettyPrint();
        if i < a.Length - 1
        {
            print "-------------------------------\n";
        }
        i := i + 1;
    }

    print "===============================\n";
}

////////////////////////////////////////////////////////////////////////////////

// method Main()
// {
//     TestBlood();
// }

method TestBlood()
{
    var blood := new Blood(AM, "Bob", 12, "Prince of Wales Hospital", true);
    
    assert blood.GetBloodType()   == AM;
    assert blood.GetBloodType()   != AP;
    assert blood.GetDonorName()   == "Bob";
    assert blood.GetDateDonated() == 12;
    assert blood.HasBeenTested()  == true;
    blood.PrettyPrint();
}
