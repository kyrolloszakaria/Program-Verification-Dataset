include "QueryBloodInventory.dfy"

class Blood
{
    // add more fields if need be
    var bloodType: string;
    var donorName: string;
    // linux epoch time, using integer to represent seconds from 1980? 
    var dateDonated: int;
    
    // blood must be of valid type
    predicate Valid()
    reads this
    {
        (bloodType == "A+" || bloodType == "A-" || bloodType == "B+" || bloodType == "B-" ||
         bloodType == "O+" || bloodType == "O-" || bloodType == "AB+" || bloodType == "AB-")
    }

    constructor(cbloodType: string, cdonorName: string, cdateDonated: int)
    modifies this
    requires (cbloodType == "A+" || cbloodType == "A-" || cbloodType == "B+" || cbloodType == "B-" ||
         cbloodType == "O+" || cbloodType == "O-" || cbloodType == "AB+" || cbloodType == "AB-")
    ensures Valid()
    ensures bloodType == cbloodType && donorName == cdonorName && dateDonated == cdateDonated
    {
        bloodType := cbloodType;
        donorName := cdonorName;
        dateDonated := cdateDonated;
    }

    function method GetBloodType(): string
    reads this
    ensures GetBloodType() == bloodType
    {
        bloodType
    }

    function method GetDonorName(): string
    reads this
    ensures GetDonorName() == donorName
    {
        donorName
    }

    function method GetDateDonated(): int
    reads this
    ensures GetDateDonated() == dateDonated
    {
        dateDonated
    }

    predicate method IsExpired(currentDate: int)
    reads this
    {
        currentDate > dateDonated + 42
    }

    method PrettyPrint()
    requires Valid() ensures Valid()
    {
        print "Blood from:  ", donorName, "\nReceived on: ", dateDonated, "\nBlood type:  ", bloodType;
    }
} // end of Blood class

method Main()
{
    var bobsBlood := new Blood("A-", "bob", 12);
    
    assert bobsBlood.GetBloodType() == "A-";
    assert bobsBlood.GetDonorName() == "bob";
    assert bobsBlood.GetDateDonated() == 12;
    
    bobsBlood.PrettyPrint();

    // Query
    var inv := new Blood[4];
    inv[0] := new Blood("B+", "Ava", 9);
    inv[1] := new Blood("A-", "Bob", 12);
    inv[2] := new Blood("O+", "Cal", 12);
    inv[3] := new Blood("AB+", "Deb", 13);
    
    // (currently only seems to work with the last item in the inv)
    // maybe change bloodType to an enumeration?
    var r := queryBloodByType(inv, "AB+");
    assert r.Length == 1;
    assert r[0].GetDonorName() == "Deb";
    
    assert countBloodByDate(inv, 10, 12) == 2;
    assert countBloodByType(inv, "AB+") == 1;
    print "\nQuery successful\n";
}

