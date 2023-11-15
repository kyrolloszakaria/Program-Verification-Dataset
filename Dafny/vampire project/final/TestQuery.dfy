/* 
 * Tests for Query
 * Verification time: < 3 seconds 
 * Verified on CSE Dafny 1.9.7
 */

include "Query.dfy"

method TestQueryBloodByTypeBase1()
{
    var a1 := new Blood[0];
    
    var r1 := queryBloodByType(a1, BM);
    assert r1.Length == 0;
    assert r1.Length != 1;
    
    var r2 := queryBloodByType(a1, AP);
    assert r2.Length == 0;
    assert r2.Length != 1;
}

method TestQueryBloodByType1()
{
    var a1 := new Blood[4];
    a1[0] := new Blood(AP,  "John Smith", 1234567, "UNSW Hospital", true);
    a1[1] := new Blood(AP,  "John Smith", 1234567, "UNSW Hospital", true);
    a1[2] := new Blood(BM,  "John Smith", 1234567, "Sentry Blood",  true);
    a1[3] := new Blood(ABP, "John Smith", 1234567, "UNSW Hospital", true);
    assert a1[0].GetBloodType() == AP;
    assert a1[1].GetBloodType() == AP;
    assert a1[2].GetBloodType() == BM;
    assert a1[3].GetBloodType() == ABP;
    
    var r1 := queryBloodByType(a1, BM);
    assert r1.Length == 1;
    assert r1.Length != 2;
    assert r1[0].GetBloodType() == BM;
    assert r1[0].GetLocationAcquired() == "Sentry Blood";
}

method TestQueryBloodByType2()
{
    var a1 := new Blood[4];
    a1[0] := new Blood(AP, "John Smith", 1234567, "UNSW Hospital", true);
    a1[1] := new Blood(AP, "John Smith", 1234567, "UNSW Hospital", true);
    a1[2] := new Blood(AP, "John Smith", 1234567, "Sentry Blood",  true);
    a1[3] := new Blood(AP, "John Smith", 1234567, "UNSW Hospital", true);
    assert a1[0].GetBloodType() == AP;
    assert a1[1].GetBloodType() == AP;
    assert a1[2].GetBloodType() == AP;
    assert a1[3].GetBloodType() == AP;
    
    var r1 := queryBloodByType(a1, BM);
    assert r1.Length == 0;
    assert r1.Length != 1;
    
    var r2 := queryBloodByType(a1, AP);
    assert r2.Length == 4;
    assert r2.Length != 5;
}

method TestQueryBloodByDateBase1()
{
    var a1 := new Blood[0];
    
    var r1 := queryBloodByDate(a1, 0, 99999999);
    assert r1.Length == 0;
    assert r1.Length != 1;
}

method TestQueryBloodByDate1()
{
    var a1 := new Blood[4];
    a1[0] := new Blood(AP,  "John Smith", 222, "UNSW Hospital", true);
    a1[1] := new Blood(AP,  "John Smith", 111, "UNSW Hospital", true);
    a1[2] := new Blood(BM,  "John Smith", 444, "Sentry Blood",  true);
    a1[3] := new Blood(ABP, "John Smith", 333, "UNSW Hospital", true);
    assert a1[0].GetBloodType() == AP;
    assert a1[1].GetBloodType() == AP;
    assert a1[2].GetBloodType() == BM;
    assert a1[3].GetBloodType() == ABP;
    
    var r1 := queryBloodByDate(a1, 0, 233);
    assert r1.Length == 2;
    assert r1.Length != 1;
    assert r1[0].GetBloodType() == AP;
    assert r1[0].GetDateDonated() == 222;
    assert r1[1].GetBloodType() == AP;
    assert r1[1].GetDateDonated() == 111;
}
