/* 
 * Black-box tests for Blood Inventory
 * Some of these tests take a *long* time to verify, even with very little data.
 * This  is  likely due to the fact that they are testing a fully-fledged class.
 * The time taken to verify each test method is included in a comment above  the
 * method.
 * All methods were verified on CSE Dafny 1.9.7
 */

include "BloodInventory.dfy"

////////////////////////////////////////////////////////////////////////////////
// Black-box tests for AddBlood                                               //
////////////////////////////////////////////////////////////////////////////////

/**
 * Verification time: ~90 seconds
 */
// method TestAddBlood() 
// {
//     var inv := new BloodInventory();
//     var amt;
    
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 0;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 0;

//     var blood1 := new Blood(AP, "Amy", 2, "Hospital A", true);
//     inv.AddBlood(blood1);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 0;

//     var blood2 := new Blood(BP, "Bob", 5, "Hospital B", true);
//     inv.AddBlood(blood2);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     var blood3 := new Blood(AP, "Cal", 7, "Hospital C", true);
//     inv.AddBlood(blood3);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 2;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     var blood;

//     blood := inv.GetBloodOfType(AP);
//     assert blood[..] == [blood1, blood3];

//     blood := inv.GetBloodOfType(BP);
//     assert blood[..] == [blood2];

//     blood := inv.GetBloodOfType(AM);
//     assert blood[..] == [];
// }

////////////////////////////////////////////////////////////////////////////////
// Black-box tests for RemoveExpiredBlood                                     //
////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects - one expired
 * Verification time: < 4 minutes
 */
// method TestRemoveExpiredBlood1()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 2;

//     inv.RemoveExpiredBlood(44);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     var blood := inv.GetBloodOfType(AP);
//     assert blood[..] == [blood2];
// }

////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects - both expired
 * Verification time: < 15 minutes
 */
// method TestRemoveExpiredBlood2()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 2;

//     inv.RemoveExpiredBlood(45);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 0;
//     var blood := inv.GetBloodOfType(AP);
//     assert blood[..] == [];
// }

////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects - none expired
 * Verification time: < 3 minutes
 */
// method TestRemoveExpiredBlood3()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 2;

//     inv.RemoveExpiredBlood(43);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 2;
//     var blood := inv.GetBloodOfType(AP);
//     assert blood[..] == [blood1, blood2];
// }

////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects of different types - one expired
 * Verification time: < 7 minutes
 */
// method TestRemoveExpiredBlood4()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(BP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     inv.RemoveExpiredBlood(44);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 0;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     var i1 := inv.GetBloodOfType(AP);
//     assert i1[..] == [];
//     var i2 := inv.GetBloodOfType(BP);
//     assert i2[..] == [blood2];
// }

////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects of different types - both expired
 * Verification time: < 3 minutes
 */
// method TestRemoveExpiredBlood5()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(BP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     inv.RemoveExpiredBlood(45);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 0;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 0;

//     var i1 := inv.GetBloodOfType(AP);
//     assert i1[..] == [];
//     var i2 := inv.GetBloodOfType(BP);
//     assert i2[..] == [];
// }

////////////////////////////////////////////////////////////////////////////////

/**
 * Two blood objects of different types - none expired
 * Verification time: ~30 seconds
 */
// method TestRemoveExpiredBlood6()
// {
//     var inv := new BloodInventory();
//     var amt;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(BP, "Bob", 2, "Hospital B", true);
//     inv.AddBlood(blood2);

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     inv.RemoveExpiredBlood(43);
//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 1;

//     var i1 := inv.GetBloodOfType(AP);
//     assert i1[..] == [blood1];
//     var i2 := inv.GetBloodOfType(BP);
//     assert i2[..] == [blood2];
// }

////////////////////////////////////////////////////////////////////////////////
// Black-box tests for RemoveBlood                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Verification time: < 1 minute
 */
// method TestRemoveBlood()
// {
//     var inv := new BloodInventory();
//     var blood;
//     var invblood;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital A", true);
//     inv.AddBlood(blood2);
//     var blood3 := new Blood(BP, "Deb", 1, "Hospital A", true);
//     inv.AddBlood(blood3);
//     var blood4 := new Blood(BP, "Eva", 2, "Hospital A", true);
//     inv.AddBlood(blood4);
//     var blood5 := new Blood(BP, "Fin", 3, "Hospital A", true);
//     inv.AddBlood(blood5);

//     blood := inv.RemoveBlood(AP);
//     assert blood == blood1;
//     invblood := inv.GetBloodOfType(AP);
//     assert invblood[..] == [blood2];

//     blood := inv.RemoveBlood(AP);
//     assert blood == blood2;
//     invblood := inv.GetBloodOfType(AP);
//     assert invblood[..] == [];

//     blood := inv.RemoveBlood(BP);
//     assert blood == blood3;
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [blood4, blood5];

//     blood := inv.RemoveBlood(BP);
//     assert blood == blood4;
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [blood5];

//     blood := inv.RemoveBlood(BP);
//     assert blood == blood5;
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [];
// }

////////////////////////////////////////////////////////////////////////////////
// Black-box tests for RequestOneType                                         //
////////////////////////////////////////////////////////////////////////////////

/**
 * Verification time: ~105 minutes
 * You can go out for lunch while waiting for this to verify
 */
// method TestRequestOneType()
// {
//     var inv := new BloodInventory();
//     var amt;
//     var invblood;

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital A", true);
//     inv.AddBlood(blood2);
//     var blood3 := new Blood(AP, "Cal", 3, "Hospital A", true);
//     inv.AddBlood(blood3);
//     var blood4 := new Blood(BP, "Deb", 1, "Hospital A", true);
//     inv.AddBlood(blood4);
//     var blood5 := new Blood(BP, "Eva", 2, "Hospital A", true);
//     inv.AddBlood(blood5);
//     var blood6 := new Blood(BP, "Fin", 3, "Hospital A", true);
//     inv.AddBlood(blood6);
//     var blood7 := new Blood(BP, "Gal", 4, "Hospital A", true);
//     inv.AddBlood(blood7);

//     var req1 := Request(BP, 1);
//     var res1 := inv.RequestOneType(req1);
//     assert res1[..] == [blood4];

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 3;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 3;
//     amt := inv.GetBloodTypeCount(OP);
//     assert amt == 0;

//     invblood := inv.GetBloodOfType(AP);
//     assert invblood[..] == [blood1, blood2, blood3];
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [blood5, blood6, blood7];
//     invblood := inv.GetBloodOfType(OP);
//     assert invblood[..] == [];

//     var req2 := Request(AP, 2);
//     var res2 := inv.RequestOneType(req2);
//     assert res2[..] == [blood1, blood2];

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 3;
//     amt := inv.GetBloodTypeCount(OP);
//     assert amt == 0;

//     invblood := inv.GetBloodOfType(AP);
//     assert invblood[..] == [blood3];
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [blood5, blood6, blood7];
//     invblood := inv.GetBloodOfType(OP);
//     assert invblood[..] == [];

//     var req3 := Request(BP, 3);
//     var res3 := inv.RequestOneType(req3);
//     assert res3[..] == [blood5, blood6, blood7];

//     amt := inv.GetBloodTypeCount(AP);
//     assert amt == 1;
//     amt := inv.GetBloodTypeCount(BP);
//     assert amt == 0;
//     amt := inv.GetBloodTypeCount(OP);
//     assert amt == 0;

//     invblood := inv.GetBloodOfType(AP);
//     assert invblood[..] == [blood3];
//     invblood := inv.GetBloodOfType(BP);
//     assert invblood[..] == [];
//     invblood := inv.GetBloodOfType(OP);
//     assert invblood[..] == [];
// }

////////////////////////////////////////////////////////////////////////////////
// Blackbox tests for RequestManyTypes                                        //
////////////////////////////////////////////////////////////////////////////////

/**
 * Verification time: > 1 hour
 */
// method TestRequestManyTypes()
// {
//     var inv := new BloodInventory();

//     var blood1 := new Blood(AP, "Amy", 1, "Hospital A", true);
//     inv.AddBlood(blood1);
//     var blood2 := new Blood(AP, "Bob", 2, "Hospital A", true);
//     inv.AddBlood(blood2);
//     var blood3 := new Blood(BP, "Cal", 3, "Hospital A", true);
//     inv.AddBlood(blood3);

//     var req := new Request[2];
//     req[0]  := Request(AP, 1);
//     req[1]  := Request(BP, 1);

//     var res := inv.RequestManyTypes(req);
//     assert res[AP][..] == [blood1];
//     assert res[BP][..] == [blood3];
// }

////////////////////////////////////////////////////////////////////////////////
