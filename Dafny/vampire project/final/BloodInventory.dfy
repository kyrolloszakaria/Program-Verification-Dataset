/*
 * Blood inventory class
 * Verification time: ~30 seconds
 * Verified on CSE Dafny 1.9.7
 */

include "Blood.dfy"
include "Query.dfy"
include "Request.dfy"

class BloodInventory
{
    var inv: map<BloodType, array<Blood>>; // map of blood types to blood arrays
                                           // (referred to as 'buckets')
    
    var threshold: int;

    ////////////////////////////////////////////////////////////////////////////
    // Valid() and friends

    predicate Valid()
        reads this;

        // reads the blood arrays
        reads if BucketsExist() then
                  set t | validBloodType(t) :: inv[t]
              else
                  {};
        
        // reads the blood objects
        reads if BucketsExist() then
                  set t, i | validBloodType(t) && 0 <= i < inv[t].Length :: inv[t][i]
              else
                  {};
    {
        // there is a blood bucket for each blood type
        (BucketsExist()) &&

        // no extraneous blood buckets in the inventory
        (forall t | t in inv :: validBloodType(t)) &&

        // all blood is non-null, valid, tested (clean), and of the correct type
        (forall t, i | t in inv && 0 <= i < inv[t].Length ::
                       inv[t][i] != null &&
                       inv[t][i].Valid() &&
                       inv[t][i].HasBeenTested() &&
                       inv[t][i].GetBloodType() == t) &&

        // blood 'buckets' are all different
        (forall t, u | t in inv && u in inv :: t != u ==> inv[t] != inv[u]) &&

        threshold >= 0
    }

    predicate BucketsExist()
        reads this;
    {
        forall t | validBloodType(t) :: t in inv && inv[t] != null
    }

    predicate AllBucketsEmpty()
        reads this;
        requires BucketsExist();
        reads set t | validBloodType(t) :: inv[t];
    {
        forall t | validBloodType(t) :: inv[t] != null && inv[t].Length == 0
    }

    ////////////////////////////////////////////////////////////////////////////
    // constructor

    constructor()
        modifies this;
        ensures  Valid();
        ensures  AllBucketsEmpty();
        ensures  forall t | t in inv :: fresh(inv[t]);
        ensures  threshold == 0;
    {
        var a := new Blood[0];
        var b := new Blood[0];
        var c := new Blood[0];
        var d := new Blood[0];
        var e := new Blood[0];
        var f := new Blood[0];
        var g := new Blood[0];
        var h := new Blood[0];
        
        inv := map[
            AP := a, BP := b, OP := c, ABP := d,
            AM := e, BM := f, OM := g, ABM := h
        ];

        threshold := 0;
    }

    ////////////////////////////////////////////////////////////////////////////
    // Getters

    method GetThreshold() returns (threshold: int)
        requires Valid();
        ensures  Valid();
        ensures  threshold == this.threshold;
    {
        threshold := this.threshold;
    }

    // Gets all blood of a specified type
    method GetBloodOfType(bloodType: BloodType) returns (blood: array<Blood>)
        requires Valid();
        requires validBloodType(bloodType);
        ensures  Valid();
        ensures  blood == inv[bloodType];
    {
        blood := inv[bloodType];
    }

    ////////////////////////////////////////////////////////////////////////////
    // Setters

    method ModifyThreshold(threshold: int)
        modifies this`threshold;
        requires Valid();
        requires threshold >= 0;
        ensures  Valid();
        ensures  this.threshold == threshold;
    {
        this.threshold := threshold;
    }

    ////////////////////////////////////////////////////////////////////////////
    // Printing - because there's a little bit of C in all of us

    method Show()
        requires Valid();
        ensures  Valid();
    {
        print "==========================\n";
        print "         Inventory        \n";
        print "==========================\n";

        var ts := [AP, BP, OP, ABP, AM, BM, OM, ABM];
        var i := 0;
        while i < |ts|
        {
            print ts[i], "\n";
            var j := 0;
            while j < inv[ts[i]].Length
            {
                print "\n";
                inv[ts[i]][j].PrettyPrint();
                j := j + 1;
            }
            if i < |ts| - 1
            {
                print "--------------------------\n";
            }
            i := i + 1;
        }
        print "==========================\n";
    }

    ////////////////////////////////////////////////////////////////////////////
    // Getting Blood Type Counts

    // Returns the amount of blood of a given type
    method GetBloodTypeCount(bloodType: BloodType) returns (count: int)
        requires validBloodType(bloodType);
        requires Valid();
        ensures  Valid();
        ensures  count == inv[bloodType].Length;
    {
        return inv[bloodType].Length;
    }

    // Returns the amount of blood of each type in a map
    method GetAllBloodTypeCounts() returns (counts: map<BloodType, int>)
        requires Valid();
        ensures  Valid();
        ensures  forall t | validBloodType(t) ::
                            t in counts && counts[t] == inv[t].Length;
        
        // no extraneous blood types in the returned map
        ensures  forall t | t in counts :: validBloodType(t);
    {
        counts := map[];

        var types := set t | validBloodType(t);
        var typesLeft := types;

        // on  each  iteration, remove one blood type from typesLeft and add its
        // count to the map
        while typesLeft != {}
            decreases typesLeft;
            invariant Valid();
            invariant forall t | t in inv && t !in typesLeft ::
                                 t in counts && counts[t] == inv[t].Length;
            invariant forall t | t in counts :: validBloodType(t);
        {
            var t :| t in typesLeft;
            var count := inv[t].Length;
            counts := counts[t := count];
            typesLeft := typesLeft - {t};
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Adding Blood

    method AddBlood(blood: Blood)
        modifies this`inv;
        requires Valid();
        requires blood != null;
        requires blood.Valid() && blood.HasBeenTested();
        ensures  Valid();

        // the  new blood object is added to the end of the bucket corresponding
        // to its blood type
        ensures  inv[blood.GetBloodType()][..] == old(inv[blood.GetBloodType()][..]) + [blood];
        ensures  fresh(inv[blood.GetBloodType()]);

        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && t != blood.GetBloodType() ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        var t := blood.GetBloodType();

        // create a new bucket to make room for the new blood
        var newBucket := new Blood[inv[t].Length + 1];

        // copy the original blood objects into the new bucket
        forall i | 0 <= i < inv[t].Length
        {
            newBucket[i] := inv[t][i];
        }
        newBucket[inv[t].Length] := blood;
        inv := inv[t := newBucket];
    }

    ////////////////////////////////////////////////////////////////////////////
    // Removing Expired Blood

    method RemoveExpiredBloodOfType(bloodType: BloodType, currentDate: int)
        modifies this`inv;
        requires validBloodType(bloodType);
        requires Valid();
        ensures  Valid();
        ensures  inv[bloodType] != old(inv[bloodType]);
        ensures  fresh(inv[bloodType]);
        ensures  inv[bloodType][..] == getNonExpiredBloodSeq(old(inv[bloodType]), currentDate);
        // ensure other blood buckets are unchanged
        ensures  forall t | validBloodType(t) && t != bloodType ::
                            inv[t] == old(inv[t]) && inv[t][..] == old(inv[t][..]);
    {
        // getNonExpiredBlood is in Query.dfy, and uses filter
        var nonExpired := getNonExpiredBlood(inv[bloodType], currentDate);
        inv := inv[bloodType := nonExpired];

        // prove that the filtered blood objects are still valid
        LemmaA(inv[bloodType], old(inv[bloodType]), bloodType);
    }

    // We  assume  that the system will call this method daily (at midnight), so
    // the inventory will never contain expired blood when requests are made.
    method RemoveExpiredBlood(currentDate: int)
        modifies this`inv;
        requires Valid();
        ensures  Valid();
        ensures  forall t | t in inv ::
                            fresh(inv[t]) &&
                            inv[t][..] == getNonExpiredBloodSeq(old(inv[t]), currentDate)
    {
        var types := set t | t in inv;
        var typesLeft := types;

        // on  each  iteration,  remove one blood type from typesLeft and remove
        // all expired blood of that type
        while typesLeft != {}
            decreases typesLeft;
            invariant Valid();
            invariant forall t | t in inv && t !in typesLeft ::
                                 fresh(inv[t]) &&
                                 inv[t][..] == getNonExpiredBloodSeq(old(inv[t]), currentDate);
            invariant forall t | t in inv && t  in typesLeft ::
                                 inv[t] == old(inv[t]) &&
                                 inv[t][..] == old(inv[t][..]);
        {
            var t :| t in typesLeft;
            RemoveExpiredBloodOfType(t, currentDate);
            typesLeft := typesLeft - {t};
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Remove Blood

    method RemoveBlood(bloodType: BloodType) returns (blood: Blood)
        modifies this`inv;
        requires Valid();
        requires inv[bloodType].Length > 0;
        ensures  Valid();

        // we  choose  to  remove the first blood object from the bucket for the
        // requested type
        ensures  blood == old(inv[bloodType][0]);
        ensures  blood.GetBloodType() == bloodType;

        // ensure the other blood objects remain in the inventory
        ensures  inv[bloodType][..] == old(inv[bloodType][1..]);
        ensures  fresh(inv[bloodType]);

        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && t != blood.GetBloodType() ::
                            inv[t] == old(inv[t]) &&
                            inv[t].Length == old(inv[t].Length) &&
                            inv[t][..] == old(inv[t][..]);
    {
        var t := bloodType;
        // grab first blood object
        blood := inv[t][0];

        // create a new bucket with one less room
        var newBucket := new Blood[inv[t].Length - 1];

        // copy the remaining blood objects into the new bucket
        forall i | 1 <= i < inv[t].Length
        {
            newBucket[i - 1] := inv[t][i];
        }
        inv := inv[t := newBucket];
    }

    ////////////////////////////////////////////////////////////////////////////
    // Request Fulfilment

    predicate method RequestCanBeFulfilled(req: array<Request>)
        reads this;
        reads if BucketsExist() then
                  set t | validBloodType(t) :: inv[t]
              else
                  {};
        reads if BucketsExist() then
                  set t, i | validBloodType(t) && 0 <= i < inv[t].Length :: inv[t][i]
              else
                  {};
        reads req;
        requires Valid();
        requires req != null;
        requires req.Length > 0;
        requires forall i | 0 <= i < req.Length ::
                            validBloodType(req[i].bloodType) &&
                            req[i].volume > 0;
        requires forall i, j | 0 <= i < j < req.Length ::
                               req[i].bloodType != req[j].bloodType;
    {
        forall i | 0 <= i < req.Length :: req[i].volume <= inv[req[i].bloodType].Length
    }

    // NOTE: It is assumed that Vampire staff will remove expired blood from the
    //       inventory daily (at midnight).  So the inventory will never contain
    //       expired blood.
    method RequestOneType(req: Request) returns (blood: array<Blood>)
        modifies this`inv;
        requires Valid();
        requires validBloodType(req.bloodType);

        // the inventory must have enough blood to fulfill the request. requests
        // for 0 volume of blood are useless.
        requires 0 < req.volume <= inv[req.bloodType].Length;
        ensures  Valid();

        // we  remove the first req.volume blood objects from the bucket for the
        // requested blood type
        ensures  blood != null;
        ensures  fresh(blood);
        ensures  blood[..] == old(inv[req.bloodType][..req.volume]);

        // check that whatever is left in the inventory makes sense
        ensures  fresh(inv[req.bloodType]);
        ensures  forall t | t in inv :: inv[req.bloodType] != old(inv[t]);
        ensures  inv[req.bloodType][..] == old(inv[req.bloodType][req.volume..]);
        ensures  forall t | t in inv :: blood != inv[t];

        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && t != req.bloodType ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        var t := req.bloodType;

        // create a new array to store the requested blood, and another array to
        // store the remaining blood
        blood := new Blood[req.volume];
        var newBucket := new Blood[inv[t].Length - req.volume];
        
        forall i | 0 <= i < req.volume
        {
            blood[i] := inv[t][i];
        }
        forall i | req.volume <= i < inv[t].Length
        {
            newBucket[i - req.volume] := inv[t][i];
        }
        inv := inv[t := newBucket];
    }

    method RequestManyTypes(req: array<Request>) returns (res: map<BloodType, array<Blood>>)
        modifies this`inv;
        requires Valid();
        requires req != null;
        requires req.Length > 0;
        requires forall i | 0 <= i < req.Length ::
                            validBloodType(req[i].bloodType) &&
                            0 < req[i].volume <= inv[req[i].bloodType].Length;
        requires forall i, j | 0 <= i < j < req.Length :: req[i].bloodType != req[j].bloodType;
        ensures  Valid();
        ensures  forall i | 0 <= i < req.Length ::
                            req[i].bloodType in res &&

                            // check result
                            res[req[i].bloodType] != null &&
                            fresh(res[req[i].bloodType]) &&
                            res[req[i].bloodType][..] == old(inv[req[i].bloodType][..req[i].volume]) &&
                            forall t | t in inv :: res[req[i].bloodType] != inv[t] &&
                            
                            // check remaining blood
                            fresh(inv[req[i].bloodType]) &&
                            inv[req[i].bloodType][..] == old(inv[req[i].bloodType][req[i].volume..]) &&
                            forall t | t in inv :: inv[req[i].bloodType] != old(inv[t]);
        
        // no extraneous blood types in returned map
        ensures  forall t | t in res :: exists i | 0 <= i < req.Length :: t == req[i].bloodType;

        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && (forall i | 0 <= i < req.Length :: req[i].bloodType != t) ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        res := map[];

        var i := 0;
        while i < req.Length
            invariant 0 <= i <= req.Length;
            invariant Valid();
            invariant req[..] == old(req[..]);

            // watered down versions of the postconditions
            invariant forall j | i <= j < req.Length ::
                                 0 < req[j].volume <= inv[req[j].bloodType].Length &&
                                 inv[req[j].bloodType][..] == old(inv[req[j].bloodType][..]);
            invariant forall j | 0 <= j < i ::
                                 req[j].bloodType in res &&
                                 res[req[j].bloodType] != null &&
                                 fresh(res[req[j].bloodType]) &&
                                 res[req[j].bloodType][..] == old(inv[req[j].bloodType][..req[j].volume]) &&
                                 fresh(inv[req[j].bloodType]) &&
                                 inv[req[j].bloodType][..] == old(inv[req[j].bloodType][req[j].volume..]) &&
                                 forall t | t in inv :: res[req[j].bloodType] != inv[t] &&
                                 forall t | t in inv :: inv[req[j].bloodType] != old(inv[t]);

            // same as the postconditions
            invariant forall t | t in res :: exists i | 0 <= i < req.Length :: t == req[i].bloodType;
            invariant forall t | t in inv && (forall i | 0 <= i < req.Length :: req[i].bloodType != t) ::
                                 inv[t] == old(inv[t]) &&
                                 inv[t][..] == old(inv[t][..]);
        {
            var blood := RequestOneType(req[i]);
            res := res[req[i].bloodType := blood];
            i := i + 1;
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Fix Low Supply

    method FixLowSupplyForType(bloodType: BloodType)
        modifies this`inv;
        requires Valid();
        requires validBloodType(bloodType);
        ensures  Valid();

        // if  there  is a low supply of the specified blood type, add emergency
        // blood objects to the corresponding bucket until there is  'threshold'
        // amount of blood
        ensures  old(inv[bloodType].Length) <  threshold ==> (
                     fresh(inv[bloodType]) &&
                     inv[bloodType].Length == threshold &&
                     inv[bloodType][..old(inv[bloodType].Length)] == old(inv[bloodType][..]) &&
                     forall i | old(inv[bloodType].Length) <= i < threshold ::
                                inv[bloodType][i].GetDonorName() == "Emergency Donor" &&
                                inv[bloodType][i].GetDateDonated() == 999 &&
                                inv[bloodType][i].GetLocationAcquired() == "Emergency Hospital"
                 );
        
        // if the specified blood type is *not* in low supply, don't do anything
        ensures  old(inv[bloodType].Length) >= threshold ==> (
                     inv[bloodType] == old(inv[bloodType]) &&
                     inv[bloodType][..] == old(inv[bloodType][..])
                 );
        
        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && t != bloodType ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        if inv[bloodType].Length < threshold
        {
            var newBucket := new Blood[threshold];
            forall i | 0 <= i < inv[bloodType].Length
            {
                newBucket[i] := inv[bloodType][i];
            }

            // can't create new objects in a forall statement, so we need a loop
            var i := inv[bloodType].Length;
            while i < threshold
                invariant inv == old(inv);
                invariant inv[bloodType].Length <= i <= threshold;
                invariant newBucket[..inv[bloodType].Length] == inv[bloodType][..];
                invariant Valid();
                invariant forall t | t in inv :: newBucket != inv[t];
                invariant newBucket != null;
                invariant newBucket.Length == threshold;
                invariant fresh(newBucket);
                invariant forall j | 0 <= j < i ::
                                     newBucket[j] != null &&
                                     newBucket[j].Valid() &&
                                     newBucket[j].GetBloodType() == bloodType &&
                                     newBucket[j].HasBeenTested();
                invariant forall j | inv[bloodType].Length <= j < i ::
                                     newBucket[j].GetDonorName() == "Emergency Donor" &&
                                     newBucket[j].GetDateDonated() == 999 &&
                                     newBucket[j].GetLocationAcquired() == "Emergency Hospital";
                invariant forall t | t in inv && t != bloodType :: inv[t] == old(inv[t]) && inv[t][..] == old(inv[t][..]);
            {
                newBucket[i] := new Blood(bloodType, "Emergency Donor", 999, "Emergency Hospital", true);
                i := i + 1;
            }

            inv := inv[bloodType := newBucket];
        }
    }

    method FixLowSupply()
        modifies this`inv;
        requires Valid();
        ensures  Valid();
        ensures  forall t | validBloodType(t) ::
                            old(inv[t].Length) < threshold ==> (
                                inv[t].Length == threshold &&
                                inv[t][..old(inv[t].Length)] == old(inv[t][..]) &&
                                fresh(inv[t]) &&
                                forall i | old(inv[t].Length) <= i < threshold ::
                                           inv[t][i].GetDonorName() == "Emergency Donor" &&
                                           inv[t][i].GetDateDonated() == 999 &&
                                           inv[t][i].GetLocationAcquired() == "Emergency Hospital"
                            );
        ensures  forall t | validBloodType(t) ::
                            old(inv[t].Length) >= threshold ==> (
                                inv[t] == old(inv[t]) &&
                                inv[t][..] == old(inv[t][..])
                            );
    {
        var types := set t | t in inv;
        var typesLeft := types;

        while typesLeft != {}
            decreases typesLeft;
            invariant Valid();
            invariant forall t | t in inv && t !in typesLeft ::
                                 old(inv[t].Length) < threshold ==> (
                                     inv[t].Length == threshold &&
                                     inv[t][..old(inv[t].Length)] == old(inv[t][..]) &&
                                     fresh(inv[t]) &&
                                     forall i | old(inv[t].Length) <= i < threshold ::
                                                inv[t][i].GetDonorName() == "Emergency Donor" &&
                                                inv[t][i].GetDateDonated() == 999 &&
                                                inv[t][i].GetLocationAcquired() == "Emergency Hospital"
                                 );
            invariant forall t | t in inv && t !in typesLeft ::
                                 old(inv[t].Length) >= threshold ==> (
                                     inv[t] == old(inv[t]) &&
                                     inv[t][..] == old(inv[t][..])
                                 );
            invariant forall t | t in inv && t  in typesLeft :: inv[t] == old(inv[t]);
            invariant forall t | t in inv && t  in typesLeft :: inv[t][..] == old(inv[t][..]);
        {
            var t :| t in typesLeft;
            FixLowSupplyForType(t);
            typesLeft := typesLeft - {t};
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Request with Low Supply Fix

    // NOTE: these  methods  basically  combine  the  request  and fix low blood
    //       supply methods

    method RequestOneTypeWithLowSupplyFix(req: Request) returns (blood: array<Blood>)
        modifies this`inv;
        requires Valid();
        requires validBloodType(req.bloodType);
        requires 0 < req.volume <= inv[req.bloodType].Length;
        ensures  Valid();
        ensures  blood != null;
        ensures  fresh(blood);
        ensures  blood[..] == old(inv[req.bloodType][..req.volume]);
        ensures  forall i | 0 <= i < blood.Length :: blood[i] != null && blood[i].Valid();
        ensures  fresh(inv[req.bloodType]);
        
        ensures  old(inv[req.bloodType].Length) - req.volume < threshold ==> (
                     inv[req.bloodType].Length == threshold &&
                     inv[req.bloodType][..old(inv[req.bloodType].Length) - req.volume] ==
                         old(inv[req.bloodType][req.volume..]) &&
                     forall i | old(inv[req.bloodType].Length) - req.volume <= i < threshold ::
                                inv[req.bloodType][i].GetDonorName() == "Emergency Donor" &&
                                inv[req.bloodType][i].GetDateDonated() == 999 &&
                                inv[req.bloodType][i].GetLocationAcquired() == "Emergency Hospital"
                 );
        ensures  old(inv[req.bloodType].Length) - req.volume >= threshold ==> (
                     inv[req.bloodType][..] == old(inv[req.bloodType][req.volume..])
                 );
        
        ensures  forall t | t in inv :: blood != inv[t];

        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && t != req.bloodType ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        blood := RequestOneType(req);
        FixLowSupplyForType(req.bloodType);
    }

    method RequestManyTypesWithLowSupplyFix(req: array<Request>) returns (res: map<BloodType, array<Blood>>)
        modifies this`inv;
        requires Valid();
        requires req != null;
        requires req.Length > 0;
        requires forall i | 0 <= i < req.Length ::
                            validBloodType(req[i].bloodType) &&
                            0 < req[i].volume <= inv[req[i].bloodType].Length;
        requires forall i, j | 0 <= i < j < req.Length :: req[i].bloodType != req[j].bloodType;
        ensures  Valid();
        ensures  forall i | 0 <= i < req.Length ::
                            req[i].bloodType in res &&
                            res[req[i].bloodType] != null &&
                            fresh(res[req[i].bloodType]) &&
                            res[req[i].bloodType][..] == old(inv[req[i].bloodType][..req[i].volume]) &&
                            fresh(inv[req[i].bloodType]) &&
                            forall t | t in inv :: res[req[i].bloodType] != inv[t];
        
        ensures  forall i | 0 <= i < req.Length ::
                            old(inv[req[i].bloodType].Length) - req[i].volume <  threshold ==> (
                                inv[req[i].bloodType].Length == threshold &&
                                inv[req[i].bloodType][..old(inv[req[i].bloodType].Length) - req[i].volume] ==
                                    old(inv[req[i].bloodType][req[i].volume..]) &&
                                forall j | old(inv[req[i].bloodType].Length) - req[i].volume <= j < threshold ::
                                            inv[req[i].bloodType][j].GetDonorName() == "Emergency Donor" &&
                                            inv[req[i].bloodType][j].GetDateDonated() == 999 &&
                                            inv[req[i].bloodType][j].GetLocationAcquired() == "Emergency Hospital"
                            );
        ensures  forall i | 0 <= i < req.Length ::
                            old(inv[req[i].bloodType].Length) - req[i].volume >= threshold ==> (
                                inv[req[i].bloodType][..] == old(inv[req[i].bloodType][req[i].volume..])
                            );
        
        // no extraneous blood types in result
        ensures  forall t | t in res :: exists i | 0 <= i < req.Length :: t == req[i].bloodType;
        // ensure other blood buckets are unchanged
        ensures  forall t | t in inv && (forall i | 0 <= i < req.Length :: req[i].bloodType != t) ::
                            inv[t] == old(inv[t]) &&
                            inv[t][..] == old(inv[t][..]);
    {
        res := map[];

        var i := 0;
        while i < req.Length
            invariant 0 <= i <= req.Length;
            invariant Valid();
            invariant req[..] == old(req[..]);
            invariant forall j | i <= j < req.Length ::
                                 0 < req[j].volume <= inv[req[j].bloodType].Length &&
                                 inv[req[j].bloodType][..] == old(inv[req[j].bloodType][..]);
            invariant forall j | 0 <= j < i ::
                                 req[j].bloodType in res &&
                                 res[req[j].bloodType] != null &&
                                 fresh(res[req[j].bloodType]) &&
                                 res[req[j].bloodType][..] == old(inv[req[j].bloodType][..req[j].volume]) &&
                                 fresh(inv[req[j].bloodType]) &&
                                 forall t | t in inv :: res[req[j].bloodType] != inv[t];
            invariant forall j | 0 <= j < i ::
                                 old(inv[req[j].bloodType].Length) - req[j].volume <  threshold ==> (
                                     inv[req[j].bloodType].Length == threshold &&
                                     inv[req[j].bloodType][..old(inv[req[j].bloodType].Length) - req[j].volume] ==
                                         old(inv[req[j].bloodType][req[j].volume..]) &&
                                     forall k | old(inv[req[j].bloodType].Length) - req[j].volume <= k < threshold ::
                                                inv[req[j].bloodType][k].GetDonorName() == "Emergency Donor" &&
                                                inv[req[j].bloodType][k].GetDateDonated() == 999 &&
                                                inv[req[j].bloodType][k].GetLocationAcquired() == "Emergency Hospital"
                                 );
            invariant forall j | 0 <= j < i ::
                                 old(inv[req[j].bloodType].Length) - req[j].volume >= threshold ==> (
                                     inv[req[j].bloodType][..] == old(inv[req[j].bloodType][req[j].volume..])
                                 );
 
            invariant forall t | t in res :: exists j | 0 <= j < req.Length :: t == req[j].bloodType;

            // ensure other blood buckets are unchanged
            invariant forall t | t in inv && (forall i | 0 <= i < req.Length :: req[i].bloodType != t) ::
                                 inv[t] == old(inv[t]) &&
                                 inv[t][..] == old(inv[t][..]);
        {
            var blood := RequestOneTypeWithLowSupplyFix(req[i]);
            res := res[req[i].bloodType := blood];
            i := i + 1;
        }
    }
} // end of BloodInventory class

////////////////////////////////////////////////////////////////////////////////
// Lemma A

// Prove that if A is a subset of B and all elements of B satisfy some property,
// then all elements of A also satisfy that property.

lemma LemmaA(a: array<Blood>, b: array<Blood>, t: BloodType)
    requires a != null;
    requires b != null;
    requires multiset(a[..]) <= multiset(b[..]);
    requires forall i | 0 <= i < b.Length ::
                        b[i] != null &&
                        b[i].Valid() &&
                        b[i].HasBeenTested() &&
                        b[i].GetBloodType() == t;
    ensures  forall i | 0 <= i < a.Length ::
                        a[i] != null &&
                        a[i].Valid() &&
                        a[i].HasBeenTested() &&
                        a[i].GetBloodType() == t;
{
    LemmaA1(a[..], b[..], t);
}

lemma LemmaA1(a: seq<Blood>, b: seq<Blood>, t: BloodType)
    requires multiset(a) <= multiset(b);
    requires forall i | 0 <= i < |b| ::
                        b[i] != null &&
                        b[i].Valid() &&
                        b[i].HasBeenTested() &&
                        b[i].GetBloodType() == t;
    ensures  forall i | 0 <= i < |a| ::
                        a[i] != null &&
                        a[i].Valid() &&
                        a[i].HasBeenTested() &&
                        a[i].GetBloodType() == t;
{
    LemmaA2(multiset(a), multiset(b), t);
    assert forall i | i in multiset(a) :: i != null;
}

lemma LemmaA2(a: multiset<Blood>, b: multiset<Blood>, t: BloodType)
    requires a <= b;
    requires forall i | i in b ::
                        i != null &&
                        i.Valid() &&
                        i.HasBeenTested() &&
                        i.GetBloodType() == t;
    ensures  forall i | i in a ::
                        i != null &&
                        i.Valid() &&
                        i.HasBeenTested() &&
                        i.GetBloodType() == t;
{

}
