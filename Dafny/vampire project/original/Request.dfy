include "BloodInventory.dfy"
include "Alert.dfy"
datatype request = bloodRequest(bloodType: string, volume: int)

// note we don't really need to say what happens to the inventory, since the blood inventory itself
// ensures what happens to it whenever we access its methods
method Request(batchRequest:array<request>, bloodInventory: BloodInventory) returns(requestResult: array<Blood>)
requires batchRequest != null
requires bloodInventory != null
requires bloodInventory.GetArrayVerification() != null
requires forall i :: 0 <= i < bloodInventory.GetArrayVerification().Length ==> (bloodInventory.GetArrayVerification()[i] != null)
requires forall i :: 0 <= i < batchRequest.Length ==> (validBloodType(batchRequest[i].bloodType))
requires bloodInventory.GetArrayVerification().Length < bloodInventory.GetSizeVerificaiton()
requires forall i :: 0 <= i < batchRequest.Length ==> (batchRequest[i].volume >= bloodInventory.GetBloodCountForBloodTypeVerification(batchRequest[i].bloodType, bloodInventory.GetSizeVerificaiton()))
ensures bloodInventory == old(bloodInventory)
ensures forall i :: 0 <= i < batchRequest.Length ==> (batchRequest[i].volume == GetCountOfBloodTypeInArray(requestResult, batchRequest[i].bloodType, requestResult.Length - 1))
{
    var i := 0;
    var threshold := bloodInventory.GetThreshold();
    requestResult := new Blood[1];
    while i < batchRequest.Length
    {
        var count := 0;
        while count < batchRequest[i].volume
        {
            var addblood, indexusedonlyforverification := bloodInventory.removeBlood(batchRequest[i].bloodType);
            requestResult := AddBloodToArrayResizing(requestResult, addblood);
            count := count + 1;
        }
        // before we move on check for alert for sake of checking
        var checkAlert := new Alert();
        var newBloodCount := bloodInventory.GetBloodCountForBloodTypeExecution(batchRequest[i].bloodType);
        var alertOn := checkAlert.CheckForAlert(threshold, newBloodCount);
        // THIS IS THE CALL TO HQ WEO WEO FIX THE THING
        if alertOn
        {
            var count := 0;
            var bloodType := batchRequest[i].bloodType;
            var emergencyDonor := new Blood(bloodType, "EMERGENCY DONOR", 0);
            while count < (threshold - newBloodCount)
            invariant 0 <= count <= (threshold - newBloodCount)
            invariant emergencyDonor != null
            {
                var dummy := bloodInventory.AddBlood(emergencyDonor);
                count := count + 1;
            }
        }
        i := i + 1;
    }
}

method AddBloodToArrayResizing(arr: array<Blood>, blood: Blood) returns (newResizedArray: array<Blood>)
requires arr != null
requires blood != null
ensures newResizedArray != null
ensures newResizedArray.Length == arr.Length + 1
ensures forall i :: 0 <= i < arr.Length ==> newResizedArray[i] == arr[i]
ensures newResizedArray[arr.Length] == blood
{
    newResizedArray := new Blood[arr.Length + 1];
    forall i | 0 <= i < arr.Length
    {
        newResizedArray[i] := arr[i];
    }
    newResizedArray[arr.Length] := blood;
}

function GetCountOfBloodTypeInArray(a: array<Blood>, bloodType: string, indexToCountTo: int): int
requires a != null
requires forall i :: 0 <= i < a.Length ==> (a[i] != null)
reads a, set i | 0 <= i < a.Length :: a[i]
requires indexToCountTo < a.Length
requires validBloodType(bloodType)
{
    if indexToCountTo < 0
    then
        0
    else
        if a[indexToCountTo].GetBloodType() == bloodType
        then
            1 + GetCountOfBloodTypeInArray(a, bloodType, indexToCountTo - 1)
        else
            GetCountOfBloodTypeInArray(a, bloodType, indexToCountTo - 1)
}