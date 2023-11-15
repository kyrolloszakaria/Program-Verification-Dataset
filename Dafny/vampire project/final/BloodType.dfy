/*
 * Blood type representation
 * Verification time: < 2 seconds
 * Verified on CSE Dafny 1.9.7
 */

datatype BloodType = AP | BP | OP | ABP | AM | BM | OM | ABM

predicate method validBloodType(bloodType: BloodType)
{
    bloodType in [AP, BP, OP, ABP, AM, BM, OM, ABM]
}
