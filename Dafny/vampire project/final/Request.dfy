/*
 * Request representation
 * Verification time: < 1 second
 * Verified on CSE Dafny 1.9.7
 */

include "BloodType.dfy"

datatype Request = Request(bloodType: BloodType, volume: int)
