/* 
 * Querying
 * Queries an array of blood objects by attribute.
 * Verification time: < 3 seconds
 * Verified on CSE Dafny 1.9.7
 */

include "Blood.dfy"
include "Filter.dfy"

// Returns a new array containing only blood objects of a specific blood type.
method queryBloodByType(inv: array<Blood>, bloodType: BloodType) returns (result: array<Blood>)
    requires inv != null
    requires forall i | 0 <= i < inv.Length :: inv[i] != null
    ensures  result != null
    ensures  result[..] == VerifyFilter(inv, inv.Length, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType)
{
    result := Filter(inv, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType);
}

// Returns a new array containing only blood objects in a specified date range.
method queryBloodByDate(inv: array<Blood>, start: int, end: int) returns (result: array<Blood>)
    requires inv != null;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    ensures  result != null;
    ensures  result[..] == VerifyFilter(inv, inv.Length, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end);
{
    result := Filter(inv, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end);
}

////////////////////////////////////////////////////////////////////////////////

method getNonExpiredBlood(inv: array<Blood>, currentDate: int) returns (res: array<Blood>)
    requires inv != null;
    requires forall i | 0 <= i < inv.Length ::
                        inv[i] != null &&
                        inv[i].Valid();
    ensures  res != null;
    ensures  res != inv;
    ensures  fresh(res);
    ensures  res[..] == getNonExpiredBloodSeq(inv, currentDate);
    ensures  multiset(res[..]) <= multiset(inv[..]);
{
    res := Filter(inv, (b: Blood) requires b != null reads b => !b.IsExpired(currentDate));
}

function getNonExpiredBloodSeq(inv: array<Blood>, currentDate: int): seq<Blood>
    reads inv;
    requires inv != null;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    reads set i | 0 <= i < inv.Length :: inv[i];
{
    VerifyFilter(inv, inv.Length, (b: Blood) requires b != null reads b => !b.IsExpired(currentDate))
}

////////////////////////////////////////////////////////////////////////////////

// Returns the number of blood objects of a specific blood type.
function method countBloodByType(inv: array<Blood>, bloodType: BloodType): int
    reads inv;
    requires inv != null;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    reads set i | 0 <= i < inv.Length :: inv[i];
{
    Matches(inv, inv.Length, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType)
}

// Returns the number of blood objects in a specified date range.
function method countBloodByDate(inv: array<Blood>, start: int, end: int): int
    reads inv;
    requires inv != null;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    reads set i | 0 <= i < inv.Length :: inv[i];
{
    Matches(inv, inv.Length, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end)
}

////////////////////////////////////////////////////////////////////////////////

function countBloodByTypeUpTo(inv: array<Blood>, upTo: int, bloodType: BloodType): int
    reads inv;
    requires inv != null;
    requires 0 <= upTo <= inv.Length;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    reads set i | 0 <= i < inv.Length :: inv[i];
{
    Matches(inv, upTo, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType)
}

function countBloodByDateUpTo(inv: array<Blood>, upTo: int, start: int, end: int): int
    reads inv;
    requires inv != null;
    requires 0 <= upTo <= inv.Length;
    requires forall i | 0 <= i < inv.Length :: inv[i] != null;
    reads set i | 0 <= i < inv.Length :: inv[i];
{
    Matches(inv, upTo, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end)
}
