/* Querying
 *
 * Queries an array of blood objects by attribute.
 */

include "Blood.dfy"
include "Filtering.dfy"

// Returns a new array containing only blood objects of a specific blood type.
method queryBloodByType(inv: array<Blood>, bloodType: string) returns (result: array<Blood>)
requires inv != null
requires forall i | 0 <= i < inv.Length :: inv[i] != null
ensures result != null
ensures result[..] == VerifyFilter(inv, inv.Length, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType)
{ result := Filter(inv, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType); }

// Returns a new array containing only blood objects in a specified date range.
method queryBloodByDate(inv: array<Blood>, start: int, end: int) returns (result: array<Blood>)
requires inv != null
requires forall i | 0 <= i < inv.Length :: inv[i] != null
ensures result != null
ensures result[..] == VerifyFilter(inv, inv.Length, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end)
{ result := Filter(inv, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end); }

// Returns the number of blood objects of a specific blood type.
function method countBloodByType(inv: array<Blood>, bloodType: string): int
reads inv
requires inv != null
requires forall i | 0 <= i < inv.Length :: inv[i] != null
reads set i | 0 <= i < inv.Length :: inv[i]
{ Matches(inv, inv.Length, (b: Blood) requires b != null reads b => b.GetBloodType() == bloodType) }

// Returns the number of blood objects in a specified date range.
function method countBloodByDate(inv: array<Blood>, start: int, end: int): int
reads inv
requires inv != null
requires forall i | 0 <= i < inv.Length :: inv[i] != null
reads set i | 0 <= i < inv.Length :: inv[i]
{ Matches(inv, inv.Length, (b: Blood) requires b != null reads b => start <= b.GetDateDonated() <= end) }
