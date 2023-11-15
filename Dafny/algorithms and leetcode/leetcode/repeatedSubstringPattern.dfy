/*
https://leetcode.com/problems/repeated-substring-pattern/
function repeatedSubstringPattern(s: string): boolean {
    let n = Math.floor(s.length/2);
    for(let i = 1; i <= n; i ++) {
        if(s.length % i !== 0) continue;
        
        let substring = s.slice(0, i);
        if(substring.repeat(s.length/i) == s) return true
        
    }
    return false;
};
*/
function method repeat(s: string, count: nat): string 
    requires count > 0
{
    if count == 1 then s else s + repeat(s, count-1)
}

method test() {
    var example := "abab";
    assert "ab" < example;
    assert "aba" < example;
}

method repeatedSubstringPattern(s: string) returns (isRepeated: bool)
    requires |s| >= 1
    ensures isRepeated ==> exists sn :: sn < s && |sn| >= 1 && repeat(sn, |s|/|sn|) == s
{
    if |s| == 1  {
        return false;
    }
    var n := |s| / 2;
    for i := 1 to n 
    {
        if (|s| % i != 0) {
            continue;
        }
        var substring := s[0..i];
        if(repeat(substring, |s|/|substring|) == s) {
            return true;
        }
    }
    return false;
}