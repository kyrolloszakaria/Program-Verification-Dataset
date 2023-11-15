// method atoi(ns: string) returns (ret: int) 
//     ensures atoi(ret) == ns;
// {
//     return "-1";
// }

method atoi(ns: string) returns (ret: int) 
    requires isNumString(ns)
{

}

method itoa(num: int) returns (ret: string)
    ensures isNumString(ret)
{
    var lookup := numchars();
    ret := "";
    var i := num;
    if num < 0 {
        ret := "-";
        i := 0 - num;
    }
    while i > 0 
        invariant isNumString(ret)
    {
        var digit := i % 10; 
        // assert lookup[digit] in numchars();
        ret := ret+[lookup[digit]];
        i := i / 10;
    }
    return ret;
}

function method numchars(): seq<char>
    ensures numchars() == ['-','0','1','2','3','4','5','6','7','8','9']
{
    ['-','0','1','2','3','4','5','6','7','8','9']
}

predicate charInNC(c: char) {
    c in numchars()
}

predicate isNumString(s: string) 
{
    s == "" || forall i  :: 0 <= i < |s| ==> charInNC(s[i])
}

method test() {
    var one := "1";
    var onehundredsome := "1239";
    var test := "test1234";
    assert isNumString(one) == true;
    assert isNumString(onehundredsome) == true;
}

method Fizzbuzz(n: int) returns (ret: array<string>)
    requires n >= 0
    ensures n == ret.Length
    ensures forall i :: 0 <= i < n ==> i % 3 == 0 && i % 5 != 0 ==> ret[i] == "fizz"
    ensures forall i :: 0 <= i < n ==> i % 3 != 0 && i % 5 == 0 ==> ret[i] == "buzz"
    ensures forall i :: 0 <= i < n ==> i % 15 == 0              ==> ret[i] == "fizzbuzz"
    //ensures forall i :: 0 <= i < n ==> i % 3 != 0 && i % 5 != 0 ==> ret[i] == i
{
    ret := new string[n];

    var j := 0;
    while j < n
        invariant 0 <= j <= n // Another one of those "obvious" facts that Dafny needs to be told explicitly
        invariant forall i :: 0 <= i < j ==> i % 3 == 0 && i % 5 != 0 ==> ret[i] == "fizz"
        invariant forall i :: 0 <= i < j ==> i % 3 != 0 && i % 5 == 0 ==> ret[i] == "buzz"
        invariant forall i :: 0 <= i < j ==> i % 15 == 0              ==> ret[i] == "fizzbuzz"
        //invariant forall i :: 0 <= i < n ==> i % 3 != 0 && i % 5 != 0 ==> ret[i] == i
    {
        if j % 3 == 0 && j % 5 != 0 {
            ret[j] := "fizz";
        } else if j % 3 != 0 && j % 5 == 0 {
            ret[j] := "buzz";
        } else if j % 15 == 0 {
            ret[j] := "fizzbuzz";
        } else if j % 3 != 0 && j % 5 != 0 {
            ret[j] := "TODO: convert j to a string";
        }
        j := j + 1;
    }
}