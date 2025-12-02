// /* A set is represented as a sequence with no duplicates */
// predicate isSet(s: seq<int>) {
//   forall i: int :: 0 <= i < |s| ==>
//   forall j: int :: 0 <= j < |s| && j != i ==> 
//   s[j] != s[i]
// }


// method test(s: seq<int>) returns (t: seq<int>)
//   ensures s == t
// {
//   t := [];
//   var i := 0;
//   while i < |s|
//     invariant 0 <= i <= |s|
//     invariant t == s[..i]
//     invariant |t| == i
//   {
//     t := t + [s[i]];
//     i := i + 1;
//   }
// }