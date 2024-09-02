method Index(n: int) returns (i: int)
  requires 1 <= n
  ensures 0 <= i < n
{
  i := n / 2;

  // Or, the following statement also satisfies the specification:
  // i := 0;
}

method Caller() {
  var x := Index(50);
  var y := Index(50);
  assert x == y; // error: the specification of Index does not allow you to prove this condition
}
