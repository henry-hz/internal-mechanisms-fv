ghost function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant p == Power(i)
  {
    p := 2 * p;
    i := i + 1;
  }
}

method ComputePower'(n: nat) returns (p: nat)
  ensures p == Power(n)
{
  p := 1;
  var i := 0;
  while i != n
    invariant 0 <= i <= n
    invariant p * Power(n - i) == Power(n)
  {
    p := 2 * p;
    i := i + 1;
  }
}
