function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)
{
  // proof is automatic by Dafny's automatic induction
}
