method Triple(x: int) returns (r: int) {
  var y := 2 * x;
  r := x + y;
}

method Main() {
  var t := Triple(18);
  print t, "\n"; // 54
}
