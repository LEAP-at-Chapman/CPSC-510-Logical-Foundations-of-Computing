method Divide(x: int, y: int) returns (q: int, r: int)
  requires y > 0     // divisor must be positive
  ensures x == q * y + r
  ensures 0 <= r < y
{
  q := 0;
  r := x;
  while r >= y
    invariant 0 <= r
    invariant x == q * y + r
  {
    r := r - y;
    q := q + 1;
  }
}

method Main() {
  var quotient, remainder := Divide(12,8);
  print "Divide(-12,8) = ", quotient, ", remainder = ", remainder, "\n";
}