method Multiply(x0: int, y: int) returns (z: int)
  requires x0 >= 0  // needed for termination
  ensures z == x0 * y
{
  z := 0;
  var x := x0;
  while x != 0
    invariant z == (x0 - x) * y
    invariant x >= 0
    decreases x
  {
    z := z + y;
    x := x - 1;
    
  }
}