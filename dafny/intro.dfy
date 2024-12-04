function pow(x: int, y: nat): int
{
  if y == 0 then 1
  else x * pow(x, y-1)
}

const INT_MAX: int := pow(2, 64)-1

method Add(x: int, y: int) returns (z: int)
  requires x + y <= INT_MAX
  ensures z == x + y
{
  return x + y;
}

method Min(x: int, y: int) returns (z:int)
  ensures z <= x && z <= y
{
  if x < y {
    return x;
  } else {
    return y;
  }
}

method F(n: int) returns (z: int)
  requires n < INT_MAX
  ensures z <= 1
{
  var m := Min(0, n);
  var y := Add(m, 1);
  return y;
}
