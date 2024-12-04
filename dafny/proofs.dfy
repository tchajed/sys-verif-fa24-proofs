function seq_sum(s: seq<int>): int
{
  if s == [] then 0
  else s[0] + seq_sum(s[1..])
}

lemma seq_sum_app(s1: seq<int>, s2: seq<int>)
  ensures seq_sum(s1 + s2) == seq_sum(s1) + seq_sum(s2)
{
  if s1 == [] {
    assert s1 + s2 == s2;
    return;
  }
  seq_sum_app(s1[1..], s2);
  assert s1[1..] + s2 == (s1 + s2)[1..];
}
