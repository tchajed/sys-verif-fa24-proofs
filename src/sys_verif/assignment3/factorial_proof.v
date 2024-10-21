(*| # Assignment 3: verify factorial function

The code in
[go/functional/functional.go](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/go/functional/functional.go)
implements `func Factorial(n uint6) uint64`.

Here, you'll prove this function correct, proving that the imperative, loop-based
implementation Go is equivalent to a recursive, functional implementation in
Gallina.

Before starting, **you should read the [fibonacci
demo](/notes/program-proofs/fibonacci_proof.md)**, which has a very similar
structure to this proof.

|*)
From sys_verif.program_proof Require Import prelude empty_ffi.
From Goose.sys_verif_code Require Import functional.

Section proof.
Context `{hG: !heapGS Σ}.

(*| A functional implementation of the factorial function is already provided as
`fact` by the Coq standard library, which is what we'll use. It looks as you'd expect:

```coq
Fixpoint fact (n: nat): nat :=
  match n with
  | 0%nat => 1%nat
  | S n' => (S n' * fact n')%nat
  end.
```

|*)

Lemma fact_monotonic (n m: nat) :
  (n ≤ m)%nat →
  (fact n ≤ fact m)%nat.
Proof.
  (* this is already in the standard library *)
  apply Coq.Arith.Factorial.fact_le.
Qed.

Lemma fact_S (n: nat) :
  fact (S n) = ((S n) * fact n)%nat.
Proof.
  (* this follows from the definition itself *)
  reflexivity.
Qed.

(* You will need to use `rewrite word.unsigned_mul_nowrap` yourself in this
proof, which the `word` tactic will not (currently) do automatically. *)

Lemma wp_Factorial (n: w64) :
  {{{ ⌜Z.of_nat (fact (uint.nat n)) < 2^64⌝ }}}
    Factorial #n
  {{{ (c: w64), RET #c; ⌜uint.nat c = fact (uint.nat n)⌝ }}}.
Proof.
Admitted.

End proof.
