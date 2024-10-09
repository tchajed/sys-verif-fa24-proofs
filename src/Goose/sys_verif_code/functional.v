(* autogenerated from sys_verif_code/functional *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.

Section code.
Context `{ext_ty: ext_types}.

(* Add returns the sum of a and b *)
Definition Add: val :=
  rec: "Add" "a" "b" :=
    "a" + "b".

(* Max returns the max of a and b *)
Definition Max: val :=
  rec: "Max" "a" "b" :=
    (if: "a" > "b"
    then "a"
    else "b").

Definition Midpoint: val :=
  rec: "Midpoint" "x" "y" :=
    ("x" + "y") `quot` #2.

(* Midpoint2 calculates the midpoint in an overflow-proof way *)
Definition Midpoint2: val :=
  rec: "Midpoint2" "x" "y" :=
    "x" + (("y" - "x") `quot` #2).

Definition Arith: val :=
  rec: "Arith" "a" "b" :=
    let: "sum" := "a" + "b" in
    (if: "sum" = #7
    then "a"
    else
      let: "mid" := Midpoint "a" "b" in
      "mid").

(* SumNrec adds up the numbers from 1 to n, recursively. *)
Definition SumNrec: val :=
  rec: "SumNrec" "n" :=
    (if: "n" = #0
    then #0
    else "n" + ("SumNrec" ("n" - #1))).

(* SumN adds up the numbers from 1 to n, with a loop. *)
Definition SumN: val :=
  rec: "SumN" "n" :=
    let: "sum" := ref_to uint64T #0 in
    let: "i" := ref_to uint64T #1 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "i") > "n"
      then Break
      else
        "sum" <-[uint64T] (std.SumAssumeNoOverflow (![uint64T] "sum") (![uint64T] "i"));;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![uint64T] "sum".

(* Fibonacci returns the nth Fibonacci number *)
Definition Fibonacci: val :=
  rec: "Fibonacci" "n" :=
    (if: "n" = #0
    then #0
    else
      let: "fib_prev" := ref_to uint64T #0 in
      let: "fib_cur" := ref_to uint64T #1 in
      let: "i" := ref_to uint64T #1 in
      (for: (λ: <>, (![uint64T] "i") < "n"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
        let: "fib_next" := (![uint64T] "fib_cur") + (![uint64T] "fib_prev") in
        "fib_prev" <-[uint64T] (![uint64T] "fib_cur");;
        "fib_cur" <-[uint64T] "fib_next";;
        Continue);;
      ![uint64T] "fib_cur").

(* Factorial returns n factorial *)
Definition Factorial: val :=
  rec: "Factorial" "n" :=
    (if: "n" = #0
    then #1
    else
      let: "fact" := ref_to uint64T #1 in
      let: "i" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "i") < "n"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
        "fact" <-[uint64T] ((![uint64T] "fact") * ((![uint64T] "i") + #1));;
        Continue);;
      ![uint64T] "fact").

(* FastExp returns b to the power of n0 *)
Definition FastExp: val :=
  rec: "FastExp" "b" "n0" :=
    let: "a" := ref_to uint64T #1 in
    let: "c" := ref_to uint64T "b" in
    let: "n" := ref_to uint64T "n0" in
    Skip;;
    (for: (λ: <>, (![uint64T] "n") > #0); (λ: <>, Skip) := λ: <>,
      (if: ((![uint64T] "n") `rem` #2) = #1
      then
        "a" <-[uint64T] ((![uint64T] "a") * (![uint64T] "c"));;
        "n" <-[uint64T] ((![uint64T] "n") `quot` #2)
      else "n" <-[uint64T] ((![uint64T] "n") `quot` #2));;
      "c" <-[uint64T] ((![uint64T] "c") * (![uint64T] "c"));;
      Continue);;
    ![uint64T] "a".

End code.
