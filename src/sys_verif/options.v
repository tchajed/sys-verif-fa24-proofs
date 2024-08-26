From stdpp Require Export base.
From Coq Require Export ssreflect.
From Coq Require Export Lia.

(* force strict bulleting *)
#[export] Set Default Goal Selector "!".

(* Establishes what section variables proofs depend on. This enables vos proofs
to work - without it, Coq runs the proof to figure out what the signature should
look like (based on what variables are used), which we don't want. *)
#[export] Set Default Proof Using "Type".

(* This is an option that we don't want universally but may be locally
needed. *)

(* Printing projections is nice for record fields but unfortunately causes
coercions like [to_val] to be printed when they  *)
#[export] Unset Printing Projections.

#[global] Open Scope Z_scope.

#[global] Open Scope general_if_scope.
