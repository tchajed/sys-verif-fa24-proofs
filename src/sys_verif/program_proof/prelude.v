(* slightly extend Perennial's proof setup *)
From Perennial.program_proof Require Export proof_prelude.
From iris_named_props Require Import named_props.
From sys_verif Require Export options.

(* enable ASCII [name :: P] instead of Unicode [name ∷ P] for named
propositions, in bi_scope *)
Export named_props_ascii_notation.

#[global] Open Scope general_if_scope.

(* Print ncfupd as a normal fupd, to avoid seeing (even more) confusing
goals.

These notations need to be distinct from the fupd notations (otherwise those
don't parse), so they include a Unicode zero-width space after the => *)
Notation "|={ E }=>​ Q" := (ncfupd E E Q) (only printing, at level 200, E at level 50) : bi_scope.
Notation "|==>​ Q" := (ncfupd ⊤ ⊤ Q) (only printing, at level 200) : bi_scope.

Tactic Notation "wp_start" :=
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.

Tactic Notation "wp_start" "as" constr(pat) :=
  (* When proving a loop body, the obligation is expressed using a Hoare triple
  as an iProp with a persistently modality in front, which is not needed in the
  top-level Hoare triple notation.

    Ideally the tactic would differentiate these two with pattern matching but
    we haven't bothered with error messaging here.
   *)
  try (iModIntro (□ _)%I);
  iIntros (Φ) "Hpre HΦ";
  iDestruct "Hpre" as pat;
  try wp_rec.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  first [ wp_apply wp_ref_to;
          [ val_ty
          | iIntros (l) H ]
        | wp_apply wp_ref_of_zero;
          [ cbv; by auto
          | iIntros (l) H ]
        | wp_apply wp_allocStruct;
          [ val_ty
          | iIntros (l) H ]
    ]
.
