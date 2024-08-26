(* slightly extend Perennial's proof setup *)
From Perennial.program_proof Require Export proof_prelude.
From sys_verif Require Export options.

#[global] Open Scope general_if_scope.

#[warning="-uniform-inheritance"]
#[global] Coercion goose_lang.Var : string >-> expr.

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
