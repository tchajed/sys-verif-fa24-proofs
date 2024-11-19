From sys_verif.program_proof Require Import prelude.

From iris.base_logic.lib Require Import ghost_var.

From Goose.sys_verif_code Require Import hashmap.

Module atomic_ptr.
Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.

  Definition N := nroot.

  #[local] Definition lock_inv l (P: loc → iProp Σ): iProp _ :=
    ∃ (mref: loc), "val" ∷ l ↦[atomicPtr :: "val"] #mref ∗
       "HP" ∷ P mref.

  Definition is_atomic_ptr (l: loc) (P: loc → iProp Σ): iProp _ :=
    ∃ (mu_l: loc),
    "mu" ∷ l ↦[atomicPtr :: "mu"]□ #mu_l ∗
    "Hlock" ∷ is_lock N (#mu_l) (lock_inv l P).

  #[global] Instance is_atomic_ptr_persistent l P : Persistent (is_atomic_ptr l P).
  Proof. apply _. Qed.

  Lemma wp_newAtomicPtr (P: loc → iProp Σ) (m_ref: loc) :
    {{{ P m_ref }}}
      newAtomicPtr #m_ref
    {{{ (l: loc), RET #l; is_atomic_ptr l P }}}.
  Proof.
    wp_start as "HP".
    rewrite -wp_fupd.
    wp_apply wp_new_free_lock. iIntros (mu_l) "Hlock".
    wp_alloc l as "Hptr".
    iApply struct_fields_split in "Hptr".
    iNamed "Hptr".
    iMod (struct_field_pointsto_persist with "mu") as "mu".
    iMod (alloc_lock N _ _ (lock_inv l P)
           with "Hlock [HP val]") as "Hlock".
    { iFrame. }
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_atomicPtr__load l (P: loc → iProp _) (Q: loc → iProp Σ) :
    {{{ is_atomic_ptr l P ∗ (∀ x, P x -∗ |={⊤}=> Q x ∗ P x) }}}
      atomicPtr__load #l
    {{{ (x: loc), RET #x; Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]".
    iNamed "Hint".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    repeat (wp_loadField || wp_storeField).

    iMod ("Hfupd" with "HP") as "[HQ HP]".

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP val]").
    { iFrame. }

    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_atomicPtr__store l (P: loc → iProp _) (Q: loc → iProp _) (y: loc) :
    {{{ is_atomic_ptr l P ∗
          (∀ x, P x -∗ |={⊤}=> Q x ∗ P y) }}}
      atomicPtr__store #l #y
    {{{ (x: loc), RET #(); Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]".
    iNamed "Hint".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Hinv]". iNamed "Hinv".
    repeat (wp_loadField || wp_storeField).
    iMod ("Hfupd" with "HP") as "[HQ HP]".

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP val]").
    { iFrame. }

    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

End proof.

#[global] Typeclasses Opaque is_atomic_ptr.

End atomic_ptr.

Import atomic_ptr.

Section proof.
  Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}.
  Context `{!ghost_varG Σ (gmap w64 w64)}.

  Definition ptr_rep (γ: gname) (P: gmap w64 w64 → iProp _) (mref: loc): iProp _ :=
      ∃ (m: gmap w64 w64),
      "#Hm_clean" ∷ own_map mref DfracDiscarded m ∗
      "HP" ∷ P m ∗
      "Hm_var" ∷ ghost_var γ (1/2) m
      .

  Definition lock_inv (γ: gname): iProp _ :=
    ∃ (m: gmap w64 w64),
     "Hm_lock" ∷ ghost_var γ (1/2) m
     .

  (* Recall that the [P] argument is a representation invariant from the user of
     the hashmap, which we need to maintain. Intuitively, [P m] should always hold
     for some [m] that is the logically current state of the hashmap.

    This hashmap implementation has an atomic pointer to a read-only copy of the
    map. Writes do a deep copy of the map to avoid disturbing reads.

    The know from the state that the invariant for the hashmap consists of two
    pieces: the representation predicate for the atomic pointer, and the lock
    invariant. It turns out these two are enough (and we won't need a separate
    invariant). Notice that we have the _caller_'s representation predicate [P]
    for the actual map value, as well as the internal _hashmap_ predicate
    [ptr_rep] for the map reference itself. We can guess that [ptr_rep] must
    contain the caller's [P], since reads don't use the lock and yet still must
    read the current value of the map.

    For writes, each operation gets the current value of the map, does a deep
    copy (to allow modifications), and then stores the new map. We need a lock
    to prevent a concurrent write from overlapping (think about how a write
    could be lost if we didn't). So, the lock invariant captures that the
    logical value of the map is frozen while the lock is held. We implement that
    in Iris with a ghost variable whose value is the current map value - in
    addition to maintaining [P m], we'll also have [ghost_var γ q m]. That ghost
    variable will be half owned by the atomic pointer (since it needs to match
    the physical state), and half owned by the _lock invariant_. This means upon
    acquiring the lock the write operation knows the current value of the map
    can no longer change, while still allowing reads.
   *)

  Definition is_hashmap (l: loc) (P: gmap w64 w64 → iProp _): iProp _ :=
    ∃ (ptr_l mu_l: loc) γ,
    "#clean" ∷ l ↦[HashMap :: "clean"]□ #ptr_l ∗
    "#mu" ∷ l ↦[HashMap :: "mu"]□ #mu_l ∗
    "#Hclean" ∷ is_atomic_ptr ptr_l (ptr_rep γ P) ∗
    "#Hlock" ∷ is_lock nroot (#mu_l) (lock_inv γ)
    .

  #[global] Instance is_hashmap_persistent l P : Persistent (is_hashmap l P) := _.

  Lemma wp_NewHashMap (P: gmap w64 w64 → iProp _) :
    {{{ P ∅ }}}
      NewHashMap #()
    {{{ (l: loc), RET #l; is_hashmap l P }}}.
  Proof.
    wp_start as "HP".
    wp_apply (wp_NewMap w64 w64).
    iIntros (mref) "Hm".
    iMod (own_map_persist with "Hm") as "#Hm".
    wp_apply (wp_ref_to); [ val_ty | ].
    iIntros (m_l) "m".
    wp_load.
    iMod (ghost_var_alloc (∅: gmap w64 w64)) as (γ) "[Hm_var Hm_lock]".
    wp_apply (wp_newAtomicPtr (ptr_rep γ P) with "[Hm_var $HP]").
    { iFrame "∗#". }
    iIntros (ptr_l) "Hclean".
    wp_apply (wp_newMutex nroot _ (lock_inv γ) with "[$Hm_lock]").
    iIntros (mu_l) "Hlock".
    rewrite -wp_fupd.
    wp_alloc l as "Hmap".
    iApply struct_fields_split in "Hmap". iNamed "Hmap".
    iMod (struct_field_pointsto_persist with "clean") as "clean".
    iMod (struct_field_pointsto_persist with "mu") as "mu".
    iApply "HΦ".
    iFrame "∗#".
    done.
  Qed.

  Lemma wp_mapClone mref (m: gmap w64 w64) :
    {{{ own_map mref DfracDiscarded m }}}
      mapClone #mref
    {{{ (mref': loc), RET #mref';
      own_map mref' (DfracOwn 1) m }}}.
  Proof.
    wp_start as "#Hm".
    wp_apply (wp_NewMap w64 w64).
    iIntros (mref') "Hm_new".
    wp_pures.
    wp_apply (wp_MapIter_2 (K:=w64) (V:=w64) _ _ _ _ _ (λ mtodo mdone,
      own_map mref' (DfracOwn 1) mdone
    )%I with "[$Hm] [$Hm_new]").
    { clear Φ.
      iIntros (k v mtodo mdone).
      iIntros "!>" (Φ) "Hpre HΦ".
      iDestruct "Hpre" as "[Hm_new %Hget]".
      wp_apply (wp_MapInsert w64 w64 v with "[$Hm_new]").
      { eauto. }
      iIntros "Hm_new".
      iApply "HΦ".
      rewrite /typed_map.map_insert.
      iFrame. }

    iIntros "[_ Hm_new]".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_HashMap__Load l (key: w64) (P: gmap w64 w64 → iProp _)
    (Q: (w64 * bool) → iProp _) :
  {{{ is_hashmap l P ∗ (∀ m, P m ={⊤}=∗ Q (map_get m key) ∗ P m) }}}
    HashMap__Load #l #key
  {{{ (v: w64) (ok: bool), RET (#v, #ok); Q (v, ok) }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]".
    iNamed "Hmap".
    wp_pures.
    wp_loadField.
    wp_apply (wp_atomicPtr__load _ _ (λ mref,
      ∃ m, own_map mref DfracDiscarded m ∗
      Q (map_get m key)
    )%I with "[$Hclean Hfupd]").

    { iIntros (mref) "Hrep". iNamed "Hrep".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "#∗". }

    iIntros (mref) "(%m & #Hclean_map & HQ)".
    wp_pures.
    wp_apply (wp_MapGet with "[$Hclean_map]").
    iIntros (v ok) "[%Hget _]".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    rewrite Hget. iFrame.
  Qed.

  (* The spec of this helper is a bit complicated since it is called with the
  lock held, hence a decent amount of context has to be passed in the
  precondition. The important part of the spec is that [m] is the current
  abstract state due to the [ghost_var] premise, and it is exactly the map
  returned as physical state. We can also see the spec returns [own_map] with a
  fraction of [1] due to the deep copy here. *)
  Lemma wp_HashMap__dirty (γ: gname) l (ptr_l: loc) (P: gmap w64 w64 → iProp _) (m: gmap w64 w64) :
    {{{ "#clean" ∷ l ↦[HashMap :: "clean"]□ #ptr_l ∗
        "#Hclean" ∷ is_atomic_ptr ptr_l (ptr_rep γ P) ∗
        "Hm_lock" ∷ ghost_var γ (1/2) m }}}
      HashMap__dirty #l
    {{{ (mref: loc), RET #mref;
      own_map mref (DfracOwn 1) m ∗
      ghost_var γ (1/2) m }}}.
  Proof.
    wp_start as "Hpre". iNamed "Hpre".
    wp_loadField.
    wp_apply (wp_atomicPtr__load _ _ (λ mref,
      (* the important part is that this [m] matches the one in the precondition, because of the ghost variable *)
     own_map mref DfracDiscarded m ∗ ghost_var γ (1/2) m)%I
     with "[$Hclean Hm_lock]").
    { iIntros (mref) "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iModIntro. iFrame "#∗". }
      iIntros (mref) "(Hclean_m & Hm)".
      wp_pures.
      wp_apply (wp_mapClone with "Hclean_m").
      iIntros (mref') "Hdirty".
      iApply "HΦ".
      iFrame.
  Qed.

  Lemma wp_HashMap__Store l (key: w64) (val: w64) (P: gmap w64 w64 → iProp _)
    (Q: gmap w64 w64 → iProp _) :
  {{{ is_hashmap l P ∗
      (∀ m, P m ={⊤}=∗ Q m ∗ P (map_insert key val m)) }}}
    HashMap__Store #l #key #val
  {{{ m, RET #(); Q m }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]".
    iNamed "Hmap".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_pures.
    wp_apply (wp_MapInsert w64 w64 val with "Hdirty").
    { done. }
    rewrite /typed_map.map_insert.
    iIntros "Hm".
    iMod (own_map_persist with "Hm") as "#Hm_new".
    wp_loadField.
    wp_apply (wp_atomicPtr__store _ _
      (λ _, Q m ∗ ghost_var γ (1/2) (map_insert key val m))%I
     with "[$Hclean Hfupd Hm_lock]").
    { iIntros (mref') "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iMod (ghost_var_update_halves (map_insert key val m) with "Hm_lock Hm_var") as "[Hm_lock Hm_var]".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "∗#". }
    iIntros (_) "[HQ Hm_lock]".
    wp_pures. wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
    { iFrame. }
    wp_pures.
    iModIntro. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_HashMap__Delete l (key: w64) (P: gmap w64 w64 → iProp _)
    (Q: gmap w64 w64 → iProp _) :
  {{{ is_hashmap l P ∗
      (∀ m, P m ={⊤}=∗ Q m ∗ P (delete key m)) }}}
    HashMap__Delete #l #key
  {{{ m, RET #(); Q m }}}.
  Proof.
    wp_start as "[#Hmap Hfupd]".
    iNamed "Hmap".
    wp_pures.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[Hlocked Hinv]".
    iNamed "Hinv".
    wp_apply (wp_HashMap__dirty with "[$clean $Hclean $Hm_lock]").
    iIntros (mref) "[Hdirty Hm_lock]".
    wp_pures.
    wp_apply (wp_MapDelete w64 w64 with "Hdirty").
    rewrite /map_del.
    iIntros "Hm".
    iMod (own_map_persist with "Hm") as "#Hm_new".
    wp_loadField.
    wp_apply (wp_atomicPtr__store _ _
      (λ _, Q m ∗ ghost_var γ (1/2) (delete key m))%I
     with "[$Hclean Hfupd Hm_lock]").
    { iIntros (mref') "Hrep". iNamed "Hrep".
      iDestruct (ghost_var_agree with "Hm_lock Hm_var") as %<-.
      iMod (ghost_var_update_halves (map_delete key m) with "Hm_lock Hm_var") as "[Hm_lock Hm_var]".
      iMod ("Hfupd" with "HP") as "[HQ HP]".
      iModIntro.
      iFrame "∗#". }
      iIntros (_) "[HQ Hm_lock]".
      wp_pures. wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked Hm_lock]").
      { iFrame. }
      wp_pures.
      iModIntro. iApply "HΦ". iFrame.
    Qed.

End proof.

#[global] Typeclasses Opaque is_hashmap.
