From Perennial.goose_lang Require Import lang lifting typing.

#[export] Instance empty_ext : ffi_syntax :=
  {| ffi_opcode := Empty_set;
     ffi_val := Empty_set;
  |}.

#[export] Instance empty_model : ffi_model :=
  {| ffi_state := unit;
     ffi_global_state := unit;
  |}.

#[export] Instance empty_ffi_interp : ffi_interp empty_model :=
    {| ffiLocalGS := λ _, unit;
       ffiGlobalGS _ := unit;
       ffi_local_ctx Σ _ (d: @ffi_state empty_model) := True%I;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ _ (d: @ffi_state empty_model) := True%I;
       ffi_global_start _ _ _ := True%I;
       ffi_restart := fun _ _ (d: @ffi_state empty_model) => True%I;
       ffi_crash_rel Σ hF1 σ1 hF2 σ2 := True%I;
    |}.

#[export] Instance empty_semantics : ffi_semantics empty_ext empty_model :=
  {| ffi_step := λ op v, Transitions.runF (λ s, (s, Val v));
    ffi_crash_step := λ _ _, True |}.

#[export] Instance empty_val_ty : val_types :=
  {| ext_tys :=  Empty_set; |}.

#[export] Instance empty_types : ext_types empty_ext :=
  {| val_tys := empty_val_ty;
    get_ext_tys := λ v '(t1, t2), True;
  |}.
