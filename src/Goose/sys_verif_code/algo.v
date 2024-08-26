(* autogenerated from sys_verif_code/algo *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition Person := struct.decl [
  "Name" :: stringT;
  "Age" :: uint64T
].

Definition Sort: val :=
  rec: "Sort" "arr" :=
    let: "l" := slice.len "arr" in
    let: "l_m_1" := "l" - #1 in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "l"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      let: "j" := ref_to uint64T #0 in
      (for: (λ: <>, (![uint64T] "j") < "l_m_1"); (λ: <>, "j" <-[uint64T] ((![uint64T] "j") + #1)) := λ: <>,
        (if: (struct.get Person "Age" (SliceGet (struct.t Person) "arr" (![uint64T] "j"))) > (struct.get Person "Age" (SliceGet (struct.t Person) "arr" ((![uint64T] "j") + #1)))
        then
          let: "tmp" := SliceGet (struct.t Person) "arr" (![uint64T] "j") in
          SliceSet (struct.t Person) "arr" (![uint64T] "j") (SliceGet (struct.t Person) "arr" ((![uint64T] "j") + #1));;
          SliceSet (struct.t Person) "arr" ((![uint64T] "j") + #1) "tmp";;
          Continue
        else Continue));;
      Continue);;
    #().

End code.