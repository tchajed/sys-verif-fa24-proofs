(* autogenerated from sys_verif_code/hashmap *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.
Local Coercion Var' s: expr := Var s.

Definition atomicPtr := struct.decl [
  "mu" :: ptrT;
  "val" :: mapT uint64T
].

Definition newAtomicPtr: val :=
  rec: "newAtomicPtr" "m" :=
    struct.new atomicPtr [
      "mu" ::= lock.new #();
      "val" ::= "m"
    ].

Definition atomicPtr__load: val :=
  rec: "atomicPtr__load" "a" :=
    lock.acquire (struct.loadF atomicPtr "mu" "a");;
    let: "val" := struct.loadF atomicPtr "val" "a" in
    lock.release (struct.loadF atomicPtr "mu" "a");;
    "val".

Definition atomicPtr__store: val :=
  rec: "atomicPtr__store" "a" "m" :=
    lock.acquire (struct.loadF atomicPtr "mu" "a");;
    struct.storeF atomicPtr "val" "a" "m";;
    lock.release (struct.loadF atomicPtr "mu" "a");;
    #().

(* A HashMap that supports concurrent reads by deep-cloning the map on every
   write.

   Modeled on DeepCopyMap in Go's [map_reference_test.go].

   (note that this is a reference implementation for testing the more
   sophisticated and actually used [sync.Map] implementation)

   [map_reference_test.go]: https://cs.opensource.google/go/go/+/refs/tags/go1.22.5:src/sync/map_reference_test.go
   [sync.Map]: https://pkg.go.dev/sync#Map *)
Definition HashMap := struct.decl [
  "clean" :: ptrT;
  "mu" :: ptrT
].

Definition NewHashMap: val :=
  rec: "NewHashMap" <> :=
    let: "m" := ref_to (mapT uint64T) (NewMap uint64T uint64T #()) in
    struct.new HashMap [
      "clean" ::= newAtomicPtr (![mapT uint64T] "m");
      "mu" ::= lock.new #()
    ].

Definition HashMap__Load: val :=
  rec: "HashMap__Load" "h" "key" :=
    let: "clean" := atomicPtr__load (struct.loadF HashMap "clean" "h") in
    let: ("value", "ok") := MapGet "clean" "key" in
    ("value", "ok").

(* Clone the input map by copying all values. *)
Definition mapClone: val :=
  rec: "mapClone" "m" :=
    let: "clone" := NewMap uint64T uint64T #() in
    MapIter "m" (λ: "k" "v",
      MapInsert "clone" "k" "v");;
    "clone".

(* Assuming mu is held, return an owned copy of the current clean map. *)
Definition HashMap__dirty: val :=
  rec: "HashMap__dirty" "h" :=
    let: "clean" := atomicPtr__load (struct.loadF HashMap "clean" "h") in
    mapClone "clean".

Definition HashMap__Store: val :=
  rec: "HashMap__Store" "h" "key" "value" :=
    lock.acquire (struct.loadF HashMap "mu" "h");;
    let: "dirty" := HashMap__dirty "h" in
    MapInsert "dirty" "key" "value";;
    atomicPtr__store (struct.loadF HashMap "clean" "h") "dirty";;
    lock.release (struct.loadF HashMap "mu" "h");;
    #().

Definition HashMap__Delete: val :=
  rec: "HashMap__Delete" "h" "key" :=
    lock.acquire (struct.loadF HashMap "mu" "h");;
    let: "dirty" := HashMap__dirty "h" in
    MapDelete "dirty" "key";;
    atomicPtr__store (struct.loadF HashMap "clean" "h") "dirty";;
    lock.release (struct.loadF HashMap "mu" "h");;
    #().

End code.
