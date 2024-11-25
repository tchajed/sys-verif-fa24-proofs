(* autogenerated from sys_verif_code/sharded_hashmap *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

(* entries.go *)

Definition entry := struct.decl [
  "key" :: uint32T;
  "val" :: uint64T
].

Definition entryShard := struct.decl [
  "entries" :: slice.T (struct.t entry)
].

Definition entryShard__Get: val :=
  rec: "entryShard__Get" "es" "key" :=
    let: "entries" := struct.loadF entryShard "entries" "es" in
    let: "found" := ref_to boolT #false in
    let: "val" := ref_to uint64T #0 in
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (slice.len "entries")); (λ: <>, Skip) := λ: <>,
      let: "e" := SliceGet (struct.t entry) "entries" (![uint64T] "i") in
      (if: (struct.get entry "key" "e") = "key"
      then
        "found" <-[boolT] #true;;
        "val" <-[uint64T] (struct.get entry "val" "e");;
        Break
      else
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    (![uint64T] "val", ![boolT] "found").

Definition entryShard__Store: val :=
  rec: "entryShard__Store" "es" "key" "val" :=
    let: "found" := ref_to boolT #false in
    let: "i" := ref_to uint64T #0 in
    let: "l" := slice.len (struct.loadF entryShard "entries" "es") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < "l"); (λ: <>, Skip) := λ: <>,
      (if: (struct.get entry "key" (SliceGet (struct.t entry) (struct.loadF entryShard "entries" "es") (![uint64T] "i"))) = "key"
      then
        "found" <-[boolT] #true;;
        Break
      else
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    (if: ![boolT] "found"
    then
      SliceSet (struct.t entry) (struct.loadF entryShard "entries" "es") (![uint64T] "i") (struct.mk entry [
        "key" ::= "key";
        "val" ::= "val"
      ]);;
      #()
    else
      struct.storeF entryShard "entries" "es" (SliceAppend (struct.t entry) (struct.loadF entryShard "entries" "es") (struct.mk entry [
        "key" ::= "key";
        "val" ::= "val"
      ]));;
      #()).

(* shard.go *)

Definition shard := struct.decl [
  "m" :: mapT uint64T
].

Definition newShard: val :=
  rec: "newShard" <> :=
    struct.new shard [
      "m" ::= NewMap uint64T uint64T #()
    ].

Definition shard__Load: val :=
  rec: "shard__Load" "s" "key" :=
    let: ("v", "ok") := MapGet (struct.loadF shard "m" "s") (to_u64 "key") in
    ("v", "ok").

Definition shard__Store: val :=
  rec: "shard__Store" "s" "key" "v" :=
    MapInsert (struct.loadF shard "m" "s") (to_u64 "key") "v";;
    #().

(* sharded_hashmap.go *)

Definition hash: val :=
  rec: "hash" "key" :=
    let: "h" := ref_to uint32T #(U32 5381) in
    let: "k" := #(U32 17000069) in
    "h" <-[uint32T] (((![uint32T] "h") * "k") + ("key" `and` #(U32 255)));;
    "h" <-[uint32T] (((![uint32T] "h") * "k") + (("key" ≫ #8) `and` #(U32 255)));;
    "h" <-[uint32T] (((![uint32T] "h") * "k") + (("key" ≫ #16) `and` #(U32 255)));;
    "h" <-[uint32T] (((![uint32T] "h") * "k") + (("key" ≫ #24) `and` #(U32 255)));;
    ![uint32T] "h".

Definition bucket := struct.decl [
  "mu" :: ptrT;
  "subMap" :: ptrT
].

Definition HashMap := struct.decl [
  "buckets" :: slice.T ptrT
].

Definition newBucket: val :=
  rec: "newBucket" <> :=
    struct.new bucket [
      "mu" ::= newMutex #();
      "subMap" ::= newShard #()
    ].

Definition createNewBuckets: val :=
  rec: "createNewBuckets" "newSize" :=
    let: "newBuckets" := ref_to (slice.T ptrT) (NewSlice ptrT #0) in
    let: "numBuckets" := to_u64 "newSize" in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "numBuckets"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      "newBuckets" <-[slice.T ptrT] (SliceAppend ptrT (![slice.T ptrT] "newBuckets") (newBucket #()));;
      Continue);;
    ![slice.T ptrT] "newBuckets".

Definition NewHashMap: val :=
  rec: "NewHashMap" "size" :=
    struct.new HashMap [
      "buckets" ::= createNewBuckets "size"
    ].

Definition bucketIdx: val :=
  rec: "bucketIdx" "key" "numBuckets" :=
    to_u64 ((hash "key") `rem` (to_u32 "numBuckets")).

Definition HashMap__Load: val :=
  rec: "HashMap__Load" "hm" "key" :=
    let: "buckets" := struct.loadF HashMap "buckets" "hm" in
    let: "b" := SliceGet ptrT "buckets" (bucketIdx "key" (slice.len "buckets")) in
    Mutex__Lock (struct.loadF bucket "mu" "b");;
    let: ("x", "ok") := shard__Load (struct.loadF bucket "subMap" "b") "key" in
    Mutex__Unlock (struct.loadF bucket "mu" "b");;
    ("x", "ok").

Definition HashMap__Store: val :=
  rec: "HashMap__Store" "hm" "key" "val" :=
    let: "buckets" := struct.loadF HashMap "buckets" "hm" in
    let: "b" := SliceGet ptrT "buckets" (bucketIdx "key" (slice.len "buckets")) in
    Mutex__Lock (struct.loadF bucket "mu" "b");;
    shard__Store (struct.loadF bucket "subMap" "b") "key" "val";;
    Mutex__Unlock (struct.loadF bucket "mu" "b");;
    #().

End code.
