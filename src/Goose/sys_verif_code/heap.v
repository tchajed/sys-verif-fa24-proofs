(* autogenerated from sys_verif_code/heap *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

(* binary_search.go *)

(* BinarySearch looks for needle in the sorted list s. It returns (index, found)
   where if found = false, needle is not present in s, and if found = true, s[index]
   == needle.

   If needle appears multiple times in s, no guarantees are made about which of
   those indices is returned. *)
Definition BinarySearch: val :=
  rec: "BinarySearch" "s" "needle" :=
    let: "i" := ref_to uint64T #0 in
    let: "j" := ref_to uint64T (slice.len "s") in
    Skip;;
    (for: (λ: <>, (![uint64T] "i") < (![uint64T] "j")); (λ: <>, Skip) := λ: <>,
      let: "mid" := (![uint64T] "i") + (((![uint64T] "j") - (![uint64T] "i")) `quot` #2) in
      (if: (SliceGet uint64T "s" "mid") < "needle"
      then
        "i" <-[uint64T] ("mid" + #1);;
        Continue
      else
        "j" <-[uint64T] "mid";;
        Continue));;
    (if: (![uint64T] "i") < (slice.len "s")
    then (![uint64T] "i", (SliceGet uint64T "s" (![uint64T] "i")) = "needle")
    else (![uint64T] "i", #false)).

(* exercises.go *)

Definition ExampleA: val :=
  rec: "ExampleA" "x" "y" "z" :=
    (if: ![boolT] "x"
    then
      "y" <-[uint64T] "z";;
      #()
    else
      "y" <-[uint64T] #0;;
      #()).

Definition ExampleB: val :=
  rec: "ExampleB" "x" "y" "z" :=
    (if: ![boolT] "x"
    then
      control.impl.Assert ("z" = #0);;
      "y" <-[uint64T] "z";;
      #()
    else
      "y" <-[uint64T] #0;;
      #()).

Definition S1 := struct.decl [
  "a" :: uint64T;
  "b" :: slice.T byteT
].

Definition ExampleC: val :=
  rec: "ExampleC" "x" :=
    (if: (struct.loadF S1 "a" "x") = #0
    then #(str"false")
    else #(str"true")).

Definition ExampleD: val :=
  rec: "ExampleD" "x" :=
    control.impl.Assert ((struct.loadF S1 "a" "x") = (slice.len (struct.loadF S1 "b" "x")));;
    SliceGet byteT (struct.loadF S1 "b" "x") #0.

Definition ExampleE: val :=
  rec: "ExampleE" "x" "y" :=
    struct.storeF S1 "a" "y" (struct.get S1 "a" "x");;
    struct.storeF S1 "b" "y" slice.nil;;
    #().

Definition collatzF: val :=
  rec: "collatzF" "x" :=
    (if: ("x" `rem` #2) = #0
    then "x" `quot` #2
    else (#3 * "x") + #1).

Definition collatzIter: val :=
  rec: "collatzIter" "x" "n" :=
    (if: "n" = #0
    then "x"
    else "collatzIter" (collatzF "x") ("n" - #1)).

Definition ExampleG: val :=
  rec: "ExampleG" <> :=
    collatzIter #12 #9.

(* heap.go *)

Definition Swap: val :=
  rec: "Swap" "x" "y" :=
    let: "old_y" := ![uint64T] "y" in
    "y" <-[uint64T] (![uint64T] "x");;
    "x" <-[uint64T] "old_y";;
    #().

(* IgnoreOneLocF has a specification that shows it does not need ownership of
   its second argument. *)
Definition IgnoreOneLocF: val :=
  rec: "IgnoreOneLocF" "x" "y" :=
    control.impl.Assert ((![uint64T] "x") = #0);;
    "x" <-[uint64T] #42;;
    #().

(* UseIgnoreOneLocOwnership uses IgnoreOneLocF and can be verified using its
   specification. *)
Definition UseIgnoreOneLocOwnership: val :=
  rec: "UseIgnoreOneLocOwnership" <> :=
    let: "x" := ref_to uint64T #0 in
    let: "y" := ref_to uint64T #42 in
    IgnoreOneLocF "x" "y";;
    control.impl.Assert ((![uint64T] "x") = (![uint64T] "y"));;
    #().

(* CopySlice copies from src to dst

   dst must be at least as long as src *)
Definition CopySlice: val :=
  rec: "CopySlice" "dst" "src" :=
    let: "l" := slice.len "dst" in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, (![uint64T] "i") < "l"); (λ: <>, "i" <-[uint64T] ((![uint64T] "i") + #1)) := λ: <>,
      SliceSet byteT "dst" (![uint64T] "i") (SliceGet byteT "src" (![uint64T] "i"));;
      Continue);;
    #().

Definition StackEscape: val :=
  rec: "StackEscape" <> :=
    let: "x" := ref_to uint64T #42 in
    "x".

(* linked_list.go *)

Definition Node := struct.decl [
  "elem" :: uint64T;
  "next" :: ptrT
].

Definition NewList: val :=
  rec: "NewList" <> :=
    let: "l" := ref (zero_val ptrT) in
    ![ptrT] "l".

Definition Node__Insert: val :=
  rec: "Node__Insert" "l" "elem" :=
    struct.new Node [
      "elem" ::= "elem";
      "next" ::= "l"
    ].

Definition Node__Pop: val :=
  rec: "Node__Pop" "l" :=
    (if: "l" = #null
    then (#0, "l", #false)
    else (struct.loadF Node "elem" "l", struct.loadF Node "next" "l", #true)).

Definition Node__Contains: val :=
  rec: "Node__Contains" "l" "elem" :=
    let: "n" := ref_to ptrT "l" in
    let: "found" := ref_to boolT #false in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![ptrT] "n") = #null
      then Break
      else
        (if: (struct.loadF Node "elem" (![ptrT] "n")) = "elem"
        then
          "found" <-[boolT] #true;;
          Break
        else
          "n" <-[ptrT] (struct.loadF Node "next" (![ptrT] "n"));;
          Continue)));;
    ![boolT] "found".

Definition Node__Delete: val :=
  rec: "Node__Delete" "l" "elem" :=
    (if: "l" = #null
    then "l"
    else
      (if: (struct.loadF Node "elem" "l") = "elem"
      then "Node__Delete" (struct.loadF Node "next" "l") "elem"
      else
        struct.storeF Node "next" "l" ("Node__Delete" (struct.loadF Node "next" "l") "elem");;
        "l")).

Definition Node__Append: val :=
  rec: "Node__Append" "l" "other" :=
    (if: "l" = #null
    then "other"
    else
      struct.new Node [
        "elem" ::= struct.loadF Node "elem" "l";
        "next" ::= "Node__Append" (struct.loadF Node "next" "l") "other"
      ]).

(* majority_vote.go *)

(* FindMajority finds an `x` that appears in the slice `a` more than half the
   time.

   That is, if there is some x that appears in a strictly more than `len(a)/2`
   times, then `FindMajority` will return it.

   This implementation of the algorithm comes from _Program Proofs_ by K. Rustan
   M. Leino in chapter 13.7. *)
Definition FindMajority (T:ty): val :=
  rec: "FindMajority" "a" :=
    let: "k" := ref_to T (SliceGet T "a" #0) in
    let: "lo" := ref_to uint64T #0 in
    let: "hi" := ref_to uint64T #1 in
    let: "c" := ref_to uint64T #1 in
    let: "l" := slice.len "a" in
    Skip;;
    (for: (λ: <>, (![uint64T] "hi") < "l"); (λ: <>, Skip) := λ: <>,
      (if: (SliceGet T "a" (![uint64T] "hi")) = (![T] "k")
      then
        "hi" <-[uint64T] ((![uint64T] "hi") + #1);;
        "c" <-[uint64T] ((![uint64T] "c") + #1)
      else
        (if: (((![uint64T] "hi") + #1) - (![uint64T] "lo")) < (#2 * (![uint64T] "c"))
        then "hi" <-[uint64T] ((![uint64T] "hi") + #1)
        else "hi" <-[uint64T] ((![uint64T] "hi") + #1)));;
      (if: (![uint64T] "hi") = "l"
      then Break
      else
        "k" <-[T] (SliceGet T "a" (![uint64T] "hi"));;
        "lo" <-[uint64T] (![uint64T] "hi");;
        "hi" <-[uint64T] ((![uint64T] "hi") + #1);;
        "c" <-[uint64T] #1;;
        Continue));;
    ![T] "k".

(* queue.go *)

Definition Stack := struct.decl [
  "elements" :: slice.T uint64T
].

Definition NewStack: val :=
  rec: "NewStack" <> :=
    struct.new Stack [
      "elements" ::= NewSlice uint64T #0
    ].

Definition Stack__Push: val :=
  rec: "Stack__Push" "s" "x" :=
    struct.storeF Stack "elements" "s" (SliceAppend uint64T (struct.loadF Stack "elements" "s") "x");;
    #().

(* Pop returns the most recently pushed element. The boolean indicates success,
   which is false if the stack was empty. *)
Definition Stack__Pop: val :=
  rec: "Stack__Pop" "s" :=
    (if: (slice.len (struct.loadF Stack "elements" "s")) = #0
    then (#0, #false)
    else
      let: "x" := SliceGet uint64T (struct.loadF Stack "elements" "s") ((slice.len (struct.loadF Stack "elements" "s")) - #1) in
      struct.storeF Stack "elements" "s" (SliceTake (struct.loadF Stack "elements" "s") ((slice.len (struct.loadF Stack "elements" "s")) - #1));;
      ("x", #true)).

Definition Queue := struct.decl [
  "back" :: ptrT;
  "front" :: ptrT
].

Definition NewQueue: val :=
  rec: "NewQueue" <> :=
    struct.mk Queue [
      "back" ::= NewStack #();
      "front" ::= NewStack #()
    ].

Definition Queue__Push: val :=
  rec: "Queue__Push" "q" "x" :=
    Stack__Push (struct.get Queue "back" "q") "x";;
    #().

Definition Queue__emptyBack: val :=
  rec: "Queue__emptyBack" "q" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: ("x", "ok") := Stack__Pop (struct.get Queue "back" "q") in
      (if: "ok"
      then
        Stack__Push (struct.get Queue "front" "q") "x";;
        Continue
      else Break));;
    #().

Definition Queue__Pop: val :=
  rec: "Queue__Pop" "q" :=
    let: ("x", "ok") := Stack__Pop (struct.get Queue "front" "q") in
    (if: "ok"
    then ("x", #true)
    else
      Queue__emptyBack "q";;
      let: ("x", "ok2") := Stack__Pop (struct.get Queue "front" "q") in
      ("x", "ok2")).

(* search_tree.go *)

Definition SearchTree := struct.decl [
  "key" :: uint64T;
  "left" :: ptrT;
  "right" :: ptrT
].

Definition NewSearchTree: val :=
  rec: "NewSearchTree" <> :=
    let: "s" := ref (zero_val ptrT) in
    ![ptrT] "s".

Definition singletonTree: val :=
  rec: "singletonTree" "key" :=
    let: "s" := ref (zero_val ptrT) in
    struct.new SearchTree [
      "key" ::= "key";
      "left" ::= ![ptrT] "s";
      "right" ::= ![ptrT] "s"
    ].

Definition SearchTree__Insert: val :=
  rec: "SearchTree__Insert" "t" "key" :=
    (if: "t" = #null
    then singletonTree "key"
    else
      (if: "key" < (struct.loadF SearchTree "key" "t")
      then struct.storeF SearchTree "left" "t" ("SearchTree__Insert" (struct.loadF SearchTree "left" "t") "key")
      else
        (if: (struct.loadF SearchTree "key" "t") < "key"
        then struct.storeF SearchTree "right" "t" ("SearchTree__Insert" (struct.loadF SearchTree "right" "t") "key")
        else #()));;
      "t").

Definition SearchTree__Contains: val :=
  rec: "SearchTree__Contains" "t" "key" :=
    (if: "t" = #null
    then #false
    else
      (if: "key" = (struct.loadF SearchTree "key" "t")
      then #true
      else
        (if: "key" < (struct.loadF SearchTree "key" "t")
        then "SearchTree__Contains" (struct.loadF SearchTree "left" "t") "key"
        else "SearchTree__Contains" (struct.loadF SearchTree "right" "t") "key"))).

(* struct.go *)

Definition Person := struct.decl [
  "FirstName" :: stringT;
  "LastName" :: stringT;
  "Age" :: uint64T
].

Definition Person__Name: val :=
  rec: "Person__Name" "p" :=
    ((struct.get Person "FirstName" "p") + #(str" ")) + (struct.get Person "LastName" "p").

Definition Person__Older: val :=
  rec: "Person__Older" "p" "delta" :=
    struct.storeF Person "Age" "p" ((struct.loadF Person "Age" "p") + "delta");;
    #().

Definition Person__GetAge: val :=
  rec: "Person__GetAge" "p" :=
    struct.fieldRef Person "Age" "p".

Definition ExamplePerson: val :=
  rec: "ExamplePerson" <> :=
    struct.mk Person [
      "FirstName" ::= #(str"Ada");
      "LastName" ::= #(str"Lovelace");
      "Age" ::= #25
    ].

Definition ExamplePersonRef: val :=
  rec: "ExamplePersonRef" <> :=
    struct.new Person [
      "FirstName" ::= #(str"Ada");
      "LastName" ::= #(str"Lovelace");
      "Age" ::= #25
    ].

Definition Person__BuggySetAge: val :=
  rec: "Person__BuggySetAge" "p" :=
    struct.storeF Person "Age" "p" ((struct.get Person "Age" "p") + #1);;
    #().

Definition Rect := struct.decl [
  "Width" :: uint64T;
  "Height" :: uint64T
].

Definition Rect__Area: val :=
  rec: "Rect__Area" "r" :=
    (struct.get Rect "Width" "r") * (struct.get Rect "Height" "r").

Definition Rect__IsSquare: val :=
  rec: "Rect__IsSquare" "r" :=
    (struct.get Rect "Width" "r") = (struct.get Rect "Height" "r").

Definition Rect__MakeSquare: val :=
  rec: "Rect__MakeSquare" "r" :=
    struct.storeF Rect "Height" "r" (struct.loadF Rect "Width" "r");;
    #().

End code.
