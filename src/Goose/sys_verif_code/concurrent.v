(* autogenerated from sys_verif_code/concurrent *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.

Section code.
Context `{ext_ty: ext_types}.

(* barrier.go *)

(* A simple barrier, very similar to a Go `sync.WaitGroup`. We prove a spec that
   allows only one thread to call `Wait()`, but subsequent calls will return
   immediately and the implementation should satisfy a more general
   specification. *)
Definition Barrier := struct.decl [
  "numWaiting" :: uint64T;
  "mu" :: ptrT;
  "cond" :: ptrT
].

(* Create a new barrier waiting for no threads. *)
Definition NewBarrier: val :=
  rec: "NewBarrier" <> :=
    let: "mu" := newMutex #() in
    let: "cond" := NewCond "mu" in
    struct.new Barrier [
      "numWaiting" ::= #0;
      "mu" ::= "mu";
      "cond" ::= "cond"
    ].

(* Add `n` threads that the barrier is waiting to call `Done()`. *)
Definition Barrier__Add: val :=
  rec: "Barrier__Add" "b" "n" :=
    Mutex__Lock (struct.loadF Barrier "mu" "b");;
    struct.storeF Barrier "numWaiting" "b" (std.SumAssumeNoOverflow (struct.loadF Barrier "numWaiting" "b") "n");;
    Mutex__Unlock (struct.loadF Barrier "mu" "b");;
    #().

(* Mark one thread as done. *)
Definition Barrier__Done: val :=
  rec: "Barrier__Done" "b" :=
    Mutex__Lock (struct.loadF Barrier "mu" "b");;
    (if: (struct.loadF Barrier "numWaiting" "b") = #0
    then Panic "Done() called too many times"
    else #());;
    struct.storeF Barrier "numWaiting" "b" ((struct.loadF Barrier "numWaiting" "b") - #1);;
    (if: (struct.loadF Barrier "numWaiting" "b") = #0
    then Cond__Broadcast (struct.loadF Barrier "cond" "b")
    else #());;
    Mutex__Unlock (struct.loadF Barrier "mu" "b");;
    #().

(* Wait blocks until all threads pending with `Add()` have called `Done()`. *)
Definition Barrier__Wait: val :=
  rec: "Barrier__Wait" "b" :=
    Mutex__Lock (struct.loadF Barrier "mu" "b");;
    Skip;;
    (for: (λ: <>, (struct.loadF Barrier "numWaiting" "b") > #0); (λ: <>, Skip) := λ: <>,
      Cond__Wait (struct.loadF Barrier "cond" "b");;
      Continue);;
    Mutex__Unlock (struct.loadF Barrier "mu" "b");;
    #().

(* concurrent.go *)

Definition AtomicInt := struct.decl [
  "x" :: uint64T;
  "mu" :: ptrT
].

Definition NewAtomicInt: val :=
  rec: "NewAtomicInt" <> :=
    struct.new AtomicInt [
      "x" ::= #0;
      "mu" ::= newMutex #()
    ].

Definition AtomicInt__Get: val :=
  rec: "AtomicInt__Get" "i" :=
    Mutex__Lock (struct.loadF AtomicInt "mu" "i");;
    let: "x" := struct.loadF AtomicInt "x" "i" in
    Mutex__Unlock (struct.loadF AtomicInt "mu" "i");;
    "x".

Definition AtomicInt__Inc: val :=
  rec: "AtomicInt__Inc" "i" "y" :=
    Mutex__Lock (struct.loadF AtomicInt "mu" "i");;
    struct.storeF AtomicInt "x" "i" ((struct.loadF AtomicInt "x" "i") + "y");;
    Mutex__Unlock (struct.loadF AtomicInt "mu" "i");;
    #().

Definition ParallelAdd1: val :=
  rec: "ParallelAdd1" <> :=
    let: "i" := NewAtomicInt #() in
    let: "h1" := std.Spawn (λ: <>,
      AtomicInt__Inc "i" #2;;
      #()
      ) in
    let: "h2" := std.Spawn (λ: <>,
      AtomicInt__Inc "i" #2;;
      #()
      ) in
    std.JoinHandle__Join "h1";;
    std.JoinHandle__Join "h2";;
    AtomicInt__Get "i".

Definition ParallelAdd2: val :=
  rec: "ParallelAdd2" <> :=
    let: "x" := ref_to uint64T #0 in
    let: "m" := newMutex #() in
    let: "b" := NewBarrier #() in
    Barrier__Add "b" #1;;
    Barrier__Add "b" #1;;
    Fork (Mutex__Lock "m";;
          "x" <-[uint64T] (std.SumAssumeNoOverflow (![uint64T] "x") #2);;
          Mutex__Unlock "m";;
          Barrier__Done "b");;
    Fork (Mutex__Lock "m";;
          "x" <-[uint64T] (std.SumAssumeNoOverflow (![uint64T] "x") #2);;
          Mutex__Unlock "m";;
          Barrier__Done "b");;
    Barrier__Wait "b";;
    Mutex__Lock "m";;
    let: "x_now" := ![uint64T] "x" in
    Mutex__Unlock "m";;
    "x_now".

End code.
