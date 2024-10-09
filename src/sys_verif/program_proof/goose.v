(*| # Lecture 11: Goose - Modeling and reasoning about Go

> Follow these notes in Coq at [src/sys_verif/program_proof/goose.v](https://github.com/tchajed/sys-verif-fa24-proofs/blob/main/src/sys_verif/program_proof/goose.v).

## Learning outcomes

By the end of this lecture, you should be able to:

1. Map from Go to its Goose translation, and back.
2. Explain what is trusted in a proof using Goose.
3. Read proof goals involving Goose pointers and structs.

---

## Motivation

So far, we have a way to specify and verify programs, but in a language that is too restrictive and that we can't run. On the other hand, the language is precisely defined so we know what our programs _do_ (by definition) and therefore what the proofs _mean_.

Now we want to turn our attention to executable code. This lecture outlines one way to do this.

The workflow is that we write the code we plan to run in Go, then translate it to an `expr`-like language in Coq, then do the proofs over the translated code. We concretely use a tool called [Goose](https://github.com/goose-lang/goose) that implements this for Go, translating to a language called GooseLang.

## High-level overview

What goes into making the Goose approach work?

First, we need to define GooseLang, the target of the translation. This language will look a lot like our `expr`s, but an important change is that values will be more realistic primitives - for example, we'll replace numbers of type $\mathbb{Z}$ with 64-bit unsigned integers. GooseLang has a precise semantics in the same style as the notes, a relation $(e, h) \leadsto (e', h')$ where $h$ is the heap, a (finite) map from locations to values.

Second, we need to translate Go to GooseLang. The basic idea is to translate each Go package to a Coq file, and each Go function to an expression. Go has structs and _methods_ on structs, which will be translated to GooseLang functions that take the struct as the first argument. Some complications we'll have to deal with when we get to the specifics include handling slices (variable-length arrays), concurrency, and loops.

Finally, we will prove useful reasoning principles about GooseLang that make it convenient to reason about the translation.

Of course, you, the reader, don't have to do these things; they're already done in Goose.

Here's a first taste of what this translation looks like:

```go
func Arith(a, b uint64) uint64 {
	sum := a + b
	if sum == 7 {
		return a
	}
	mid := Midpoint(a, b)
	return mid
}
```

translates to:

```coq
Definition Arith: val :=
  rec: "Arith" "a" "b" :=
    let: "sum" := "a" + "b" in
    (if: "sum" = #7
    then "a"
    else
      let: "mid" := Midpoint "a" "b" in
      "mid").
```

An important aspect of Goose (and any verification methodology for "real" code) is to ask, what do the proofs _mean_? Another way to think about this question is, what do we believe a verified specification says about the code, and what tools do we trust to make this happen?

We've already talked about how to interpret specifications in separation logic and won't go further into that part.

Goose _models_ Go code using GooseLang. You can see one evidence of this modeling above: whereas the Go code has a `return` statement to stop executing a function and return to the caller, the `Arith` in Coq (a `val`, which is a GooseLang value) instead is an expression that evaluates to an integer. If you compare the two you can convince yourself for this example that `Arith` in GooseLang, under the expected semantics you learned, evaluates to the same result as `Arith` in Go (assuming `Midpoint` is also translated correctly). When you use Goose to verify a program, you are essentially trusting that every function in that program has been modeled correctly.

## Goose details

### GooseLang

GooseLang has the following features:

- Values can be bytes, 64-bit integers, strings. As before, we have the unit value $()$ and functions as first-class values.
- Allocation supports arrays that get contiguous locations, to model slices.

In addition, GooseLang has some primitives related to concurrency:
- Pointer loads and stores are _non-atomic_ to model weak memory (we won't talk about this in class)
- Fork creates a new thread, used to model the `go f()` statement that spawns a "goroutine" running `f()`.
- A compare-and-exchange operation that is used in the translation of locks.

There are also some features we won't talk about:
- "External" functions and values allow reasoning about code that interacts with a disk, or distributed systems code.
- Prophecy variables, an advanced technique for doing proofs in concurrent separation logic.

### Local variables

Goose models immutable local variables as `let` bindings, vs using heap variables. In Go, it is permitted and safe to take the address of local variables; conceptually, they are all on the heap. The compiler does a simple _escape analysis_: if the analysis proves that a function's address is never used outside the function, then it is instead allocated on the stack.

One caveat about this "optimization": Goose translates variables declared with `x := ...` as immutable and variables declared as `var x = ...` as mutable; this is not a feature of Go, in which all local variables are mutable. A future version should probably do an analysis of the function rather than using the syntax.

```go
func StackEscape() *uint64 {
	var x = uint64(42)
	return &x // x has escaped! // [!code highlight]
}
```

```coq
Definition StackEscape: val :=
  rec: "StackEscape" <> :=
    let: "x" := ref_to uint64T #42 in
    "x".
```

Go also has a construct `new(T)` that allocates a pointer to a value of type `T` and initializes it to the _zero value_ of the type (and every type in Go has a well-defined zero value). Goose also supports this form of allocation, although allocating by taking the address of a heap variable is more common. (For structs, the most common pattern is actually `&S { ... }` - that is, taking the address of a struct literal.)

### Control flow

GooseLang has no special features for control flow. Instead, it must be modeled in the translation. The current translation handles specific, known patterns and is not fully general, thus there are control flow patterns that are not supported (for example, `return` inside a `for` loop). In those cases the translation fails and the developer must rewrite the code to avoid the tricky control flow. A new version of Goose (a significant rewrite) is in progress that will lift most of these limitations.

The `Arith` example above shows how an `if` statement with an early return is translated. Another set of control flow features is related to loops. Here's an example of a loop translation:

```go
// SumN adds up the numbers from 1 to n, with a loop.
func SumN(n uint64) uint64 {
	var sum = uint64(0)
	var i = uint64(1)
	for {
		if i > n {
			break
		}
		sum += i
		i++
	}
	return sum
}
```

```coq
Definition SumN: val :=
  rec: "SumN" "n" :=
    let: "sum" := ref_to uint64T #0 in
    let: "i" := ref_to uint64T #1 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (![uint64T] "i") > "n"
      then Break
      else
        "sum" <-[uint64T] ((![uint64T] "sum") + (![uint64T] "i"));;
        "i" <-[uint64T] ((![uint64T] "i") + #1);;
        Continue));;
    ![uint64T] "sum".
```

The (GooseLang) syntax `for:` is a very thin Notation around the following _model_ of (Go) `for` loops (the order of arguments differs though):

```coq
Definition For: val :=
  λ: "cond" "body" "post",
  (rec: "loop" <> :=
     let: "continue" :=
        (if: "cond" #()
         then "body" #()
         else #false) in
     if: "continue"
     then "post" #();; "loop" #()
     else #()) #().
```

The Go code `for e1; e2; e3 { body }` is translated (roughly) into `e1;; For e2 body e3`.

`For` takes three _functions_ as arguments: cond, body, and post. You can think of it as having the type `For : (unit -> bool) -> (unit -> unit) -> (unit -> unit) -> unit`, where `#() : unit` is the unit value in GooseLang. (You are welcome to think about these types but we don't actually have a type system for GooseLang, so it's only in your imagination.)

You might be confused by the `unit` argument each function takes: this is sometimes called a _thunk_ and is needed to prevent evaluating the condition, body, and post until they are needed in the loop. For example, if for the `cond` we passed a `bool` rather than a `unit -> bool` it would be a constant throughout the entire loop. A function that takes a unit isn't evaluated until desired by passing the argument.

::: info Exercise

Check your understanding: does the `cond` return `true` when the loop should stop or keep going? Try to figure out how this follows from the definition of `Fo`, not just your expectations.

Next, do you believe this is a correct model of `for` loops?

:::

|*)

(*| ### Proofs with Goose
|*)

From sys_verif.program_proof Require Import prelude empty_ffi.
From Goose.sys_verif_code Require heap functional.

Section goose.
Context `{hG: !heapGS Σ}.

Lemma wp_Add (n m: w64) :
  {{{ ⌜uint.Z n + uint.Z m < 2^64⌝ }}}
    functional.Add #n #m
  {{{ (y: w64), RET #y; ⌜(uint.Z y = uint.Z n + uint.Z m)%Z⌝ }}}.
Proof.
  wp_start as "%Hoverflow".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iPureIntro.
  word.
Qed.

Lemma wp_StackEscape :
  {{{ True }}}
    heap.StackEscape #()
  {{{ (l: loc), RET #l; l ↦[uint64T] #(W64 42) }}}.
Proof.
  wp_start as "_".
  wp_alloc x as "x".
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_SumNrec (n: w64) :
  {{{ ⌜uint.Z n * (uint.Z n + 1) / 2 < 2^64⌝ }}}
    functional.SumNrec #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  iIntros (Φ) "Hpre HΦ". iDestruct "Hpre" as %Hoverflow.
  iLöb as "IH" forall (n Hoverflow Φ).
  wp_rec. wp_pures.
  wp_if_destruct.
  - iModIntro.
    iApply "HΦ".
    iPureIntro.
    word.
  - wp_pures.
    wp_apply "IH".
    { iPureIntro.
      word. }
    iIntros (m Hm).
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    rewrite word.unsigned_add_nowrap.
    + rewrite Hm.
      word.
    + rewrite Hm. word.
Qed.

Lemma wp_SumN (n: w64) :
  {{{ True }}}
    functional.SumN #n
  {{{ (m: w64), RET #m; ⌜uint.Z m = uint.Z n * (uint.Z n + 1) / 2⌝ }}}.
Proof.
  wp_start as "_".
  wp_alloc sum_l as "sum".
  wp_alloc i_l as "i".
  wp_pures.
  wp_apply (wp_forBreak
              (λ continue,
                ∃ (sum i: w64),
                  "sum" :: sum_l ↦[uint64T] #sum ∗
                    "i" :: i_l ↦[uint64T] #i)%I
             with "[] [sum i]").
  - clear Φ.
    wp_start as "IH".
    iNamed "IH".
    wp_load.
    wp_pures. wp_if_destruct.
    + iModIntro.
      iApply "HΦ".
      iFrame.
    + wp_load. wp_load. wp_store. wp_load. wp_store.
      iModIntro.
      iApply "HΦ".
      iFrame.
  - iFrame.
  - iIntros "IH". iNamed "IH".
    wp_load.
    iModIntro.
    iApply "HΦ".
    (* oops, didn't prove anything about sum *)
Abort.

End goose.

(*| 
## Implementation

How the translator uses Go tooling. What Go exposes for type checking.

## What does a proof mean?

Translation is implicitly giving a semantics to Go. Correctness relies on this program being modeled "correctly": modeled behavior should be a subset of Go compiler behavior.

If translation does not work, sound (can't prove something wrong) but not a good developer experience. Failure modes: does not translate, does not compile in Coq, compiles but GooseLang code is always undefined.

---

::: info

From here onward is probably the next lecture

:::

Theme for today: ownership in Go

## Structs

How to model structs, then how to reason about them. Need for some "types".

Difference between _shallow_ and _deep_ embedding.

## Slices and map

Modeling length, capacity, and contiguous allocations. Ownership in slices, slice append.

Maps as non-atomic values.

## Fractional permissions

"Fictional separation" models read-only access.

|*)
