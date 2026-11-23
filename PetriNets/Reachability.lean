/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Basic

/-!
# Firing sequences and reachability

Provides finite firing sequences, weakest predecessor markings, and the
resulting reachability relation for weighted P/T nets, extending the one-step
firing semantics from `PetriNets.Basic`.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, especially "Sequential and Distributed Runs",
  pp. 35–49, and "Reachability in Elementary System Nets", pp. 141–145.
  DOI: 10.1007/978-3-642-33278-4.
* T. Murata, "Petri Nets: Properties, Analysis and Applications",
  *Proceedings of the IEEE* 77(4), 1989, Section IV-A, p. 547.
  DOI: 10.1109/5.24143.
-/

@[expose] public section

namespace PetriNet

/-! ## Firing sequences -/

/-- `net.FiresSequence src ts tgt` means that firing the transitions in `ts`
from left to right takes marking `src` to marking `tgt`.

A proof is built with `nil` for the empty sequence, or with `cons` from a
proof that the first transition fires and a proof that the remaining sequence
fires from the resulting intermediate marking. -/
inductive WeightedNet.FiresSequence {P T : Type*} (net : WeightedNet P T) :
    Marking P → List T → Marking P → Prop where
  /-- The empty sequence leaves a marking unchanged. -/
  | nil (m) : net.FiresSequence m [] m
  /-- A nonempty sequence fires its head transition to an intermediate
  marking `i`, then fires its tail from `i` to `tgt`. -/
  | cons {ts : List T} {src i tgt : Marking P} {t : T}
      (head : net.Fires src t i)
      (tail : net.FiresSequence i ts tgt) :
      net.FiresSequence src (t :: ts) tgt

/-- The marking obtained by applying the token updates of a transition list
from left to right.

Like `firingResult`, this is a total function: it computes a marking even if
some transition in the list is not enabled. A proof of `FiresSequence`
additionally establishes that every transition is enabled when it is applied.
-/
def WeightedNet.firingSequenceResult {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) (ts : List T) : Marking P :=
  ts.foldl net.firingResult src

@[simp]
theorem WeightedNet.firingSequenceResult_nil {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) :
    net.firingSequenceResult src [] = src :=
  rfl

@[simp]
theorem WeightedNet.firingSequenceResult_cons {P T : Type*}
    (net : WeightedNet P T) (src : Marking P) (t : T) (ts : List T) :
    net.firingSequenceResult src (t :: ts) =
      net.firingSequenceResult (net.firingResult src t) ts :=
  rfl

/-- The target of a valid firing sequence is exactly the marking computed by
`firingSequenceResult`. -/
theorem WeightedNet.FiresSequence.eq_firingSequenceResult {P T : Type*}
    {net : WeightedNet P T} {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) :
    tgt = net.firingSequenceResult src ts := by
  induction h with
  | nil => rfl
  | cons head _ ih =>
      rw [WeightedNet.firingSequenceResult_cons, ← head.eq_firingResult]
      exact ih

/-- Lift a standard firing to a singleton firing sequence. -/
theorem WeightedNet.FiresSequence.singleton {P T : Type*}
    {net : WeightedNet P T} {src tgt : Marking P} {t : T}
    (h : net.Fires src t tgt) : net.FiresSequence src [t] tgt := by
  exact WeightedNet.FiresSequence.cons h (WeightedNet.FiresSequence.nil tgt)

/-- Concatenate two firing sequences whose intermediate markings agree. -/
theorem WeightedNet.FiresSequence.append {P T : Type*}
    {net : WeightedNet P T} {src i tgt : Marking P} {ts₁ ts₂ : List T}
    (h₁ : net.FiresSequence src ts₁ i)
    (h₂ : net.FiresSequence i ts₂ tgt) :
    net.FiresSequence src (ts₁ ++ ts₂) tgt := by
  induction h₁ with
  | nil => exact h₂
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons head (ih h₂)

/-- A transition sequence has a unique target marking when fired from a
source marking. -/
theorem WeightedNet.FiresSequence.deterministic {P T : Type*}
    {net : WeightedNet P T} {src tgt₁ tgt₂ : Marking P} {ts : List T}
    (h₁ : net.FiresSequence src ts tgt₁)
    (h₂ : net.FiresSequence src ts tgt₂) : tgt₁ = tgt₂ := by
  exact h₁.eq_firingSequenceResult.trans h₂.eq_firingSequenceResult.symm

/-! ## Weakest predecessor markings -/

/-- The least marking from which firing `t` can cover `target`.

At each place, it contains the tokens consumed by `t`, plus the part of the
target demand not supplied by the post-incidence of `t`:

```text
weakestPreMarking(p) = pre(p,t) + (target(p) - post(p,t)).
```

This is the standard one-step predecessor construction used in backward
reachability arguments. -/
def WeightedNet.weakestPreMarking {P T : Type*} (net : WeightedNet P T)
    (t : T) (target : Marking P) : Marking P := fun p =>
  net.pre p t + (target p - net.post p t)

/-- Propagate a target demand backwards through a transition sequence.

The construction applies `weakestPreMarking` from right to left:

```text
weakestPreMarkingSequence []       target = target
weakestPreMarkingSequence (t::ts)  target =
  weakestPreMarking t (weakestPreMarkingSequence ts target).
```

It is the least initial demand obtained by successively propagating the final
demand backwards across every transition in the list. -/
def WeightedNet.weakestPreMarkingSequence {P T : Type*}
    (net : WeightedNet P T) : List T → Marking P → Marking P
  | [], target => target
  | t :: ts, target =>
      net.weakestPreMarking t (net.weakestPreMarkingSequence ts target)

/-- Propagating a demand backwards through concatenated transition lists is
the same as first propagating it through the suffix and then through the
prefix. -/
theorem WeightedNet.weakestPreMarkingSequence_append {P T : Type*}
    (net : WeightedNet P T) (ts₁ ts₂ : List T) (target : Marking P) :
    net.weakestPreMarkingSequence (ts₁ ++ ts₂) target =
      net.weakestPreMarkingSequence ts₁
        (net.weakestPreMarkingSequence ts₂ target) := by
  induction ts₁ with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.cons_append, WeightedNet.weakestPreMarkingSequence]
      rw [ih]

/-- Any marking above `weakestPreMarking` enables `t`, and its post-firing
marking covers `target`.

Thus `weakestPreMarking` is a threshold for one-step backward reachability,
not merely one particular source from which the target can be covered. -/
theorem WeightedNet.fires_firingResult_cover_of_weakestPreMarking_le
    {P T : Type*} (net : WeightedNet P T) (t : T) (target : Marking P)
    {src : Marking P} (hsrc : net.weakestPreMarking t target ≤ src) :
    net.Fires src t (net.firingResult src t) ∧
      target ≤ net.firingResult src t := by
  have henabled : net.Enabled src t := by
    intro p
    calc
      net.pre p t ≤ net.weakestPreMarking t target p := by
        simp [WeightedNet.weakestPreMarking]
      _ ≤ src p := hsrc p
  have hfires : net.Fires src t (net.firingResult src t) :=
    ⟨henabled, fun _ => rfl⟩
  have htarget : target ≤ net.firingResult src t := by
    intro p
    have hp := hsrc p
    simp [WeightedNet.weakestPreMarking] at hp ⊢
    omega
  exact ⟨hfires, htarget⟩

/-- Any marking above `weakestPreMarkingSequence ts target` can execute `ts`,
and its computed result covers `target`.

```text
weakestPreMarkingSequence ts target ≤ src

src ────────────ts─────────────▶ firingSequenceResult src ts
                                  ▲
                                  │ target ≤ result
```

The proof follows the list from left to right. The first application of
`fires_firingResult_cover_of_weakestPreMarking_le` reaches a marking covering
the `weakestPreMarkingSequence` of the tail; the induction hypothesis then
executes the tail and covers the original target. -/
theorem WeightedNet.firesSequence_cover_of_weakestPreMarkingSequence_le
    {P T : Type*} (net : WeightedNet P T) (ts : List T)
    (target : Marking P) {src : Marking P}
    (hsrc : net.weakestPreMarkingSequence ts target ≤ src) :
    net.FiresSequence src ts (net.firingSequenceResult src ts) ∧
      target ≤ net.firingSequenceResult src ts := by
  induction ts generalizing src with
  | nil =>
      exact ⟨WeightedNet.FiresSequence.nil src, hsrc⟩
  | cons t ts ih =>
      obtain ⟨hfirst, htailDemand⟩ :=
        net.fires_firingResult_cover_of_weakestPreMarking_le t
          (net.weakestPreMarkingSequence ts target) hsrc
      obtain ⟨htail, htarget⟩ := ih htailDemand
      exact ⟨WeightedNet.FiresSequence.cons hfirst htail, htarget⟩

/-! ## Reachability -/

/-- A marking `m'` is reachable from another marking `m` if there exists
a finite transition sequence that takes `m` to `m'`. -/
def WeightedNet.Reachable {P T : Type*} (net : WeightedNet P T)
    (m m' : Marking P) : Prop :=
  ∃ ts : List T, net.FiresSequence m ts m'

/-- Every marking is reachable from itself by the empty firing sequence. -/
@[refl]
theorem WeightedNet.Reachable.refl {P T : Type*} (net : WeightedNet P T)
    (m : Marking P) : net.Reachable m m := by
  exact ⟨[], WeightedNet.FiresSequence.nil m⟩

/-- Reachability is transitive: consecutive witnessing firing sequences can be
concatenated. -/
@[trans]
theorem WeightedNet.Reachable.trans {P T : Type*} {net : WeightedNet P T}
    {m₁ m₂ m₃ : Marking P} (h₁ : net.Reachable m₁ m₂)
    (h₂ : net.Reachable m₂ m₃) : net.Reachable m₁ m₃ := by
  rcases h₁ with ⟨ts₁, hts₁⟩
  rcases h₂ with ⟨ts₂, hts₂⟩
  exact ⟨ts₁ ++ ts₂, WeightedNet.FiresSequence.append hts₁ hts₂⟩

-- TODO: Provide `IsRefl` and `IsTrans` instances if generic relation APIs need them.

end PetriNet
