/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability
public import Cslib.Foundations.Semantics.LTS.Basic
import PetriNets.Repetition

/-!
# Coverability

Provides coverability for weighted P/T nets, including ω-markings,
ω-firing semantics, and concretisations.

A marking `m` is coverable from an initial marking `m₀` when some marking
reachable from `m₀` contains at least as many tokens as `m` at every place.
Unlike reachability, coverability does not require `m` itself to be reached.

An ω-marking represents arbitrarily large token counts at selected places.
Its coverability means that every finite marking below it is coverable.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} {net : WeightedNet P T}

/-! ## ω-markings and concretisations -/

/-- An ω-marking assigns either a natural-number token count or `ω` to each
place. The value `ω`, represented by `⊤` (top), denotes an arbitrarily large token
count. Mathlib's extended natural numbers `ℕ∞` are defined using `WithTop ℕ`.

The order and arithmetic come from `ℕ∞ = WithTop ℕ`. In particular, for every
finite `n : ℕ`, we have `n ≤ ω`, `ω + n = n + ω = ω`, and `ω - n = ω`.
Consequently, consuming or producing a finite number of tokens at a place
labelled `ω` leaves that place labelled `ω`. We do not need to give `ω - ω`
a weighted P/T net interpretation because arc weights are always finite. -/
abbrev OmegaMarking (P : Type*) := P → ℕ∞

namespace OmegaMarking

/-- Two distinct comparable ω-markings differ strictly at some place. -/
theorem exists_place_lt_of_le_of_ne {m m' : OmegaMarking P}
    (hle : m ≤ m') (hne : m ≠ m') :
    ∃ p, m p < m' p := by
  by_contra h
  push Not at h
  apply hne
  funext p
  exact le_antisymm (hle p) (h p)

end OmegaMarking

/-- Lift a concrete marking into an ω-markings. Every finite token count
is mapped to the corresponding value in `ℕ∞`; no place is mapped to
`ω`. -/
def Marking.toOmega (m : Marking P) : OmegaMarking P :=
  fun p => m p

@[simp]
theorem Marking.toOmega_apply (m : Marking P) (p : P) :
    m.toOmega p = m p :=
  rfl

/-- A concrete marking is canonically usable as an ω-marking.
We define a coercion from `Marking P` to `OmegaMarking P`, so that Lean
inserts `Marking.toOmega` whenever an `OmegaMarking` is expected in a
comparison. As a result, we can write, for example, `m ≤ mω`, with `m` a
concrete marking and `mω` an ω-marking, and Lean interprets it as
`m.toOmega ≤ mω`. -/
instance : Coe (Marking P) (OmegaMarking P) where
  coe := Marking.toOmega

/-- Concretise an ω-marking by replacing every `ω` component with a prescribed
reserve, while retaining the exact value of every finite component.

```text
concretise (3, ω, 5, ω) (r₀, r₁, r₂, r₃) = (3, r₁, 5, r₃)
```
-/
def OmegaMarking.concretise
    (m : OmegaMarking P) (reserve : Marking P) : Marking P :=
  fun p => if m p = ⊤ then reserve p else (m p).toNat

/-- A concretisation is below its ω-marking. -/
theorem OmegaMarking.concretise_toOmega_le
    (m : OmegaMarking P) (reserve : Marking P) :
    m.concretise reserve ≤ m := by
  intro p
  by_cases hp : m p = ⊤
  · simp [OmegaMarking.concretise, hp]
  · simp only [Marking.toOmega_apply, OmegaMarking.concretise, hp,
      ↓reduceIte]
    exact (ENat.natCast_toNat hp).le

/-- At an `ω` component, `concretise` uses the supplied reserve. -/
@[simp]
theorem OmegaMarking.concretise_apply_of_eq_top
    {m : OmegaMarking P} {reserve : Marking P} {p : P}
    (hp : m p = ⊤) :
    m.concretise reserve p = reserve p := by
  simp [OmegaMarking.concretise, hp]

/-- At a finite component, `concretise` retains its exact natural value. -/
theorem OmegaMarking.concretise_apply_of_ne_top
    {m : OmegaMarking P} {reserve : Marking P} {p : P}
    (hp : m p ≠ ⊤) :
    (m.concretise reserve p : ℕ∞) = m p := by
  simp only [OmegaMarking.concretise, hp, ↓reduceIte]
  exact ENat.natCast_toNat hp

/-! ## ω-firing semantics -/

/-- A transition is enabled at an ω-marking when every place contains at
least its finite pre-incidence weight. A place labelled `ω` satisfies every
finite pre-incidence requirement, so it never prevents a transition from
being enabled. -/
def WeightedNet.OmegaEnabled (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : Prop :=
  ∀ p, (net.pre p t : ℕ∞) ≤ m p

/-- Increasing an ω-marking preserves transition enabledness.
If `t` is enabled at `m` and `m ≤ m'`, then `t` is also enabled at `m'`. -/
theorem WeightedNet.OmegaEnabled.mono
    {m m' : OmegaMarking P} {t : T}
    (h : net.OmegaEnabled m t) (hleq : m ≤ m') :
    net.OmegaEnabled m' t := by
  intro p
  exact (h p).trans (hleq p)

/-- The ω-marking obtained by applying the token update of `t` to `m`.

As for `firingResult`, this function is defined whether or not `t` is
enabled; `OmegaFires` additionally requires enabledness. -/
def WeightedNet.omegaFiringResult (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : OmegaMarking P :=
  fun p => m p - net.pre p t + net.post p t

/-- `net.OmegaFires m t m'` means that `t` is enabled at the ω-marking `m`
and firing it produces `m'`. Subtraction and addition are those of `ℕ∞`, so a
component equal to `ω` remains equal to `ω`. -/
def WeightedNet.OmegaFires (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) (m' : OmegaMarking P) : Prop :=
  net.OmegaEnabled m t ∧
    ∀ p,
      m' p = m p - net.pre p t + net.post p t

/-- Adding the same ω-marking to the source and target preserves a firing. -/
theorem WeightedNet.OmegaFires.add
    {src tgt : OmegaMarking P} {t : T}
    (hfires : net.OmegaFires src t tgt) (d : OmegaMarking P) :
    net.OmegaFires (src + d) t (tgt + d) := by
  constructor
  · exact hfires.1.mono (by simp)
  · intro p
    change tgt p + d p =
      (src p + d p) - net.pre p t + net.post p t
    rw [hfires.2 p]
    rw [add_assoc, add_comm (net.post p t : ℕ∞) (d p), ← add_assoc]
    exact congrArg (· + (net.post p t : ℕ∞))
      ((ENat.addLECancellable_of_ne_top
        (ENat.natCast_ne_top (net.pre p t))).tsub_add_eq_add_tsub
          (hfires.1 p))

/-- Firing preserves every component already equal to `ω`. -/
theorem WeightedNet.OmegaFires.preserves_top
    {src tgt : OmegaMarking P} {t : T}
    (hfires : net.OmegaFires src t tgt) {p : P} (hp : src p = ⊤) :
    tgt p = ⊤ := by
  rw [hfires.2 p, hp]
  simp

/-- Suppose `src₁ ≤ src₂` and transition `t` fires from `src₁` to `tgt₁`.
Then `t` also fires from `src₂` to some `tgt₂`, and `tgt₁ ≤ tgt₂`. Thus,
starting with at least as many tokens at every place preserves the pointwise
order after firing the same transition. -/
theorem WeightedNet.OmegaFires.mono
    {src₁ src₂ tgt₁ : OmegaMarking P} {t : T}
    (h₁ : net.OmegaFires src₁ t tgt₁)
    (hleq : src₁ ≤ src₂) :
    ∃ tgt₂, net.OmegaFires src₂ t tgt₂ ∧ tgt₁ ≤ tgt₂ := by
  let tgt₂ : OmegaMarking P :=
    fun p => src₂ p - net.pre p t + net.post p t
  have h₂ : net.OmegaFires src₂ t tgt₂ :=
    ⟨h₁.1.mono hleq, fun _ => rfl⟩
  refine ⟨tgt₂, h₂, ?_⟩
  intro p
  rw [h₁.2 p, h₂.2 p]
  exact add_le_add (tsub_le_tsub_right (hleq p) _) le_rfl

/-- A transition is enabled at an ω-marking exactly when it can fire to some
ω-marking. -/
theorem WeightedNet.omegaEnabled_iff_exists_omegaFires
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.OmegaFires m t m' := by
  constructor
  · intro henabled
    use fun p => m p - net.pre p t + net.post p t
    exact ⟨henabled, fun _ => rfl⟩
  · rintro ⟨_, hfires⟩
    exact hfires.1

/-- Firing a transition from an ω-marking has a unique result. -/
theorem WeightedNet.omegaFires_is_deterministic
    {m m₁ m₂ : OmegaMarking P} {t : T}
    (h₁ : net.OmegaFires m t m₁) (h₂ : net.OmegaFires m t m₂) : m₁ = m₂ := by
  funext p
  exact (h₁.2 p).trans (h₂.2 p).symm

/-! ## ω-marking transition system -/

/-- The ω-marking semantics of `net` as a labelled transition
system. Its states are all ω-markings, its labels are the transitions of the
weighted P/T net, and its transition relation is ω-firing. -/
def WeightedNet.omegaMarkingLTS (net : WeightedNet P T) :
    Cslib.LTS (OmegaMarking P) T where
  Tr := net.OmegaFires

/-- An edge of the ω-marking LTS is exactly an ω-firing. -/
@[simp]
theorem WeightedNet.omegaMarkingLTS_tr_iff
    (net : WeightedNet P T) (src : OmegaMarking P) (t : T)
    (tgt : OmegaMarking P) :
    net.omegaMarkingLTS.Tr src t tgt ↔ net.OmegaFires src t tgt :=
  Iff.rfl

/-- A transition is enabled at an ω-marking exactly when the ω-marking LTS
has an outgoing edge carrying that transition. -/
theorem WeightedNet.omegaMarkingLTS_enabled_iff_exists_tr
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.omegaMarkingLTS.Tr m t m' :=
  net.omegaEnabled_iff_exists_omegaFires m t

/-- Apply a transition sequence successively to an ω-marking.

This is the deterministic ω-marking analogue of `firingSequenceResult`. It
computes a marking for every list; an `omegaMarkingLTS.MTr` proof separately
establishes that every transition was enabled. -/
def WeightedNet.omegaFiringSequenceResult
    (net : WeightedNet P T) : OmegaMarking P → List T → OmegaMarking P
  | m, [] => m
  | m, t :: ts =>
      net.omegaFiringSequenceResult (net.omegaFiringResult m t) ts

/-- The target of an executable ω-firing sequence is its computed
`omegaFiringSequenceResult`. -/
theorem WeightedNet.omegaMTr_eq_omegaFiringSequenceResult
    {src tgt : OmegaMarking P} {labels : List T}
    (hexec : net.omegaMarkingLTS.MTr src labels tgt) :
    tgt = net.omegaFiringSequenceResult src labels := by
  induction hexec with
  | refl => rfl
  | @stepL src t mid labels tgt hfirst _ ih =>
      have hmid : mid = net.omegaFiringResult src t := by
        funext p
        exact hfirst.2 p
      rw [WeightedNet.omegaFiringSequenceResult, ← hmid]
      exact ih

/-- An executable ω-firing sequence can be replayed from any larger source.
Its deterministic result covers the original target. -/
theorem WeightedNet.omegaMTr_mono
    {src tgt largerSrc : OmegaMarking P} {labels : List T}
    (hexec : net.omegaMarkingLTS.MTr src labels tgt)
    (hle : src ≤ largerSrc) :
    net.omegaMarkingLTS.MTr largerSrc labels
        (net.omegaFiringSequenceResult largerSrc labels) ∧
      tgt ≤ net.omegaFiringSequenceResult largerSrc labels := by
  induction hexec generalizing largerSrc with
  | refl => exact ⟨Cslib.LTS.MTr.refl, hle⟩
  | @stepL src t mid labels tgt hfirst _ ih =>
      obtain ⟨largerMid, hfirst', hmidLe⟩ := hfirst.mono hle
      obtain ⟨htail', htgtLe⟩ := ih hmidLe
      have hmid : largerMid = net.omegaFiringResult largerSrc t := by
        funext p
        exact hfirst'.2 p
      rw [WeightedNet.omegaFiringSequenceResult, ← hmid]
      exact ⟨Cslib.LTS.MTr.stepL hfirst' htail', htgtLe⟩

/-- Adding the same ω-marking to both endpoints preserves an executable
ω-firing sequence. -/
theorem WeightedNet.omegaMTr_add
    {src tgt : OmegaMarking P} {labels : List T}
    (hexec : net.omegaMarkingLTS.MTr src labels tgt)
    (d : OmegaMarking P) :
    net.omegaMarkingLTS.MTr (src + d) labels (tgt + d) := by
  induction hexec with
  | refl => exact Cslib.LTS.MTr.refl
  | stepL hfirst _ ih =>
      exact Cslib.LTS.MTr.stepL (hfirst.add d) ih

/-- A non-decreasing ω-firing sequence stays non-decreasing when replayed
from a larger source. The same extra tokens are added to both endpoints. -/
theorem WeightedNet.omegaMTr_replay_nondecreasing
    {src tgt largerSrc : OmegaMarking P} {labels : List T}
    (hexec : net.omegaMarkingLTS.MTr src labels tgt)
    (hgrowth : src ≤ tgt) (hle : src ≤ largerSrc) :
    ∃ largerTgt, net.omegaMarkingLTS.MTr largerSrc labels largerTgt ∧
      largerSrc ≤ largerTgt := by
  let d := largerSrc - src
  have hsrc : src + d = largerSrc := by
    funext p
    exact add_tsub_cancel_of_le (hle p)
  refine ⟨tgt + d, hsrc ▸ net.omegaMTr_add hexec d, ?_⟩
  rw [← hsrc]
  exact add_le_add_left hgrowth d

/-! ## Weakest ω-predecessors -/

/-- The weakest ω-marking from which firing `t` can cover `target`.

It is the ω-marking analogue of `weakestPreMarking`: at every place it
contains the finite pre-incidence weight, together with the part of the target
demand not supplied by the post-incidence weight. -/
def WeightedNet.weakestPreOmegaMarking
    (net : WeightedNet P T) (t : T) (target : OmegaMarking P) :
    OmegaMarking P := fun p =>
  net.pre p t + (target p - net.post p t)

/-- Propagate an ω-marking target backwards through a transition sequence.
The transitions are processed from right to left, as for
`weakestPreMarkingSequence`. -/
def WeightedNet.weakestPreOmegaMarkingSequence
    (net : WeightedNet P T) : List T → OmegaMarking P → OmegaMarking P
  | [], target => target
  | t :: ts, target =>
      net.weakestPreOmegaMarking t
        (net.weakestPreOmegaMarkingSequence ts target)

/-- Weakest ω-predecessors distribute over concatenation: first propagate
the target through the suffix, then through the prefix. -/
theorem WeightedNet.weakestPreOmegaMarkingSequence_append
    (net : WeightedNet P T) (ts₁ ts₂ : List T)
    (target : OmegaMarking P) :
    net.weakestPreOmegaMarkingSequence (ts₁ ++ ts₂) target =
      net.weakestPreOmegaMarkingSequence ts₁
        (net.weakestPreOmegaMarkingSequence ts₂ target) := by
  induction ts₁ with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.cons_append,
        WeightedNet.weakestPreOmegaMarkingSequence]
      rw [ih]

/-- Any ω-marking above `weakestPreOmegaMarking t target` enables `t`.
Firing `t` from it produces an ω-marking covering `target`. -/
theorem WeightedNet.exists_omegaFires_cover_of_weakestPreOmegaMarking_le
    (net : WeightedNet P T) (t : T)
    (target : OmegaMarking P) {src : OmegaMarking P}
    (hsrc : net.weakestPreOmegaMarking t target ≤ src) :
    ∃ tgt, net.OmegaFires src t tgt ∧ target ≤ tgt := by
  let tgt : OmegaMarking P :=
    fun p => src p - net.pre p t + net.post p t
  have henabled : net.OmegaEnabled src t := by
    intro p
    calc
      (net.pre p t : ℕ∞) ≤ net.weakestPreOmegaMarking t target p := by
        simp [WeightedNet.weakestPreOmegaMarking]
      _ ≤ src p := hsrc p
  have hfires : net.OmegaFires src t tgt :=
    ⟨henabled, fun _ => rfl⟩
  refine ⟨tgt, hfires, ?_⟩
  intro p
  have hremaining : target p - net.post p t ≤
      src p - net.pre p t :=
    ENat.le_sub_of_add_le_left (by simp) (hsrc p)
  calc
    target p ≤ target p - net.post p t + net.post p t := le_tsub_add
    _ ≤ src p - net.pre p t + net.post p t :=
      add_le_add hremaining le_rfl
    _ = tgt p := rfl

/-- The ω-valued and concrete weakest predecessor constructions agree on
concrete target markings. -/
theorem WeightedNet.weakestPreOmegaMarking_coe
    (net : WeightedNet P T) (t : T) (target : Marking P) :
    net.weakestPreOmegaMarking t target = net.weakestPreMarking t target := by
  funext p
  simp [WeightedNet.weakestPreOmegaMarking, WeightedNet.weakestPreMarking]

/-- The ω-valued and concrete weakest predecessor sequence constructions
agree on concrete target markings. -/
theorem WeightedNet.weakestPreOmegaMarkingSequence_coe
    (net : WeightedNet P T) (ts : List T) (target : Marking P) :
    net.weakestPreOmegaMarkingSequence ts target =
      net.weakestPreMarkingSequence ts target := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [WeightedNet.weakestPreOmegaMarkingSequence,
        WeightedNet.weakestPreMarkingSequence]
      rw [ih, net.weakestPreOmegaMarking_coe]

/-- Propagate an ω-marking target backwards across an ω-firing.

If `t` fires from `src` to `tgt` and `target ≤ tgt`, then the weakest
ω-marking sufficient to cover `target` lies below `src`. -/
theorem WeightedNet.weakestPreOmegaMarking_le_of_omegaFires
    {src tgt target : OmegaMarking P} {t : T}
    (hfires : net.OmegaFires src t tgt) (htarget : target ≤ tgt) :
    net.weakestPreOmegaMarking t target ≤ src := by
  intro p
  have hremaining : target p - net.post p t ≤
      src p - net.pre p t := by
    calc
      target p - net.post p t ≤ tgt p - net.post p t :=
        tsub_le_tsub_right (htarget p) _
      _ = (src p - net.pre p t + net.post p t) - net.post p t := by
        rw [hfires.2 p]
      _ ≤ src p - net.pre p t := add_tsub_le_right
  change (net.pre p t : ℕ∞) + (target p - net.post p t) ≤ src p
  calc
    (net.pre p t : ℕ∞) + (target p - net.post p t) ≤
        net.pre p t + (src p - net.pre p t) :=
      add_le_add le_rfl hremaining
    _ = src p := add_tsub_cancel_of_le (hfires.1 p)

/-- Any ω-marking above the weakest predecessor of a transition sequence can
execute that sequence, and the resulting ω-marking covers `target`.

```text
weakestPreOmegaMarkingSequence ts target ≤ src

src ────────────ts─────────────▶ tgt
                                  ▲
                                  │ target ≤ tgt
```
-/
theorem WeightedNet.exists_omegaMTr_cover_of_weakestPreOmegaMarkingSequence_le
    (net : WeightedNet P T) (ts : List T)
    (target : OmegaMarking P) {src : OmegaMarking P}
    (hsrc : net.weakestPreOmegaMarkingSequence ts target ≤ src) :
    ∃ tgt, net.omegaMarkingLTS.MTr src ts tgt ∧ target ≤ tgt := by
  induction ts generalizing src with
  | nil =>
      exact ⟨src, Cslib.LTS.MTr.refl, hsrc⟩
  | cons t ts ih =>
      obtain ⟨next, hfirst, htailDemand⟩ :=
        net.exists_omegaFires_cover_of_weakestPreOmegaMarking_le t
          (net.weakestPreOmegaMarkingSequence ts target) hsrc
      obtain ⟨tgt, htail, htarget⟩ := ih htailDemand
      exact ⟨tgt, Cslib.LTS.MTr.stepL hfirst htail, htarget⟩

/-! ## Relation with concrete firing semantics -/

/-- Lifting a concrete marking into an ω-marking preserves and reflects
enabledness. -/
theorem WeightedNet.enabled_iff_omegaEnabled_toOmega
    (net : WeightedNet P T) (m : Marking P) (t : T) :
    net.Enabled m t ↔ net.OmegaEnabled m t := by
  simp [WeightedNet.Enabled, WeightedNet.OmegaEnabled, Marking.toOmega]

/-- Lifting concrete source and target markings into the ω-markings
preserves and reflects firing. -/
theorem WeightedNet.fires_iff_omegaFires_toOmega
    (net : WeightedNet P T) (m m' : Marking P) (t : T) :
    net.Fires m t m' ↔ net.OmegaFires m t m' := by
  constructor
  · rintro ⟨henabled, hfires⟩
    constructor
    · apply (net.enabled_iff_omegaEnabled_toOmega m t).mp
      exact henabled
    · intro p
      simp
      rw [hfires p, WeightedNet.firingResult_apply]
      rw [ENat.natCast_add, ENat.natCast_sub]
  · rintro ⟨henabled, hfires⟩
    constructor
    · exact (net.enabled_iff_omegaEnabled_toOmega m t).mpr henabled
    · intro p
      have hp := hfires p
      simp at hp
      change m' p = m p - net.pre p t + net.post p t
      exact_mod_cast hp

/-! ## Concrete predecessors of ω-firing -/

/-- Propagate a concrete target demand backwards across an ω-firing.

Assume that `t` fires from `omegaSrc` to `omegaTgt`, and that the concrete
marking `target` lies below `omegaTgt`. Then the least concrete marking
sufficient to cover `target` after firing `t` lies below `omegaSrc`:

```text
          omegaSrc ─────────────t──────────────▶ omegaTgt
              ▲                                      ▲
              ≤                                      ≤
              │                                      │
weakestPreMarking t target ──t──▶ a marking covering target
```

At a place where `omegaSrc` is `ω`, this is immediate because the
predecessor demand is concrete. At a finite place, it follows from the
ω-firing equation and `target ≤ omegaTgt`.

This theorem is the backward step used to turn a concrete demand below an
ω-successor into a concrete demand below its source. -/
theorem WeightedNet.weakestPreMarking_le_of_omegaFires
    {omegaSrc omegaTgt : OmegaMarking P} {t : T} {target : Marking P}
    (hfires : net.OmegaFires omegaSrc t omegaTgt)
    (htarget : target ≤ omegaTgt) :
    net.weakestPreMarking t target ≤ omegaSrc := by
  rw [← net.weakestPreOmegaMarking_coe t target]
  exact net.weakestPreOmegaMarking_le_of_omegaFires hfires htarget

/-- Propagating a concrete demand backwards along an ω-execution gives
a concrete predecessor below the abstract source. -/
private theorem WeightedNet.weakestPreMarkingSequence_le_of_omegaMTr
    {src tgt : OmegaMarking P} {ts : List T} {demand : Marking P}
    (hexec : net.omegaMarkingLTS.MTr src ts tgt) (hdemand : demand ≤ tgt) :
    net.weakestPreMarkingSequence ts demand ≤ src := by
  induction hexec with
  | refl => exact hdemand
  | stepL hfirst _ ih =>
      exact net.weakestPreMarking_le_of_omegaFires hfirst (ih hdemand)

/-- Realise a concrete demand below an ω-firing target by an ordinary firing.

Given `omegaSrc ─t→ omegaTgt` and a concrete `demand` represented below
`omegaTgt`, the theorem constructs a concrete source below `omegaSrc`. Firing
`t` from that source produces its deterministic firing result, which covers
`demand`:

```text
           omegaSrc ─────────t─────────▶ omegaTgt
               ▲                           ▲
            toOmega ≤                   toOmega ≤
               │                           │
          finiteSrc ──t──▶ firingResult   demand
```
-/
theorem WeightedNet.exists_finite_firing_cover_of_omegaFires
    {omegaSrc omegaTgt : OmegaMarking P} {t : T} {demand : Marking P}
    (hfires : net.OmegaFires omegaSrc t omegaTgt)
    (hdemand : demand ≤ omegaTgt) :
    ∃ finiteSrc : Marking P,
      finiteSrc ≤ omegaSrc ∧
      net.Fires finiteSrc t (net.firingResult finiteSrc t) ∧
      demand ≤ net.firingResult finiteSrc t := by
  let finiteSrc := net.weakestPreMarking t demand
  have hsrcBelow : finiteSrc ≤ omegaSrc :=
    net.weakestPreMarking_le_of_omegaFires hfires hdemand
  obtain ⟨hfiniteFires, hdemandBelow⟩ :=
    net.fires_firingResult_cover_of_weakestPreMarking_le t demand le_rfl
  exact ⟨finiteSrc, hsrcBelow, hfiniteFires, hdemandBelow⟩

/-! ## Concrete replay of ω-firing sequences -/

/-- Every concrete marking `c` below an ω-marking `m` is covered by a concretisation
using one uniform bound for all ω-places. -/
private theorem OmegaMarking.exists_uniform_concretise_ge [Fintype P]
    {m : OmegaMarking P} {c : Marking P} (hle : c ≤ m) :
    ∃ L : ℕ, c ≤ m.concretise (fun _ => L) := by
  /- We choose a uniform bound `L` as the largest value in `c`. -/
  let L := Finset.univ.sup c
  let uniformcConcrete := m.concretise (fun _ => L)
  refine ⟨L, ?_⟩
  intro q
  by_cases hq : m q = ⊤
  · have hmax : c q ≤ L := Finset.le_sup (Finset.mem_univ q)
    simpa [uniformcConcrete, hq] using hmax
  · have hvalue : (uniformcConcrete q : ℕ∞) = m q :=
      m.concretise_apply_of_ne_top hq
    have hqle := hle q
    rw [← hvalue] at hqle
    simpa using hqle

/-- Replay an ω-execution concretely using enough tokens at the
source's ω-places to cover the target demand. -/
private theorem WeightedNet.exists_concrete_replay
    [Fintype P]
    {src tgt : OmegaMarking P} {ts : List T}
    (hexec : net.omegaMarkingLTS.MTr src ts tgt)
    (K : ℕ) :
    ∃ (L : ℕ) (reached : Marking P),
      net.FiresSequence (src.concretise (fun _ => L)) ts reached ∧
      tgt.concretise (fun _ => K) ≤ reached := by
  let demand := tgt.concretise (fun _ => K)
  let pre := net.weakestPreMarkingSequence ts demand
  have hpre : pre ≤ src :=
    net.weakestPreMarkingSequence_le_of_omegaMTr hexec
      (tgt.concretise_toOmega_le _)
  obtain ⟨L, hbudget⟩ := OmegaMarking.exists_uniform_concretise_ge hpre
  obtain ⟨hfire, hcover⟩ := net.firesSequence_cover_of_weakestPreMarkingSequence_le
    ts demand hbudget
  exact ⟨L, _, hfire, hcover⟩

/-- An ordinary ω-execution preserves finiteness at each finite place. -/
private theorem WeightedNet.omegaMTr_preserves_finite
    {src tgt : OmegaMarking P} {ts : List T} {p : P}
    (hexec : net.omegaMarkingLTS.MTr src ts tgt)
    (hsrc : src p ≠ ⊤) : tgt p ≠ ⊤ := by
  induction hexec with
  | refl => exact hsrc
  | stepL hfirst _ ih =>
      apply ih
      rw [hfirst.2 p]
      simp [hsrc, ENat.add_eq_top]

/-- A concrete replay covering the target demand gains at least one token
at a place that strictly grows in the ω-execution. -/
private theorem WeightedNet.exists_concrete_replay_growsAt
    [Fintype P]
    {src tgt : OmegaMarking P} {ts : List T} {p : P}
    (hexec : net.omegaMarkingLTS.MTr src ts tgt)
    (hgrowth : src p < tgt p) (K : ℕ) :
    ∃ (L : ℕ) (reached : Marking P),
      net.FiresSequence (src.concretise (fun _ => L)) ts reached ∧
      tgt.concretise (fun _ => K) ≤ reached ∧
      src.concretise (fun _ => L) p + 1 ≤ reached p := by
  obtain ⟨L, reached, hfire, hcover⟩ := net.exists_concrete_replay hexec K
  have hsrc : src p ≠ ⊤ := ne_top_of_lt hgrowth
  have htgt := net.omegaMTr_preserves_finite hexec hsrc
  have hlt : src.concretise (fun _ => L) p < tgt.concretise (fun _ => K) p := by
    apply ENat.natCast_lt_natCast.mp
    change _ < (tgt.concretise (fun _ => K) p : ℕ∞)
    rw [src.concretise_apply_of_ne_top hsrc,
      tgt.concretise_apply_of_ne_top htgt]
    exact hgrowth
  exact ⟨L, reached, hfire, hcover, hlt.trans_le (hcover p)⟩

/-- A repetition budget fits below an ω-marking when the concrete source
already fits below it and the replay loses no tokens at its finite places. -/
private theorem OmegaMarking.repeat_budget_le
    {m : OmegaMarking P} {base reached : Marking P}
    (hbase : base ≤ m)
    (hfinite : ∀ q, m q ≠ ⊤ → base q ≤ reached q) (n : ℕ) :
    base + n • (base - reached) ≤ m := by
  intro q
  by_cases hq : m q = ⊤
  · simp [hq]
  · change ((base q + n * (base q - reached q) : ℕ) : ℕ∞) ≤ m q
    rw [Nat.sub_eq_zero_of_le (hfinite q hq), Nat.mul_zero, Nat.add_zero]
    exact hbase q

/-- Repeat a concrete replay exactly `n` times. The concrete source stays
below the abstract source, and the repetition gains at least `n` tokens
at the strictly growing place. A nonempty repetition also covers the
target concretisation with budget `K`. -/
theorem WeightedNet.exists_concrete_replay_repeated_growsAt
    [Fintype P]
    {src tgt : OmegaMarking P} {ts : List T} {p : P}
    (hexec : net.omegaMarkingLTS.MTr src ts tgt)
    (hle : src ≤ tgt) (hgrowth : src p < tgt p) (n K : ℕ) :
    ∃ base reached : Marking P,
      base ≤ src ∧
      net.FiresSequence base (List.replicate n ts).flatten reached ∧
      base p + n ≤ reached p ∧
      (0 < n → tgt.concretise (fun _ => K) ≤ reached) := by
  cases n with
  | zero =>
      exact ⟨src.concretise 0, src.concretise 0, src.concretise_toOmega_le 0,
        WeightedNet.FiresSequence.nil _, le_rfl, fun h => (Nat.lt_irrefl 0 h).elim⟩
  | succ n =>
      obtain ⟨L, reached, hfire, hcover, hp⟩ :=
        net.exists_concrete_replay_growsAt hexec hgrowth K
      let base := src.concretise (fun _ => L)
      let start := base + n • (base - reached)
      refine ⟨start, _, ?_, hfire.repeat_with_budget n, ?_, ?_⟩
      · apply OmegaMarking.repeat_budget_le (src.concretise_toOmega_le _) _ n
        intro q hq
        have htq := net.omegaMTr_preserves_finite hexec hq
        apply (ENat.natCast_le_natCast.mp ?_).trans (hcover q)
        rw [src.concretise_apply_of_ne_top hq, tgt.concretise_apply_of_ne_top htq]
        exact hle q
      · exact Marking.repeat_with_budget_gain_at hp n
      · intro _
        exact hcover.trans (by simp)

/-! ## Coverability -/

/-- A marking `m` is coverable from `m₀` when there is a marking `m'`
reachable from `m₀` such that `m ≤ m'`. The order on markings is pointwise:
`m ≤ m'` means that `m p ≤ m' p` for every place `p`. -/
def WeightedNet.CoverableFrom (net : WeightedNet P T)
    (m₀ m : Marking P) : Prop :=
  ∃ m', net.Reachable m₀ m' ∧ m ≤ m'

/-- If the weakest predecessor of `target` through `t` is coverable, then
`target` is coverable. A reachable marking covering the predecessor enables
`t`, and its firing result covers `target`. -/
theorem WeightedNet.coverableFrom_of_weakestPreMarking
    {m₀ target : Marking P} {t : T}
    (hpre : net.CoverableFrom m₀ (net.weakestPreMarking t target)) :
    net.CoverableFrom m₀ target := by
  obtain ⟨src, hreachable, hle⟩ := hpre
  obtain ⟨hfires, htarget⟩ :=
    net.fires_firingResult_cover_of_weakestPreMarking_le t target hle
  exact ⟨net.firingResult src t,
    hreachable.trans ⟨[t], WeightedNet.FiresSequence.singleton hfires⟩,
    htarget⟩

/-- If the weakest predecessor of `target` through a transition sequence is
coverable, then `target` is coverable.

A reachable marking covering the weakest predecessor can execute the complete
sequence and reaches a marking covering `target` (monotonicity of the firing sequence):

```text
                         labels
 m₀ ──Reachable──▶ reached ─────────▶ result
                      ▲                 ▲
                      │ ≤               │ ≤
                      │                 │
        weakestPreMarkingSequence     target
```

The reachable marking covering the weakest predecessor can execute `labels`;
the resulting marking then covers `target`. -/
theorem WeightedNet.coverableFrom_of_weakestPreMarkingSequence
    {m₀ target : Marking P} {labels : List T}
    (hpre : net.CoverableFrom m₀
      (net.weakestPreMarkingSequence labels target)) :
    net.CoverableFrom m₀ target := by
  obtain ⟨src, hreachable, hle⟩ := hpre
  obtain ⟨hseq, htarget⟩ :=
    net.firesSequence_cover_of_weakestPreMarkingSequence_le
      labels target hle
  exact ⟨net.firingSequenceResult src labels,
    hreachable.trans ⟨labels, hseq⟩, htarget⟩

/-- An ω-marking `mω` is ω-coverable from `m₀` when every concrete
marking below `mω` is coverable from `m₀`.

Equivalently, the downward closure of `mω` among concrete markings is
contained in the downward closure of the reachable markings from `m₀`:

```text
∀ m, m ≤ mω → ∃ m', Reachable m₀ m' ∧ m ≤ m'.
```
-/
def WeightedNet.OmegaCoverableFrom (net : WeightedNet P T)
    (m₀ : Marking P) (mω : OmegaMarking P) : Prop :=
  ∀ m : Marking P, m ≤ mω → net.CoverableFrom m₀ m

/-- Obtain a reachable cover for a chosen concretisation of an
ω-coverable marking.

The marking `mω.concretise reserve` retains the exact finite components of
`mω` and uses `reserve p` wherever `mω p = ω`. Since this concrete marking
is below `mω`, the definition of `OmegaCoverableFrom` supplies a reachable
marking `reached` which covers it:

```text
                mω
                 ▲
                 │ ≤
 mω.concretise reserve
                 │ ≤
                 ▼
              reached
                 ▲
                 │ Reachable
                 │
                m₀
```

Equivalently, the resulting reachable marking satisfies:

* if `mω p = (n : ℕ∞)` for some `n : ℕ`, then `n ≤ reached p`; and
* if `mω p = ω`, then `reserve p ≤ reached p`.

Thus callers may choose arbitrarily large, independently specified finite
reserves at the ω-places. The reachable witness may depend on the chosen
reserve; the theorem does not claim that one concrete marking realises all
possible reserves simultaneously. -/
theorem WeightedNet.OmegaCoverableFrom.coverable_concretise
    {m₀ : Marking P} {mω : OmegaMarking P}
    (h : net.OmegaCoverableFrom m₀ mω) (reserve : Marking P) :
    net.CoverableFrom m₀ (mω.concretise reserve) := by
  exact h (mω.concretise reserve) (mω.concretise_toOmega_le reserve)

/-- An ω-marking `mω` is `K`-coverable from `m₀` when its concretisation with
`K` tokens at every `ω`-place is coverable from `m₀`. Its finite components
retain their exact values. -/
def WeightedNet.KCoverableFrom (net : WeightedNet P T)
    (m₀ : Marking P) (mω : OmegaMarking P) (K : ℕ) : Prop :=
  net.CoverableFrom m₀ (mω.concretise fun _ => K)

/-- For finitely many places, ω-coverability is equivalent to `K`-coverability
for every `K`.

Thus it suffices to show that, for every `K`, one reachable marking covers the
finite components of `mω` and has at least `K` tokens at every `ω`-place. -/
theorem WeightedNet.omegaCoverableFrom_iff_forall_kCoverableFrom
    [Fintype P]
    {m₀ : Marking P} {mω : OmegaMarking P} :
    net.OmegaCoverableFrom m₀ mω ↔
      ∀ K, net.KCoverableFrom m₀ mω K := by
  classical
  constructor
  · intro hsound K
    exact hsound.coverable_concretise (fun _ => K)
  · intro hrealise demand hdemand
    let K := ∑ p, demand p
    obtain ⟨reached, hreachable, hcover⟩ := hrealise K
    refine ⟨reached, hreachable, fun p => ?_⟩
    apply (show demand p ≤ mω.concretise (fun _ => K) p by
      by_cases hp : mω p = ⊤
      · simp only [OmegaMarking.concretise, hp, ↓reduceIte]
        exact Finset.single_le_sum
          (fun q _ => Nat.zero_le (demand q)) (Finset.mem_univ p)
      · simp only [OmegaMarking.concretise, hp, ↓reduceIte]
        apply ENat.natCast_le_natCast.mp
        rw [ENat.natCast_toNat hp]
        exact hdemand p).trans
    exact hcover p

/-- The initial marking embedded as an ω-marking is ω-coverable from
itself. Every concrete marking below `m₀` is covered by the reachable
marking `m₀`. -/
theorem WeightedNet.omegaCoverableFrom_initial
    (net : WeightedNet P T) (m₀ : Marking P) :
    net.OmegaCoverableFrom m₀ m₀ := by
  intro m hle
  refine ⟨m₀, WeightedNet.Reachable.refl net m₀, ?_⟩
  intro p
  exact ENat.natCast_le_natCast.mp (hle p)

/- Transport a concrete firing cover through soundness of its abstract source.

```text
concreteSrc ──t──▶ concreteTgt
    │                 │
    ≤                 ≤
    │                 │
reachableSrc ──t──▶ reachableTgt

demand ≤ concreteTgt
```

Source soundness supplies `reachableSrc`; firing monotonicity supplies
`reachableTgt`, which covers `demand`. -/
private theorem coverableFrom_of_concrete_firing_cover
    {m₀ concreteSrc concreteTgt demand : Marking P}
    {src : OmegaMarking P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ src)
    (hsrcBelow : concreteSrc ≤ src)
    (hfires : net.Fires concreteSrc t concreteTgt)
    (hdemandBelow : demand ≤ concreteTgt) :
    net.CoverableFrom m₀ demand := by
  obtain ⟨reachableSrc, hreachableSrc, hconcreteSrcBelow⟩ :=
    hsound concreteSrc hsrcBelow
  have hconcreteReachable : net.Reachable concreteSrc concreteTgt :=
    ⟨[t], WeightedNet.FiresSequence.singleton hfires⟩
  obtain ⟨reachableTgt, hreachableTgt, hconcreteTgtBelow⟩ :=
    hconcreteReachable.mono hconcreteSrcBelow
  exact ⟨reachableTgt, hreachableSrc.trans hreachableTgt,
    hdemandBelow.trans hconcreteTgtBelow⟩

/-- ω-coverability is preserved by an ω-firing.

For every concrete demand below `omegaTgt`, the firing determines a sufficient
concrete demand below `omegaSrc`. Source ω-coverability supplies a reachable
marking covering that demand, and firing monotonicity produces a reachable
marking covering the original target demand.

```text
              OmegaFires t
 omegaSrc ─────────────────▶ omegaTgt
    │                            │
  sound                        sound
```
-/
theorem WeightedNet.omegaCoverableFrom_of_omegaFires
    {m₀ : Marking P} {omegaSrc omegaTgt : OmegaMarking P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ omegaSrc)
    (hfires : net.OmegaFires omegaSrc t omegaTgt) :
    net.OmegaCoverableFrom m₀ omegaTgt := by
  intro demand hdemand
  obtain ⟨concreteSrc, hsrcBelow, hconcreteFires, hdemandBelow⟩ :=
    net.exists_finite_firing_cover_of_omegaFires hfires hdemand
  exact coverableFrom_of_concrete_firing_cover
    hsound hsrcBelow hconcreteFires hdemandBelow

end PetriNet
