/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability
public import Cslib.Foundations.Semantics.LTS.Basic
import PetriNets.Monotonicity

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
theorem exists_place_lt_of_le_of_ne {P : Type*} {m m' : OmegaMarking P}
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
def Marking.toOmega {P : Type*} (m : Marking P) : OmegaMarking P :=
  fun p => m p

@[simp]
theorem Marking.toOmega_apply {P : Type*} (m : Marking P) (p : P) :
    m.toOmega p = m p :=
  rfl

/-- A concrete marking is canonically usable as an ω-marking.
We define a coercion from `Marking P` to `OmegaMarking P`, so that Lean
inserts `Marking.toOmega` whenever an `OmegaMarking` is expected in a
comparison. As a result, we can write, for example, `m ≤ mω`, with `m` a
concrete marking and `mω` an ω-marking, and Lean interprets it as
`m.toOmega ≤ mω`. -/
instance {P : Type*} : Coe (Marking P) (OmegaMarking P) where
  coe := Marking.toOmega

/-- Concretise an ω-marking by replacing every `ω` component with a prescribed
reserve, while retaining the exact value of every finite component.

```text
concretise (3, ω, 5, ω) (r₀, r₁, r₂, r₃) = (3, r₁, 5, r₃)
```
-/
def OmegaMarking.concretise {P : Type*}
    (m : OmegaMarking P) (reserve : Marking P) : Marking P :=
  fun p => if m p = ⊤ then reserve p else (m p).toNat

/-- A concretisation is below its ω-marking. -/
theorem OmegaMarking.concretise_toOmega_le {P : Type*}
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
theorem OmegaMarking.concretise_apply_of_eq_top {P : Type*}
    {m : OmegaMarking P} {reserve : Marking P} {p : P}
    (hp : m p = ⊤) :
    m.concretise reserve p = reserve p := by
  simp [OmegaMarking.concretise, hp]

/-- At a finite component, `concretise` retains its exact natural value. -/
theorem OmegaMarking.concretise_apply_of_ne_top {P : Type*}
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
def WeightedNet.OmegaEnabled {P T : Type*} (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : Prop :=
  ∀ p, (net.pre p t : ℕ∞) ≤ m p

/-- Increasing an ω-marking preserves transition enabledness.
If `t` is enabled at `m` and `m ≤ m'`, then `t` is also enabled at `m'`. -/
theorem WeightedNet.OmegaEnabled.mono {P T : Type*}
    {net : WeightedNet P T} {m m' : OmegaMarking P} {t : T}
    (h : net.OmegaEnabled m t) (hleq : m ≤ m') :
    net.OmegaEnabled m' t := by
  intro p
  exact (h p).trans (hleq p)

/-- `net.OmegaFires m t m'` means that `t` is enabled at the ω-marking `m`
and firing it produces `m'`. Subtraction and addition are those of `ℕ∞`, so a
component equal to `ω` remains equal to `ω`. -/
def WeightedNet.OmegaFires {P T : Type*} (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) (m' : OmegaMarking P) : Prop :=
  net.OmegaEnabled m t ∧
    ∀ p,
      m' p = m p - net.pre p t + net.post p t

/-- The weakest ω-marking from which firing `t` can cover `target`.

It is the ω-marking analogue of `weakestPreMarking`: at every place it
contains the finite pre-incidence weight, together with the part of the target
demand not supplied by the post-incidence weight. -/
def WeightedNet.weakestPreOmegaMarking {P T : Type*}
    (net : WeightedNet P T) (t : T) (target : OmegaMarking P) :
    OmegaMarking P := fun p =>
  net.pre p t + (target p - net.post p t)

/-- Propagate an ω-marking target backwards through a transition sequence.
The transitions are processed from right to left, as for
`weakestPreMarkingSequence`. -/
def WeightedNet.weakestPreOmegaMarkingSequence {P T : Type*}
    (net : WeightedNet P T) : List T → OmegaMarking P → OmegaMarking P
  | [], target => target
  | t :: ts, target =>
      net.weakestPreOmegaMarking t
        (net.weakestPreOmegaMarkingSequence ts target)

/-- Weakest ω-predecessors distribute over concatenation: first propagate
the target through the suffix, then through the prefix. -/
theorem WeightedNet.weakestPreOmegaMarkingSequence_append {P T : Type*}
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

/-- Firing preserves every component already equal to `ω`. -/
theorem WeightedNet.OmegaFires.preserves_top {P T : Type*}
    {net : WeightedNet P T} {src tgt : OmegaMarking P} {t : T}
    (hfires : net.OmegaFires src t tgt) {p : P} (hp : src p = ⊤) :
    tgt p = ⊤ := by
  rw [hfires.2 p, hp]
  simp

/-- Suppose `src₁ ≤ src₂` and transition `t` fires from `src₁` to `tgt₁`.
Then `t` also fires from `src₂` to some `tgt₂`, and `tgt₁ ≤ tgt₂`. Thus,
starting with at least as many tokens at every place preserves the pointwise
order after firing the same transition. -/
theorem WeightedNet.OmegaFires.mono {P T : Type*}
    {net : WeightedNet P T} {src₁ src₂ tgt₁ : OmegaMarking P} {t : T}
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
theorem WeightedNet.omegaEnabled_iff_exists_omegaFires {P T : Type*}
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.OmegaFires m t m' := by
  constructor
  · intro henabled
    use fun p => m p - net.pre p t + net.post p t
    exact ⟨henabled, fun _ => rfl⟩
  · rintro ⟨_, hfires⟩
    exact hfires.1

/-- Firing a transition from an ω-marking has a unique result. -/
theorem WeightedNet.omegaFires_is_deterministic {P T : Type*}
    {net : WeightedNet P T} {m m₁ m₂ : OmegaMarking P} {t : T}
    (h₁ : net.OmegaFires m t m₁) (h₂ : net.OmegaFires m t m₂) : m₁ = m₂ := by
  funext p
  exact (h₁.2 p).trans (h₂.2 p).symm

/-- Any ω-marking above `weakestPreOmegaMarking t target` enables `t`.
Firing `t` from it produces an ω-marking covering `target`. -/
theorem WeightedNet.exists_omegaFires_cover_of_weakestPreOmegaMarking_le
    {P T : Type*} (net : WeightedNet P T) (t : T)
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
theorem WeightedNet.weakestPreOmegaMarking_coe {P T : Type*}
    (net : WeightedNet P T) (t : T) (target : Marking P) :
    net.weakestPreOmegaMarking t target = net.weakestPreMarking t target := by
  funext p
  simp [WeightedNet.weakestPreOmegaMarking, WeightedNet.weakestPreMarking]

/-- The ω-valued and concrete weakest predecessor sequence constructions
agree on concrete target markings. -/
theorem WeightedNet.weakestPreOmegaMarkingSequence_coe {P T : Type*}
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
    {P T : Type*} {net : WeightedNet P T}
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

/-! ## ω-marking transition system -/

/-- The ω-marking semantics of `net` as a labelled transition
system. Its states are all ω-markings, its labels are the transitions of the
weighted P/T net, and its transition relation is ω-firing. -/
def WeightedNet.omegaMarkingLTS {P T : Type*} (net : WeightedNet P T) :
    Cslib.LTS (OmegaMarking P) T where
  Tr := net.OmegaFires

/-- An edge of the ω-marking LTS is exactly an ω-firing. -/
@[simp]
theorem WeightedNet.omegaMarkingLTS_tr_iff {P T : Type*}
    (net : WeightedNet P T) (src : OmegaMarking P) (t : T)
    (tgt : OmegaMarking P) :
    net.omegaMarkingLTS.Tr src t tgt ↔ net.OmegaFires src t tgt :=
  Iff.rfl

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
    {P T : Type*} (net : WeightedNet P T) (ts : List T)
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

/-- A transition is enabled at an ω-marking exactly when the ω-marking LTS
has an outgoing edge carrying that transition. -/
theorem WeightedNet.omegaMarkingLTS_enabled_iff_exists_tr {P T : Type*}
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.omegaMarkingLTS.Tr m t m' :=
  net.omegaEnabled_iff_exists_omegaFires m t

/-! ## Relation with concrete firing semantics -/

/-- Lifting a concrete marking into an ω-marking preserves and reflects
enabledness. -/
theorem WeightedNet.enabled_iff_omegaEnabled_toOmega {P T : Type*}
    (net : WeightedNet P T) (m : Marking P) (t : T) :
    net.Enabled m t ↔ net.OmegaEnabled m t := by
  simp [WeightedNet.Enabled, WeightedNet.OmegaEnabled, Marking.toOmega]

/-- Lifting concrete source and target markings into the ω-markings
preserves and reflects firing. -/
theorem WeightedNet.fires_iff_omegaFires_toOmega {P T : Type*}
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
    {P T : Type*} {net : WeightedNet P T}
    {omegaSrc omegaTgt : OmegaMarking P} {t : T} {target : Marking P}
    (hfires : net.OmegaFires omegaSrc t omegaTgt)
    (htarget : target ≤ omegaTgt) :
    net.weakestPreMarking t target ≤ omegaSrc := by
  rw [← net.weakestPreOmegaMarking_coe t target]
  exact net.weakestPreOmegaMarking_le_of_omegaFires hfires htarget

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
    {P T : Type*} {net : WeightedNet P T}
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

/-- A marking `m` is coverable from `m₀` when there is a marking `m'`
reachable from `m₀` such that `m ≤ m'`. The order on markings is pointwise:
`m ≤ m'` means that `m p ≤ m' p` for every place `p`. -/
def WeightedNet.CoverableFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ m : Marking P) : Prop :=
  ∃ m', net.Reachable m₀ m' ∧ m ≤ m'

/-- An ω-marking `mω` is omega coverable from `m₀` when every ordinary
marking below `mω` is coverable from `m₀`.

Equivalently, the downward closure of `mω` among ordinary markings is
contained in the downward closure of the reachable markings from `m₀`:

```text
∀ m, m ≤ mω → ∃ m', Reachable m₀ m' ∧ m ≤ m'.
```
-/
def WeightedNet.OmegaCoverableFrom {P T : Type*} (net : WeightedNet P T)
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
                          │ toOmega ≤
                          │
mω.concretise reserve ≤ reached
                              ▲
                              │ Reachable from m₀
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
    {P T : Type*} {net : WeightedNet P T}
    {m₀ : Marking P} {mω : OmegaMarking P}
    (h : net.OmegaCoverableFrom m₀ mω) (reserve : Marking P) :
    net.CoverableFrom m₀ (mω.concretise reserve) := by
  exact h (mω.concretise reserve) (mω.concretise_toOmega_le reserve)

/-- The initial marking embedded as an ω-marking is omega coverable from
itself. Every concrete marking below `m₀` is covered by the reachable
marking `m₀`. -/
theorem WeightedNet.omegaCoverableFrom_initial
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.OmegaCoverableFrom m₀ m₀ := by
  intro m hle
  refine ⟨m₀, WeightedNet.Reachable.refl net m₀, ?_⟩
  intro p
  exact ENat.natCast_le_natCast.mp (hle p)

/- Transport a finite firing cover through soundness of its abstract source.

```text
finiteSrc ──t──▶ finiteTgt
    │                 │
    ≤                 ≤
    │                 │
reachableSrc ──t──▶ reachableTgt

demand ≤ finiteTgt
```

Source soundness supplies `reachableSrc`; firing monotonicity supplies
`reachableTgt`, which covers `demand`. -/
private theorem coverableFrom_of_finite_firing_cover
    {P T : Type*} {net : WeightedNet P T}
    {m₀ finiteSrc finiteTgt demand : Marking P}
    {src : OmegaMarking P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ src)
    (hsrcBelow : finiteSrc ≤ src)
    (hfires : net.Fires finiteSrc t finiteTgt)
    (hdemandBelow : demand ≤ finiteTgt) :
    net.CoverableFrom m₀ demand := by
  obtain ⟨reachableSrc, hreachableSrc, hfiniteSrcBelow⟩ :=
    hsound finiteSrc hsrcBelow
  have hfiniteReachable : net.Reachable finiteSrc finiteTgt :=
    ⟨[t], WeightedNet.FiresSequence.singleton hfires⟩
  obtain ⟨reachableTgt, hreachableTgt, hfiniteTgtBelow⟩ :=
    hfiniteReachable.mono hfiniteSrcBelow
  exact ⟨reachableTgt, hreachableSrc.trans hreachableTgt,
    hdemandBelow.trans hfiniteTgtBelow⟩

/-- Omega coverability is preserved by an ω-firing.

For every finite demand below `omegaTgt`, the firing determines a sufficient
finite demand below `omegaSrc`. Source omega coverability supplies a reachable
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
    {P T : Type*} {net : WeightedNet P T}
    {m₀ : Marking P} {omegaSrc omegaTgt : OmegaMarking P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ omegaSrc)
    (hfires : net.OmegaFires omegaSrc t omegaTgt) :
    net.OmegaCoverableFrom m₀ omegaTgt := by
  intro demand hdemand
  obtain ⟨finiteSrc, hsrcBelow, hfiniteFires, hdemandBelow⟩ :=
    net.exists_finite_firing_cover_of_omegaFires hfires hdemand
  exact coverableFrom_of_finite_firing_cover
    hsound hsrcBelow hfiniteFires hdemandBelow

end PetriNet
