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

This module defines coverability for weighted P/T nets.

A marking `m` is coverable from an initial marking `m₀` when some marking
reachable from `m₀` contains at least as many tokens as `m` at every place.
Unlike reachability, coverability does not require `m` itself to be reached.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

/-- An ω-marking assigns either a natural-number token count or `ω` to each
place. The value `ω`, represented by `⊤` (top), denotes an arbitrarily large token
count. Mathlib's extended natural numbers `ℕ∞` are defined using `WithTop ℕ`.

The order and arithmetic come from `ℕ∞ = WithTop ℕ`. In particular, for every
finite `n : ℕ`, we have `n ≤ ω`, `ω + n = n + ω = ω`, and `ω - n = ω`.
Consequently, consuming or producing a finite number of tokens at a place
labelled `ω` leaves that place labelled `ω`. We do not need to give `ω - ω`
a Petri net interpretation because arc weights are always finite and different to `ω`. -/
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

/-- Embed an ordinary marking into the ω-markings. Every finite token count
is mapped to the corresponding value in `ℕ∞`; no place is mapped to
`ω`. -/
def Marking.toOmega {P : Type*} (m : Marking P) : OmegaMarking P :=
  fun p => m p

@[simp]
theorem Marking.toOmega_apply {P : Type*} (m : Marking P) (p : P) :
    m.toOmega p = m p :=
  rfl

/-- Replace every `ω` component of an omega marking by a prescribed finite
reserve, while retaining the exact value of every finite component.

```text
finiteApprox (3, ω, 5, ω) (r₀, r₁, r₂, r₃) = (3, r₁, 5, r₃)
```

This construction is used when an omega-coverability hypothesis must provide
a reachable ordinary marking with sufficiently many tokens at the omega
places. -/
def OmegaMarking.finiteApprox {P : Type*}
    (m : OmegaMarking P) (reserve : Marking P) : Marking P :=
  fun p => if m p = ⊤ then reserve p else (m p).toNat

/-- A finite approximation embeds below the omega marking it approximates. -/
theorem OmegaMarking.finiteApprox_toOmega_le {P : Type*}
    (m : OmegaMarking P) (reserve : Marking P) :
    (m.finiteApprox reserve).toOmega ≤ m := by
  intro p
  by_cases hp : m p = ⊤
  · simp [OmegaMarking.finiteApprox, hp]
  · simp only [Marking.toOmega_apply, OmegaMarking.finiteApprox, hp,
      ↓reduceIte]
    exact (ENat.natCast_toNat hp).le

/-- At an `ω` component, `finiteApprox` uses the supplied reserve. -/
@[simp]
theorem OmegaMarking.finiteApprox_apply_of_eq_top {P : Type*}
    {m : OmegaMarking P} {reserve : Marking P} {p : P}
    (hp : m p = ⊤) :
    m.finiteApprox reserve p = reserve p := by
  simp [OmegaMarking.finiteApprox, hp]

/-- At a finite component, `finiteApprox` retains its exact natural value. -/
theorem OmegaMarking.finiteApprox_apply_of_ne_top {P : Type*}
    {m : OmegaMarking P} {reserve : Marking P} {p : P}
    (hp : m p ≠ ⊤) :
    (m.finiteApprox reserve p : ℕ∞) = m p := by
  simp only [OmegaMarking.finiteApprox, hp, ↓reduceIte]
  exact ENat.natCast_toNat hp

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

/-- Firing preserves every component already equal to `ω`. Arc weights are
finite, so consuming and producing tokens cannot change `ω`. -/
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

/-- Firing a transition from a ω-marking has a unique result. -/
theorem WeightedNet.omegaFires_is_deterministic {P T : Type*}
    {net : WeightedNet P T} {m m₁ m₂ : OmegaMarking P} {t : T}
    (h₁ : net.OmegaFires m t m₁) (h₂ : net.OmegaFires m t m₂) : m₁ = m₂ := by
  funext p
  exact (h₁.2 p).trans (h₂.2 p).symm

/-- The unrestricted ω-marking semantics of `net` as a labelled transition
system. Its states are all ω-markings, its labels are the transitions of the
net, and its transition relation is ω-firing. It does not perform
acceleration; acceleration will be imposed separately along paths of the
covering graph. -/
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

/-- A transition is enabled at an ω-marking exactly when the ω-marking LTS
has an outgoing edge carrying that transition. -/
theorem WeightedNet.omegaMarkingLTS_enabled_iff_exists_tr {P T : Type*}
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.omegaMarkingLTS.Tr m t m' :=
  net.omegaEnabled_iff_exists_omegaFires m t

/-- Embedding an ordinary marking into the ω-markings preserves and reflects
enabledness. Mathematically this is immediate: `toOmega` changes only the
codomain from `ℕ` to `ℕ∞` and preserves every finite token count. -/
theorem WeightedNet.enabled_iff_omegaEnabled_toOmega {P T : Type*}
    (net : WeightedNet P T) (m : Marking P) (t : T) :
    net.Enabled m t ↔ net.OmegaEnabled m.toOmega t := by
  simp [WeightedNet.Enabled, WeightedNet.OmegaEnabled, Marking.toOmega]

/-- Embedding ordinary source and target markings into the ω-markings
preserves and reflects firing. Thus ordinary firing is represented exactly by
ω-firing between markings whose components are all finite. -/
theorem WeightedNet.fires_iff_omegaFires_toOmega {P T : Type*}
    (net : WeightedNet P T) (m m' : Marking P) (t : T) :
    net.Fires m t m' ↔ net.OmegaFires m.toOmega t m'.toOmega := by
  constructor
  · rintro ⟨henabled, hfires⟩
    constructor
    · apply (net.enabled_iff_omegaEnabled_toOmega m t).mp
      exact henabled
    · intro p
      simp
      rw [hfires p]
      rw [ENat.natCast_add, ENat.natCast_sub]
  · rintro ⟨henabled, hfires⟩
    constructor
    · exact (net.enabled_iff_omegaEnabled_toOmega m t).mpr henabled
    · intro p
      have hp := hfires p
      simp at hp
      exact_mod_cast hp

/-- The least marking from which firing `t` can cover `target`.

At each place, it contains the tokens consumed by `t`, plus the part of the
target demand not supplied by the post-incidence of `t`:

```text
leastPreMarking(p) = pre(p,t) + (target(p) - post(p,t)).
```

This is the standard one-step predecessor construction used in backward
coverability arguments. -/
def WeightedNet.leastPreMarking {P T : Type*} (net : WeightedNet P T)
    (t : T) (target : Marking P) : Marking P := fun p =>
  net.pre p t + (target p - net.post p t)

/-- Any marking above `leastPreMarking` enables `t`, and its post-firing
marking covers `target`.

Thus `leastPreMarking` is a threshold for one-step backward coverability, not
merely one particular source from which the target can be covered. -/
theorem WeightedNet.fires_firingResult_cover_of_leastPreMarking_le
    {P T : Type*} (net : WeightedNet P T) (t : T) (target : Marking P)
    {src : Marking P} (hsrc : net.leastPreMarking t target ≤ src) :
    net.Fires src t (net.firingResult src t) ∧
      target ≤ net.firingResult src t := by
  have henabled : net.Enabled src t := by
    intro p
    calc
      net.pre p t ≤ net.leastPreMarking t target p := by
        simp [WeightedNet.leastPreMarking]
      _ ≤ src p := hsrc p
  have hfires : net.Fires src t (net.firingResult src t) :=
    ⟨henabled, fun _ => rfl⟩
  have htarget : target ≤ net.firingResult src t := by
    intro p
    have hp := hsrc p
    simp [WeightedNet.leastPreMarking] at hp ⊢
    omega
  exact ⟨hfires, htarget⟩

/-- Propagate a concrete target demand backwards across an ω-firing.

Assume `t` fires from `omegaSrc` to `omegaTgt`.
Let `target` be a concrete marking

Then the least ordinary marking sufficient to cover `target` after firing `t` lies below `omegaSrc`:

```text
          omegaSrc ─────────────t──────────────▶ omegaTgt
              ▲                                      ▲
           toOmega ≤                              toOmega ≤
              │                                      │
leastPreMarking t target ──t──▶ a marking covering target
```

At a place where `omegaSrc` is `ω`, this is immediate because
the predecessor demand is finite. At a finite place, it follows from the
ω-firing equation and `target.toOmega ≤ omegaTgt`.

This theorem is the backward step used to turn a finite demand at an abstract
ω-successor into a finite demand at its source. -/
theorem WeightedNet.leastPreMarking_toOmega_le_of_omegaFires
    {P T : Type*} {net : WeightedNet P T}
    {omegaSrc omegaTgt : OmegaMarking P} {t : T} {target : Marking P}
    (hfires : net.OmegaFires omegaSrc t omegaTgt)
    (htarget : target.toOmega ≤ omegaTgt) :
    (net.leastPreMarking t target).toOmega ≤ omegaSrc := by
  intro p
  by_cases hp : omegaSrc p = ⊤
  · simp [WeightedNet.leastPreMarking, hp]
  · have henabledNat : net.pre p t ≤ (omegaSrc p).toNat := by
      exact ENat.natCast_le_natCast.mp <| by
        rw [ENat.natCast_toNat hp]
        exact hfires.1 p
    have htargetNat : target p ≤
        (omegaSrc p).toNat - net.pre p t + net.post p t := by
      have hpCover := htarget p
      rw [hfires.2 p, ← ENat.natCast_toNat hp] at hpCover
      exact ENat.natCast_le_natCast.mp <| by
        simpa using hpCover
    simp only [WeightedNet.leastPreMarking, Marking.toOmega_apply]
    rw [← ENat.natCast_toNat hp]
    exact_mod_cast (show net.pre p t + (target p - net.post p t) ≤
      (omegaSrc p).toNat by omega)

/-- Realise a finite demand below an ω-firing target by an ordinary firing.

Given `omegaSrc ─t→ omegaTgt` and an ordinary `demand` represented below
`omegaTgt`, the theorem constructs a finite source below `omegaSrc`. Firing
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
    (hdemand : demand.toOmega ≤ omegaTgt) :
    ∃ finiteSrc,
      finiteSrc.toOmega ≤ omegaSrc ∧
      net.Fires finiteSrc t (net.firingResult finiteSrc t) ∧
      demand ≤ net.firingResult finiteSrc t := by
  let finiteSrc := net.leastPreMarking t demand
  have hsrcBelow : finiteSrc.toOmega ≤ omegaSrc :=
    net.leastPreMarking_toOmega_le_of_omegaFires hfires hdemand
  obtain ⟨hfiniteFires, hdemandBelow⟩ :=
    net.fires_firingResult_cover_of_leastPreMarking_le t demand le_rfl
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
∀ m, m.toOmega ≤ mω → ∃ m', Reachable m₀ m' ∧ m ≤ m'.
```
-/
def WeightedNet.OmegaCoverableFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (mω : OmegaMarking P) : Prop :=
  ∀ m, m.toOmega ≤ mω → net.CoverableFrom m₀ m

/-- Obtain a reachable cover for a chosen finite approximation of an
omega-coverable marking.

The marking `mω.finiteApprox reserve` retains the exact finite components of
`mω` and uses `reserve p` wherever `mω p = ω`. Since this concrete marking
is below `mω`, the definition of `OmegaCoverableFrom` supplies a reachable
marking `reached` which covers it:

```text
                         mω
                          ▲
                          │ toOmega ≤
                          │
mω.finiteApprox reserve ≤ reached
                              ▲
                              │ Reachable from m₀
                              │
                             m₀
```

Equivalently, the resulting reachable marking satisfies:

* if `mω p = (n : ℕ∞)` for some `n : ℕ`, then `n ≤ reached p`; and
* if `mω p = ω`, then `reserve p ≤ reached p`.

Thus callers may choose arbitrarily large, independently specified finite
reserves at the omega places. The reachable witness may depend on the chosen
reserve; the theorem does not claim that one concrete marking realises all
possible reserves simultaneously. -/
theorem WeightedNet.OmegaCoverableFrom.coverable_finiteApprox
    {P T : Type*} {net : WeightedNet P T}
    {m₀ : Marking P} {mω : OmegaMarking P}
    (h : net.OmegaCoverableFrom m₀ mω) (reserve : Marking P) :
    net.CoverableFrom m₀ (mω.finiteApprox reserve) := by
  exact h (mω.finiteApprox reserve) (mω.finiteApprox_toOmega_le reserve)

/-- The initial marking embedded as an ω-marking is omega coverable from
itself. Every ordinary marking below `m₀.toOmega` is covered by the reachable
marking `m₀`. -/
theorem WeightedNet.omegaCoverableFrom_initial
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.OmegaCoverableFrom m₀ m₀.toOmega := by
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
    (hsrcBelow : finiteSrc.toOmega ≤ src)
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
