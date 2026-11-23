/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability

/-!
# Acceleration of ω-markings

Provides acceleration of ω-markings and the candidate transition system used
to construct covering graphs for weighted P/T nets.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace OmegaMarking

/-! ## ω-places and concrete markings -/

/-- The finite set of places at which a given ω-marking has value `ω`.

For example, if a three-place marking has values

```text
m = (3, ω, ω),
```

then `omegaPlaces m` is the set containing the second and third places. The
function does not construct or enumerate ω-markings: it takes one marking and
records precisely which of its components are `ω`.

The result is a `Finset P` because the place type `P` is finite. It is obtained
by filtering the finite set of all places. -/
noncomputable def omegaPlaces {P : Type*} [Fintype P]
    (m : OmegaMarking P) : Finset P := by
  classical
  exact Finset.univ.filter fun p => m p = ⊤

/-- A place belongs to `omegaPlaces m` exactly when its value in `m` is `ω`.

This theorem is the membership interface for `omegaPlaces`: it allows proofs
to move between the finite-set statement `p ∈ omegaPlaces m` and the marking
equation `m p = ⊤`. -/
@[simp]
theorem mem_omegaPlaces {P : Type*} [Fintype P]
    {m : OmegaMarking P} {p : P} :
    p ∈ omegaPlaces m ↔ m p = ⊤ := by
  classical
  simp [omegaPlaces]

/-- Convert an ω-marking containing no `ω` to a concrete marking.

The proof argument makes this conversion deliberately unavailable for a
genuinely infinite ω-marking: `ENat.toNat` alone assigns a natural value to
`ω`, which would not be a faithful conversion. -/
def toNat {P : Type*} [Fintype P] (m : OmegaMarking P)
    (_ : omegaPlaces m = ∅) : Marking P :=
  fun p => (m p).toNat

/-- Converting an ω-marking without any `ω` component to natural numbers and
embedding it again recovers the original marking. -/
theorem toOmega_toNat_eq_self {P : Type*} [Fintype P]
    {m : OmegaMarking P} (hfinite : omegaPlaces m = ∅) :
    (m.toNat hfinite).toOmega = m := by
  funext p
  apply ENat.natCast_toNat
  intro hp
  have : p ∈ omegaPlaces m := mem_omegaPlaces.mpr hp
  rw [hfinite] at this
  simp at this

/-! ## Acceleration -/

/-- `accelerate A m` is the ω-marking obtained from `m` by replacing the
values at the chosen set `A` of places by `ω`. At every place outside `A`, it
retains the value of `m`. The set `A` records exactly which places are
accelerated. -/
noncomputable def accelerate {P : Type*} (A : Set P)
    (m : OmegaMarking P) : OmegaMarking P := by
  classical
  exact fun p => if p ∈ A then ⊤ else m p

/-- Executable acceleration for a finite set of places. -/
def accelerateFinset {P : Type*} [DecidableEq P] (A : Finset P)
    (m : OmegaMarking P) : OmegaMarking P :=
  fun p => if p ∈ A then ⊤ else m p

/-- Finite-set acceleration agrees with set-based acceleration. -/
theorem accelerateFinset_eq_accelerate {P : Type*} [DecidableEq P]
    (A : Finset P) (m : OmegaMarking P) :
    accelerateFinset A m = accelerate (A : Set P) m := by
  funext p
  by_cases hp : p ∈ A <;> simp [accelerateFinset, accelerate, hp]

/-- A place selected for acceleration has value `ω`. -/
@[simp]
theorem accelerate_apply_of_mem {P : Type*} {A : Set P}
    {m : OmegaMarking P} {p : P} (hp : p ∈ A) :
    accelerate A m p = ⊤ := by
  classical
  simp [accelerate, hp]

/-- A place not selected for acceleration retains its original value. -/
@[simp]
theorem accelerate_apply_of_not_mem {P : Type*} {A : Set P}
    {m : OmegaMarking P} {p : P} (hp : p ∉ A) :
    accelerate A m p = m p := by
  classical
  simp [accelerate, hp]

/-- Acceleration never decreases an ω-marking. -/
theorem le_accelerate {P : Type*} (A : Set P) (m : OmegaMarking P) :
    m ≤ accelerate A m := by
  intro p
  by_cases hp : p ∈ A
  · rw [accelerate_apply_of_mem hp]
    exact le_top
  · rw [accelerate_apply_of_not_mem hp]

/-! ## Justified acceleration -/

/-- `AccelerationJustifiedFrom graph root m A` states that `A` is exactly the
set of places justified for acceleration at the current marking `m`.

Following Reisig, a place `p` belongs to `A` precisely when some path from
`root` to `m` contains a marking `a` such that `a ≤ m` and `a p < m p`. The
two reachability conditions below express that a path from `root` to `m` can
be formed through `a`.

This condition determines which places will be set to `ω` in the successor of
`m`. It compares `a` with `m`, not with the result of the transition
subsequently fired from `m`. -/
def AccelerationJustifiedFrom {P T : Type*}
    (graph : Cslib.LTS (OmegaMarking P) T) (root m : OmegaMarking P)
    (A : Set P) : Prop :=
  ∀ p, p ∈ A ↔
    ∃ a, graph.CanReach root a ∧ graph.CanReach a m ∧
      a ≤ m ∧ a p < m p

end OmegaMarking

/-! ## Candidate and valid cover steps -/

/-- A cover step first performs an ω-firing and then makes an arbitrary
possible choice of places (including the empty set) to accelerate to `ω`. -/
def WeightedNet.CoverStep {P T : Type*} (net : WeightedNet P T)
    (src : OmegaMarking P) (t : T) (tgt : OmegaMarking P) : Prop :=
  ∃ i A, net.OmegaFires src t i ∧ tgt = OmegaMarking.accelerate A i

/-- The LTS of all candidate cover steps. It contains an edge for every
ω-firing and every subset of places, including the empty subset, that may
subsequently be replaced by `ω`. -/
def WeightedNet.coverStepLTS {P T : Type*} (net : WeightedNet P T) :
    Cslib.LTS (OmegaMarking P) T where
  Tr := net.CoverStep

/-- An edge of `coverStepLTS` is exactly a candidate cover step. -/
@[simp]
theorem WeightedNet.coverStepLTS_tr_iff {P T : Type*}
    (net : WeightedNet P T) (src : OmegaMarking P) (t : T)
    (tgt : OmegaMarking P) :
    net.coverStepLTS.Tr src t tgt ↔ net.CoverStep src t tgt :=
  Iff.rfl

/-- Every ω-firing is a cover step that chooses no new place to accelerate. -/
theorem WeightedNet.OmegaFires.coverStep {P T : Type*}
    {net : WeightedNet P T} {src tgt : OmegaMarking P} {t : T}
    (h : net.OmegaFires src t tgt) : net.CoverStep src t tgt := by
  refine ⟨tgt, ∅, h, ?_⟩
  funext p
  classical
  simp [OmegaMarking.accelerate]

/-- A transition is enabled at an ω-marking exactly when `coverStepLTS` has
an outgoing edge carrying that transition. -/
theorem WeightedNet.coverStepLTS_enabled_iff_exists_tr {P T : Type*}
    (net : WeightedNet P T) (m : OmegaMarking P) (t : T) :
    net.OmegaEnabled m t ↔ ∃ m', net.coverStepLTS.Tr m t m' := by
  constructor
  · intro henabled
    obtain ⟨m', hfires⟩ :=
      (net.omegaEnabled_iff_exists_omegaFires m t).mp henabled
    exact ⟨m', hfires.coverStep⟩
  · rintro ⟨_, _, _, hfires, _⟩
    exact hfires.1

/-- `ValidCoverStep graph root src t tgt` means that `t` fires from `src`, and
the firing result is accelerated exactly at the places justified by a path
from `root` to `src`, producing `tgt`. -/
def WeightedNet.ValidCoverStep {P T : Type*} (net : WeightedNet P T)
    (graph : Cslib.LTS (OmegaMarking P) T) (root src : OmegaMarking P)
    (t : T) (tgt : OmegaMarking P) : Prop :=
  ∃ i A, net.OmegaFires src t i ∧
    OmegaMarking.AccelerationJustifiedFrom graph root src A ∧
    tgt = OmegaMarking.accelerate A i

/-- A valid covering step preserves every component already equal to `ω`.
The firing itself preserves `ω`, and the subsequent acceleration can only
introduce additional `ω` components. -/
theorem WeightedNet.ValidCoverStep.preserves_top {P T : Type*}
    {net : WeightedNet P T} {graph : Cslib.LTS (OmegaMarking P) T}
    {root src tgt : OmegaMarking P} {t : T}
    (hstep : net.ValidCoverStep graph root src t tgt)
    {p : P} (hp : src p = ⊤) : tgt p = ⊤ := by
  obtain ⟨i, A, hfires, _, rfl⟩ := hstep
  by_cases hpA : p ∈ A
  · exact OmegaMarking.accelerate_apply_of_mem hpA
  · rw [OmegaMarking.accelerate_apply_of_not_mem hpA]
    exact hfires.preserves_top hp

end PetriNet
