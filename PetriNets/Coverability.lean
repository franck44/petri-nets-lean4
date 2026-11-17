/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability
public import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Coverability

This module defines coverability for weighted P/T nets.

A marking `m` is coverable from an initial marking `m₀` when some marking
reachable from `m₀` contains at least as many tokens as `m` at every place.
Unlike reachability, coverability does not require `m` itself to be reached.

## Two-stage construction of a covering graph

We separate the definition of a covering graph into two stages.

First, `WeightedNet.coverStepLTS` augments the ordinary ω-firing semantics of
`WeightedNet.omegaMarkingLTS` with every possible acceleration choice. Each
acceleration edge consists of an ω-firing followed by replacing an arbitrary subset of
places by `ω`. Thus this LTS contains all ordinary ω-firing successors as well
as every possibly accelerated successor. The firing and acceleration are
combined in one edge carrying the original Petri-net transition; acceleration
does not introduce a separate silent transition.

Second, a covering-graph LTS is defined by imposing constraints on paths
of `coverStepLTS`. These constraints use the preceding node labels to select
exactly the accelerations justified by ancestors and to stop expanding nodes
that repeat an ancestor label. In this way `coverStepLTS` supplies all
candidate edges, while the path constraints characterise the edges in the
covering graph.

## Candidate acceleration steps

Suppose a net has three places and an ω-firing produces the raw marking
`(1, 3, 4)`. Candidate accelerations include all possible ways of accelerating some subset of places to `ω`.

* `(1, 3, 4)`, when no place is accelerated;
* `(ω, 3, 4)`, when only the first place is accelerated;
* `(1, ω, ω)`, when the second and third places are accelerated; and
* `(ω, ω, ω)`, when every place is accelerated.

The marking `(2, 3, 4)` is not a candidate acceleration of `(1, 3, 4)`:
acceleration may retain a finite value or replace it by `ω`, but it cannot
replace it by a different finite value.

For a two-place example, suppose firing `t` from `(2, 0)` consumes one token
from the first place and produces one in the second. Its raw result is
`(1, 1)`. The candidate cover-step LTS contains `t`-labelled edges to
`(1, 1)`, `(ω, 1)`, `(1, ω)`, and `(ω, ω)`. The ancestor condition of a
covering graph will later select the appropriate one of these candidates.

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

/-- Embed an ordinary marking into the ω-markings. Every finite token count
is mapped to the corresponding value in `ℕ∞`; no place is mapped to
`ω`. -/
def Marking.toOmega {P : Type*} (m : Marking P) : OmegaMarking P :=
  fun p => m p

@[simp]
theorem Marking.toOmega_apply {P : Type*} (m : Marking P) (p : P) :
    m.toOmega p = m p :=
  rfl

/-- A transition is enabled at an ω-marking when every place contains at
least its finite pre-incidence weight. A place labelled `ω` satisfies every
finite pre-incidence requirement, so it never prevents a transition from
being enabled. -/
def WeightedNet.OmegaEnabled {P T : Type*} (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : Prop :=
  ∀ p, (net.pre p t : ℕ∞) ≤ m p

/-- `net.OmegaFires m t m'` means that `t` is enabled at the ω-marking `m`
and firing it produces `m'`. Subtraction and addition are those of `ℕ∞`, so a
component equal to `ω` remains equal to `ω`. -/
def WeightedNet.OmegaFires {P T : Type*} (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) (m' : OmegaMarking P) : Prop :=
  net.OmegaEnabled m t ∧
    ∀ p,
      m' p = m p - net.pre p t + net.post p t

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

namespace OmegaMarking

/-- `accelerate A m` is the ω-marking obtained from `m` by replacing the
values at the chosen set `A` of places by `ω`. At every place outside `A`, it
retains the value of `m`.

Recording `A` explicitly will allow a covering graph to be defined
in an easier way. -/
noncomputable def accelerate {P : Type*} (A : Set P)
    (m : OmegaMarking P) : OmegaMarking P := by
  classical
  exact fun p => if p ∈ A then ⊤ else m p

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

end OmegaMarking

/-- A cover step first performs an ω-firing and then makes an arbitrary
possible choice of places (including the empty set) to accelerate to `ω`. -/
def WeightedNet.CoverStep {P T : Type*} (net : WeightedNet P T)
    (src : OmegaMarking P) (t : T) (tgt : OmegaMarking P) : Prop :=
  ∃ i A, net.OmegaFires src t i ∧ tgt = OmegaMarking.accelerate A i

/-- The LTS of all candidate cover steps. It contains an edge for every
ω-firing and every subset of places, including the empty subset, that may
subsequently be replaced by `ω`. A covering graph selects a subgraph whose
acceleration choices satisfy the required ancestor condition. -/
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

/-- A marking `m` is coverable from `m₀` when there is a marking `m'`
reachable from `m₀` such that `m ≤ m'`. The order on markings is pointwise:
`m ≤ m'` means that `m p ≤ m' p` for every place `p`. -/
def WeightedNet.CoverableFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ m : Marking P) : Prop :=
  ∃ m', net.Reachable m₀ m' ∧ m ≤ m'

end PetriNet
