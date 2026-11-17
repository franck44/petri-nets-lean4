/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability
public import Cslib.Foundations.Semantics.LTS.Execution

/-!
# Covering graphs

This module defines the path properties that characterise a covering graph.
A candidate graph is an LTS whose states are ω-markings and whose labels are
Petri-net transitions. It may contain loops. A covering tree can later be
obtained by unfolding its executions from the initial marking.

The construction has two levels:

* `WeightedNet.coverStepLTS` contains every ω-firing followed by every possible
  choice of places to accelerate;
* a covering graph retains paths for which the chosen accelerated places are
  exactly those justified by growth over an earlier marking on the path.

An execution records the successive states of a path. This is necessary
because acceleration depends on earlier states, rather than only on the
source of the current edge.

## Two-stage construction

First, `WeightedNet.coverStepLTS` augments the ordinary ω-firing semantics of
`WeightedNet.omegaMarkingLTS` with every possible acceleration choice. Each
edge consists of an ω-firing followed by replacing an arbitrary subset of
places by `ω`. The firing and acceleration are combined in one edge carrying
the original Petri-net transition; acceleration does not introduce a separate
silent transition.

Second, the covering-graph properties impose constraints on paths of
`coverStepLTS`. These constraints use preceding states on each path to select
exactly the accelerations justified by earlier markings. Thus `coverStepLTS`
supplies all candidate edges, while the path constraints characterise the
edges of a covering graph.

## Candidate acceleration steps

Suppose a net has three places and an ω-firing produces the raw marking
`(1, 3, 4)`. Candidate accelerations include all possible ways of accelerating
a subset of places to `ω`:

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
`(1, 1)`, `(ω, 1)`, `(1, ω)`, and `(ω, ω)`. The path constraint of a covering
graph selects the appropriate candidate.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

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

/-- The set `A` of places is justified for accelerating the raw marking `m`
along a path with state list `ancestors` when a place belongs to `A` exactly
if `m` strictly increases there over an earlier marking which it covers.

The list is intended to contain every state preceding the accelerated target,
including the source of the current edge. -/
def AccelerationJustifiedBy {P : Type*} (ancestors : List (OmegaMarking P))
    (m : OmegaMarking P) (A : Set P) : Prop :=
  ∀ p, p ∈ A ↔
    ∃ a ∈ ancestors, a ≤ m ∧ a p < m p

end OmegaMarking

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

/-- A candidate edge is a valid cover step along `ancestors` when it first
performs an ω-firing and then accelerates exactly the places justified by the
earlier markings in `ancestors`. -/
def WeightedNet.CoverStepAlong {P T : Type*} (net : WeightedNet P T)
    (ancestors : List (OmegaMarking P)) (src : OmegaMarking P) (t : T)
    (tgt : OmegaMarking P) : Prop :=
  ∃ i A, net.OmegaFires src t i ∧
    OmegaMarking.AccelerationJustifiedBy ancestors i A ∧
    tgt = OmegaMarking.accelerate A i

/-- `graph` is a covering graph of `net` from `m₀` when all of its paths from
`m₀.toOmega` use correctly accelerated cover steps, and every transition
enabled at the end of such a path labels an outgoing graph edge.

Only the part reachable from `m₀.toOmega` is constrained. Consequently the
initial state is fixed to `m₀.toOmega`, every relevant graph state is reached
by construction, and loops are permitted. -/
def WeightedNet.IsCoveringGraphFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (graph : Cslib.LTS (OmegaMarking P) T) : Prop :=
  (∀ {src ts states},
      graph.Execution m₀.toOmega ts src states →
      ∀ {t tgt}, graph.Tr src t tgt →
        net.CoverStepAlong states src t tgt) ∧
  (∀ {src ts states},
      graph.Execution m₀.toOmega ts src states →
      ∀ t, net.OmegaEnabled src t →
        ∃ tgt, graph.Tr src t tgt)

end PetriNet
