/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability
public import PetriNets.MarkingGraph
public import PetriNets.LTS.Konig
public import Mathlib.Order.WellQuasiOrder

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

/-- **Dickson's lemma for ω-markings.** If the type of places is finite, every
infinite sequence of ω-markings m₀, m₁, m₂, … contains two markings mᵢ and mⱼ with i < j such that mᵢ ≤ mⱼ. -/
theorem exists_le_pair {P : Type*} [Finite P]
    (markings : ℕ → OmegaMarking P) :
    ∃ i j, i < j ∧ markings i ≤ markings j := by
  exact wellQuasiOrdered_le markings

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
  /- collect the elements that satisfy `m p = ⊤`.-/
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

/-- Acceleration never decreases an ω-marking. -/
theorem le_accelerate {P : Type*} (A : Set P) (m : OmegaMarking P) :
    m ≤ accelerate A m := by
  intro p
  by_cases hp : p ∈ A
  · rw [accelerate_apply_of_mem hp]
    exact le_top
  · rw [accelerate_apply_of_not_mem hp]

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

/-- Every edge reachable from `m₀` obeys the covering-graph step rule.
For an edge `src --t--> tgt`, first fire `t` to obtain `i`. A place `p` is
accelerated to `ω` exactly when the path to `src` contains a marking `a` with
`a ≤ src` and `a p < src p`; every other place retains its value in `i`. -/
def WeightedNet.CoverStepRuleFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : OmegaMarking P) (graph : Cslib.LTS (OmegaMarking P) T) : Prop :=
  ∀ {src}, graph.CanReach m₀ src →
    ∀ {t tgt}, graph.Tr src t tgt →
      net.ValidCoverStep graph m₀ src t tgt

/-- At every state reachable from `m₀`, each enabled Petri-net
transition labels at least one outgoing edge of `graph`. -/
def WeightedNet.TransitionCompleteFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : OmegaMarking P) (graph : Cslib.LTS (OmegaMarking P) T) : Prop :=
  ∀ {src}, graph.CanReach m₀ src →
    ∀ t, net.OmegaEnabled src t →
      ∃ tgt, graph.Tr src t tgt

/-- `IsCoveringGraphFrom net m₀ graph` characterises a covering graph by three
separate conditions: the cover-step rule, transition completeness, and
uniqueness of the outgoing edge carrying each transition label.

The cover-step and transition-completeness conditions concern states reachable
from `m₀.toOmega`. Reisig's condition (c) is expressed by requiring the entire
covering-graph LTS to be deterministic.
Loops are permitted; a covering tree can later be obtained by unfolding the
graph from this initial state. -/
def WeightedNet.IsCoveringGraphFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (graph : Cslib.LTS (OmegaMarking P) T) : Prop :=
  net.CoverStepRuleFrom m₀.toOmega graph ∧
    net.TransitionCompleteFrom m₀.toOmega graph ∧
    graph.Deterministic

/-- If a covering graph with finitely many transition labels has infinitely
many states reachable from its initial marking, then it has an infinite
execution starting at that marking.

This is a direct application of the generic LTS form of Kőnig's lemma: the
covering graph is deterministic by definition, and `T` is finite. -/
theorem WeightedNet.coveringGraph_omegaExecution_of_infinite
    {P T : Type*} [Finite T] {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hinfinite : {m | graph.CanReach m₀.toOmega m}.Infinite) :
    ∃ markings labels,
      graph.OmegaExecution markings labels ∧ markings 0 = m₀.toOmega := by
  let _ : graph.Deterministic := hgraph.2.2
  exact Cslib.LTS.exists_omegaExecution_of_infinite_reachable
    graph m₀.toOmega hinfinite

/-- Suppose the reachable covering-graph state `srcω` covers the ordinary
marking `src`, and `t` fires from `src` to `tgt`. Then the covering graph has
a `t`-labelled edge from `srcω` to a state `tgtω` which covers `tgt`.

The result completes the following order-enriched commuting square:

```text
       Fires t
src  ----------> tgt
 |                |
 | toOmega ≤      | toOmega ≤
 v                v
srcω ----------> tgtω
       graph.Tr t
```

The square commutes in the sense of the covering order rather than by
equality: `src.toOmega ≤ srcω` implies that the upper firing can be matched by
the lower graph edge with `tgt.toOmega ≤ tgtω`, for some `tgtω`.

This is the single-step lifting result used as the induction step in the
Covering Theorem. -/
theorem WeightedNet.lift_fires_to_coveringGraph
    {P T : Type*} {net : WeightedNet P T} {m₀ src tgt : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T} {srcω : OmegaMarking P} {t : T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hreach : graph.CanReach m₀.toOmega srcω)
    (hcover : src.toOmega ≤ srcω) (hfires : net.Fires src t tgt) :
    ∃ tgtω, graph.Tr srcω t tgtω ∧ tgt.toOmega ≤ tgtω := by
  have hω : net.OmegaFires src.toOmega t tgt.toOmega :=
    (net.fires_iff_omegaFires_toOmega src tgt t).mp hfires
  obtain ⟨i, hi, htgt_i⟩ := hω.mono hcover
  obtain ⟨tgtω, hedge⟩ := hgraph.2.1 hreach t hi.1
  obtain ⟨i', A, hi', _, htgtω⟩ := hgraph.1 hreach hedge
  cases net.omegaFires_is_deterministic hi hi'
  refine ⟨tgtω, hedge, ?_⟩
  calc
    tgt.toOmega ≤ i := htgt_i
    _ ≤ OmegaMarking.accelerate A i := OmegaMarking.le_accelerate A i
    _ = tgtω := htgtω.symm

/-- Lift a finite firing sequence to a path of the covering graph. If the
reachable graph state `srcω` covers the ordinary source marking `src`, then
the graph can follow the same transition sequence to a state covering the
ordinary target marking `tgt`.

This lifts the single-step commuting square to firing sequences:

```text
             FiresSequence ts
src  ------------------------------> tgt
 |                                      |
 | toOmega ≤                            | toOmega ≤
 v                                      v
srcω -------------------------------> tgtω
                 graph.MTr ts
```

The upper and lower paths carry the same transition list `ts`, and the square
commutes in the covering order.

This generalised statement supplies the induction hypothesis needed for the
finite-run form of the Covering Theorem. -/
theorem WeightedNet.lift_firesSequence_to_coveringGraph
    {P T : Type*} {net : WeightedNet P T} {m₀ src tgt : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T} {srcω : OmegaMarking P}
    {ts : List T} (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hreach : graph.CanReach m₀.toOmega srcω)
    (hcover : src.toOmega ≤ srcω)
    (hseq : net.FiresSequence src ts tgt) :
    ∃ tgtω, graph.MTr srcω ts tgtω ∧ tgt.toOmega ≤ tgtω := by
  induction hseq generalizing srcω with
  | nil =>
      exact ⟨srcω, Cslib.LTS.MTr.refl, hcover⟩
  | cons head tail ih =>
      obtain ⟨iω, htr, hcover_i⟩ :=
        net.lift_fires_to_coveringGraph hgraph hreach hcover head
      have hreach_i : graph.CanReach m₀.toOmega iω := by
        obtain ⟨labels, hmtr⟩ := hreach
        exact ⟨labels ++ [_], Cslib.LTS.MTr.stepR graph hmtr htr⟩
      obtain ⟨tgtω, htail, hcover_tgt⟩ := ih hreach_i hcover_i
      exact ⟨tgtω, Cslib.LTS.MTr.stepL htr htail, hcover_tgt⟩

/-- **Covering Theorem (Reisig, Theorem 17), finite-run form.**

Every finite firing sequence of the net is matched by a path in the covering
graph carrying the same transition sequence. The final graph state covers the
ordinary final marking. -/
theorem WeightedNet.covering_of_firesSequence
    {P T : Type*} {net : WeightedNet P T} {m₀ tgt : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T} {ts : List T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hseq : net.FiresSequence m₀ ts tgt) :
    ∃ tgtω, graph.MTr m₀.toOmega ts tgtω ∧ tgt.toOmega ≤ tgtω := by
  exact net.lift_firesSequence_to_coveringGraph hgraph
    (Cslib.LTS.CanReach.refl graph m₀.toOmega) le_rfl hseq

/-- **Covering Theorem (Reisig, Theorem 17), infinite-run form.**

Let `markings` and `labels` describe an infinite sequential run of the net
starting at `m₀`:

```text
markings 0 --labels 0--> markings 1 --labels 1--> markings 2 --> ...
```

The theorem constructs an infinite sequence `graphMarkings` forming an
execution of the covering graph with exactly the same transition labels:

```text
markings 0  --labels 0--> markings 1  --labels 1--> markings 2  --> ...
     |                            |                            |
     | toOmega ≤                  | toOmega ≤                  | toOmega ≤
     v                            v                            v
graphMarkings 0 --labels 0--> graphMarkings 1 --labels 1--> graphMarkings 2 --> ...
```

The lower execution starts at `m₀.toOmega`, and at every position `n` its
state covers the embedded ordinary marking:
`(markings n).toOmega ≤ graphMarkings n`. Thus every step of the ordinary run
is matched by a covering-graph edge with the same label. As noted by Reisig,
the converse is not true in general: a covering-graph execution need not
represent an ordinary sequential run. -/
theorem WeightedNet.covering_of_omegaExecution
    {P T : Type*} {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    {markings : Cslib.ωSequence (Marking P)} {labels : Cslib.ωSequence T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hrun : net.markingLTS.OmegaExecution markings labels)
    (hinitial : markings 0 = m₀) :
    ∃ graphMarkings : Cslib.ωSequence (OmegaMarking P),
      graph.OmegaExecution graphMarkings labels ∧
      graphMarkings 0 = m₀.toOmega ∧
      ∀ n, (markings n).toOmega ≤ graphMarkings n := by
  classical
  let StateAt (n : ℕ) :=
    {m : OmegaMarking P //
      graph.CanReach m₀.toOmega m ∧ (markings n).toOmega ≤ m}
  let initial : StateAt 0 :=
    ⟨m₀.toOmega, Cslib.LTS.CanReach.refl graph m₀.toOmega, by
      rw [hinitial]⟩
  have stepExists (n : ℕ) (m : StateAt n) :
      ∃ m', graph.Tr m.1 (labels n) m' ∧
        graph.CanReach m₀.toOmega m' ∧ (markings (n + 1)).toOmega ≤ m' := by
    obtain ⟨m', htr, hcover⟩ :=
      net.lift_fires_to_coveringGraph hgraph m.2.1 m.2.2 (hrun n)
    refine ⟨m', htr, ?_, hcover⟩
    obtain ⟨ts, hmtr⟩ := m.2.1
    exact ⟨ts ++ [labels n], Cslib.LTS.MTr.stepR graph hmtr htr⟩
  let next (n : ℕ) (m : StateAt n) : StateAt (n + 1) :=
    ⟨Classical.choose (stepExists n m),
      (Classical.choose_spec (stepExists n m)).2.1,
      (Classical.choose_spec (stepExists n m)).2.2⟩
  have next_tr (n : ℕ) (m : StateAt n) :
      graph.Tr m.1 (labels n) (next n m).1 := by
    exact (Classical.choose_spec (stepExists n m)).1
  let lifted : (n : ℕ) → StateAt n :=
    fun n => Nat.rec initial (fun n m => next n m) n
  have lifted_succ (n : ℕ) : lifted (n + 1) = next n (lifted n) := by
    rfl
  let graphMarkings : Cslib.ωSequence (OmegaMarking P) :=
    ⟨fun n => (lifted n).1⟩
  refine ⟨graphMarkings, ?_, ?_, ?_⟩
  · intro n
    change graph.Tr (lifted n).1 (labels n) (lifted (n + 1)).1
    rw [lifted_succ]
    exact next_tr n (lifted n)
  · rfl
  · intro n
    exact (lifted n).2.2

end PetriNet
