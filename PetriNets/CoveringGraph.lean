/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Acceleration
public import PetriNets.MarkingGraph
public import PetriNets.LTS.Konig
public import Mathlib.Order.WellQuasiOrder

/-!
# Covering graphs

Provides covering graphs for weighted P/T nets. A covering graph state
is an ω-marking. A transition is an ω-firing step possibly combined with
*acceleration*. Acceleration detects unbounded growth of a place along a path and
introduces `ω` to represent the possible token counts at this place.

This module proves three principal properties:

1. When the place and transition types are finite, only finitely many
   covering-graph states are reachable.
2. Every concrete firing sequence can be lifted to a covering-graph path
   ending in an ω-marking that covers its concrete target.
3. Every concrete infinite execution can likewise be lifted to an infinite
   covering-graph execution.

## Purpose and acceleration

A covering graph is intended to give a finite representation of potentially
infinite behaviour in the marking graph. An ordinary natural-number component
records a concrete token count, while `ω` records that arbitrarily large token
counts can be accumulated at that place. The graph can therefore represent
unbounded growth without enumerating every concrete marking along it.

Acceleration detects such growth along a path. Suppose the current marking is
`m`, and an earlier marking `a` on the same path satisfies `a ≤ m`. If the
inequality is strict at a place `p`, then the path segment from `a` to `m` has
increased the token count at `p` without decreasing any component overall.
Monotonicity allows that segment to be repeated, so `p` can accumulate
arbitrarily many tokens. The successor of `m` therefore records `ω` at `p`.

Acceleration is path-dependent: the same ω-marking may justify different
accelerations when reached along different paths. This is why the definition
uses executions and their preceding states rather than only a local transition
relation.

## Two-stage construction

A covering graph is defined in two steps.

First, `coverStepLTS` contains all candidate steps: fire a transition, then
replace any chosen set of places by `ω`. This deliberately includes more
accelerations than a covering graph should retain.

Second, the covering-graph conditions retain only the accelerations justified
by growth from an earlier marking on the current path.

## Candidate acceleration steps

Suppose a net has three places and an ω-firing produces the raw marking
`(1, 3, 4)`. Possible accelerations of this marking are:

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

/-! ## Properties of ω-markings -/

/-- **Dickson's lemma for ω-marking sequences.** If the type of places is
finite, every infinite sequence of ω-markings `m₀, m₁, m₂, …` contains two
markings `mᵢ` and `mⱼ`, with `i < j`, such that `mᵢ ≤ mⱼ`. -/
theorem exists_le_pair {P : Type*} [Finite P]
    (markings : ℕ → OmegaMarking P) :
    ∃ i j, i < j ∧ markings i ≤ markings j := by
  exact wellQuasiOrdered_le markings

end OmegaMarking

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

/-- Along a reachable covering-graph edge, the set of places equal to `ω`
can only grow. -/
theorem WeightedNet.omegaPlaces_mono_of_tr {P T : Type*} [Fintype P]
    {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    {src tgt : OmegaMarking P} {t : T}
    (hreach : graph.CanReach m₀.toOmega src)
    (htr : graph.Tr src t tgt) :
    OmegaMarking.omegaPlaces src ⊆ OmegaMarking.omegaPlaces tgt := by
  intro p hp
  rw [OmegaMarking.mem_omegaPlaces] at hp ⊢
  exact (hgraph.1 hreach htr).preserves_top hp

/-- If a covering graph with finitely many transition labels has infinitely
many states reachable from its initial marking, then it has an infinite
execution starting at that marking and visiting pairwise distinct states.

This is a direct application of the generic LTS form of Kőnig's lemma: the
covering graph is deterministic by definition, and `T` is finite. -/
theorem WeightedNet.coveringGraph_omegaExecution_of_infinite
    {P T : Type*} [Finite T] {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hinfinite : {m | graph.CanReach m₀.toOmega m}.Infinite) :
    ∃ markings labels,
      graph.OmegaExecution markings labels ∧
      markings 0 = m₀.toOmega ∧ Function.Injective markings := by
  let _ : graph.Deterministic := hgraph.2.2
  exact Cslib.LTS.konig_strict
    graph m₀.toOmega hinfinite

/-- Along an infinite covering-graph execution, the set of `ω`-places at an
earlier position is contained in the set at every later position. -/
theorem WeightedNet.omegaPlaces_mono_of_omegaExecution
    {P T : Type*} [Fintype P] {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    {markings : Cslib.ωSequence (OmegaMarking P)}
    {labels : Cslib.ωSequence T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hexec : graph.OmegaExecution markings labels)
    (hinitial : markings 0 = m₀.toOmega)
    {i j : ℕ} (hij : i ≤ j) :
    OmegaMarking.omegaPlaces (markings i) ⊆
      OmegaMarking.omegaPlaces (markings j) := by
  have hreach (n : ℕ) : graph.CanReach m₀.toOmega (markings n) := by
    rw [← hinitial]
    exact ⟨labels.extract 0 n, hexec.extract_mTr (Nat.zero_le n)⟩
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
      · exact Finset.Subset.rfl
      · exact (ih (Nat.le_of_lt_succ hij')).trans
          (net.omegaPlaces_mono_of_tr hgraph (hreach j) (hexec j))

/-- On every infinite covering-graph execution over finitely many places,
the set of places equal to `ω` is constant from some position onwards.

The sets grow monotonically and are all subsets of the finite set of places.
Choose a position at which their cardinality is maximal. Every later set
contains that set but cannot have larger cardinality, so it is equal to it. -/
theorem WeightedNet.exists_omegaPlaces_stable_from
    {P T : Type*} [Fintype P] {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    {markings : Cslib.ωSequence (OmegaMarking P)}
    {labels : Cslib.ωSequence T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph)
    (hexec : graph.OmegaExecution markings labels)
    (hinitial : markings 0 = m₀.toOmega) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      OmegaMarking.omegaPlaces (markings n) =
        OmegaMarking.omegaPlaces (markings n₀) := by
  let cardAt (n : ℕ) := (OmegaMarking.omegaPlaces (markings n)).card
  have himage : (cardAt '' (Set.univ : Set ℕ)).Finite := by
    apply (Set.finite_Iic (Finset.univ : Finset P).card).subset
    rintro k ⟨n, _, rfl⟩
    exact Finset.card_le_univ _
  obtain ⟨n₀, _, hmax⟩ :=
    Set.Finite.exists_maximalFor' cardAt Set.univ himage Set.univ_nonempty
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hsub := net.omegaPlaces_mono_of_omegaExecution
    hgraph hexec hinitial hn
  have hcard : cardAt n ≤ cardAt n₀ := by
    by_cases hle : cardAt n₀ ≤ cardAt n
    · exact hmax (Set.mem_univ n) hle
    · omega
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- **Finiteness of covering graphs.** If the place and transition types are
finite, only finitely many states of a covering graph are reachable from its
initial marking.

The proof is by contradiction and combines Kőnig's lemma with Dickson's lemma.
Assume that infinitely many states are reachable. Since the transition type
is finite and the covering graph is deterministic, the `injective` version of
Kőnig lemma constructs an infinite execution

```text
m₀ → m₁ → m₂ → ⋯
```

whose markings are pairwise distinct. Since the place type is finite and an
existing `ω` component is preserved by every covering step (monotonicity),
the set of `ω`-places is constant after some position `n₀`.

Dickson's lemma is then applied to the suffix beginning at `n₀`. It gives two
positions `i < j` whose markings satisfy `mᵢ ≤ mⱼ`. The markings are distinct,
by the injectivity obtained from Kőnig's lemma, so at least one place has
strictly increased. As the `ω`-places have already stabilised, this strict
increase occurs at a place whose value in `mⱼ` is not `ω`. The earlier marking
`mᵢ` therefore justifies accelerating that place to `ω` after the step from
`mⱼ`. This creates a new `ω`-place, contradicting stabilisation. Hence only
finitely many states are reachable. -/
theorem WeightedNet.coveringGraph_reachable_finite
    {P T : Type*} [Finite P] [Finite T]
    {net : WeightedNet P T} {m₀ : Marking P}
    {graph : Cslib.LTS (OmegaMarking P) T}
    (hgraph : net.IsCoveringGraphFrom m₀ graph) :
    {m | graph.CanReach m₀.toOmega m}.Finite := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  by_contra hfinite
  have hinfinite : {m | graph.CanReach m₀.toOmega m}.Infinite :=
    hfinite
  obtain ⟨markings, labels, hexec, hinitial, hinjective⟩ :=
    net.coveringGraph_omegaExecution_of_infinite hgraph hinfinite
  obtain ⟨n₀, hstable⟩ :=
    net.exists_omegaPlaces_stable_from hgraph hexec hinitial
  obtain ⟨i, j, hij, hle⟩ :=
    OmegaMarking.exists_le_pair (fun n => markings (n₀ + n))
  let i' := n₀ + i
  let j' := n₀ + j
  have hi' : n₀ ≤ i' := by simp [i']
  have hj' : n₀ ≤ j' := by simp [j']
  have hij' : i' < j' := by omega
  have hne : markings i' ≠ markings j' := by
    intro heq
    have := hinjective heq
    omega
  obtain ⟨p, hp⟩ : ∃ p, markings i' p < markings j' p := by
    by_contra h
    push Not at h
    apply hne
    funext p
    exact le_antisymm (hle p) (h p)
  have hreach (n : ℕ) : graph.CanReach m₀.toOmega (markings n) := by
    rw [← hinitial]
    exact ⟨labels.extract 0 n, hexec.extract_mTr (Nat.zero_le n)⟩
  have hreach_i_j : graph.CanReach (markings i') (markings j') :=
    ⟨labels.extract i' j', hexec.extract_mTr (Nat.le_of_lt hij')⟩
  obtain ⟨raw, A, _, hjustified, hnext⟩ :=
    hgraph.1 (hreach j') (hexec j')
  have hpA : p ∈ A := by
    apply (hjustified p).2
    exact ⟨markings i', hreach i', hreach_i_j, hle, hp⟩
  have hpnext : markings (j' + 1) p = ⊤ := by
    rw [hnext]
    exact OmegaMarking.accelerate_apply_of_mem hpA
  have hsets_i_j : OmegaMarking.omegaPlaces (markings i') =
      OmegaMarking.omegaPlaces (markings j') :=
    (hstable i' hi').trans (hstable j' hj').symm
  have hpfinite : p ∉ OmegaMarking.omegaPlaces (markings j') := by
    intro hpomega
    have hpomega_i : p ∈ OmegaMarking.omegaPlaces (markings i') := by
      rw [hsets_i_j]
      exact hpomega
    rw [OmegaMarking.mem_omegaPlaces] at hpomega_i hpomega
    rw [hpomega_i, hpomega] at hp
    exact (lt_self_iff_false ⊤).mp hp
  have hsets_next : OmegaMarking.omegaPlaces (markings (j' + 1)) =
      OmegaMarking.omegaPlaces (markings j') :=
    (hstable (j' + 1) (by omega)).trans (hstable j' hj').symm
  apply hpfinite
  rw [← hsets_next, OmegaMarking.mem_omegaPlaces]
  exact hpnext

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
