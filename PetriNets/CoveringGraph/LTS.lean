/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Successor

/-!
# Covering transition system

Provides the (algorithm-independent) labelled transition system of the covering
graph of a weighted P/T net.

A first-occurrence node has one successor for every enabled transition. The
successor is computed from the node history by `successor`. A node whose
marking already occurs among its ancestors is terminal.-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P]

/-- The covering transition system of `net`.

An edge extends a first-occurrence node using an enabled transition and its
uniquely computed accelerated successor. -/
def coveringLTS (net : WeightedNet P T) : Cslib.LTS (Node P) T where
  Tr src t tgt :=
    src.IsFirstOccurrence ∧
      net.OmegaEnabled src.marking t ∧
      tgt = successor net src t

/-- A covering-LTS edge is exactly a first-occurrence, enabled node
extension. -/
@[simp]
theorem coveringLTS_tr_iff {src tgt : Node P} {t : T} :
    (coveringLTS net).Tr src t tgt ↔
      src.IsFirstOccurrence ∧
        net.OmegaEnabled src.marking t ∧
        tgt = successor net src t :=
  Iff.rfl

/-- The covering LTS is deterministic for each source and transition. -/
instance (net : WeightedNet P T) : (coveringLTS net).Deterministic := by
  constructor
  intro src t tgt₁ tgt₂ h₁ h₂
  exact h₁.2.2.trans h₂.2.2.symm

/-- A transition labels an outgoing edge exactly when the source is a first
occurrence and the transition is enabled at its marking. -/
theorem exists_coveringLTS_tr_iff (src : Node P) (t : T) :
    (∃ tgt, (coveringLTS net).Tr src t tgt) ↔
      src.IsFirstOccurrence ∧ net.OmegaEnabled src.marking t := by
  constructor
  · rintro ⟨_, hfirst, henabled, _⟩
    exact ⟨hfirst, henabled⟩
  · rintro ⟨hfirst, henabled⟩
    exact ⟨successor net src t, hfirst, henabled, rfl⟩

/-- A node which repeats an ancestor marking is terminal in the covering
LTS. -/
theorem coveringLTS_terminal_of_not_first_occurrence {src : Node P}
    (hduplicate : ¬ src.IsFirstOccurrence) :
    (coveringLTS net).IsTerminal src := by
  intro _ _ htr
  exact hduplicate htr.1

/-- A covering node is terminal exactly when it repeats an ancestor marking
or its marking enables no transition. -/
theorem coveringLTS_terminal_iff (src : Node P) :
    (coveringLTS net).IsTerminal src ↔
      ¬ src.IsFirstOccurrence ∨
        ∀ t, ¬ net.OmegaEnabled src.marking t := by
  constructor
  · intro hterminal
    by_cases hfirst : src.IsFirstOccurrence
    · right
      intro t henabled
      exact hterminal t (successor net src t) ⟨hfirst, henabled, rfl⟩
    · exact Or.inl hfirst
  · rintro (hduplicate | hdead)
    · exact coveringLTS_terminal_of_not_first_occurrence hduplicate
    · intro t _ htr
      exact hdead t htr.2.1

/-- A covering edge appends the target marking to the source path. -/
theorem ancestors_eq_history_of_tr {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt) :
    tgt.ancestors = src.history := by
  rw [htr.2.2]
  exact successor_ancestors net src t

/-- A covering edge preserves every place already equal to `ω`. -/
theorem marking_eq_top_of_tr {src tgt : Node P} {t : T} {p : P}
    (htr : (coveringLTS net).Tr src t tgt)
    (hp : src.marking p = ⊤) :
    tgt.marking p = ⊤ := by
  rw [htr.2.2]
  exact successor_preserves_top src t hp

/-- If a covering-LTS edge introduces no new `ω`-place, its target marking is
the unaccelerated firing result. -/
theorem marking_eq_rawSuccessor_of_tr_of_omegaPlaces_eq
    {src tgt : Node P} {t : T}
    (htr : (coveringLTS net).Tr src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    tgt.marking = rawSuccessor net src.marking t := by
  rw [htr.2.2]
  apply successor_marking_eq_rawSuccessor_of_omegaPlaces_eq
  rwa [← htr.2.2]

/-- Coverage is preserved across one concrete firing from a first-occurrence
node.

If `src.marking` covers `m` and `m` fires `t` to `m'`, the covering LTS has
the corresponding edge to `successor net src t`, whose marking covers `m'`.
-/
theorem coveringLTS_tr_cover_of_fires
    {src : Node P} {m m' : Marking P} {t : T}
    (hfirst : src.IsFirstOccurrence)
    (hcover : m ≤ src.marking)
    (hfires : net.Fires m t m') :
    (coveringLTS net).Tr src t (successor net src t) ∧
      m' ≤ (successor net src t).marking := by
  obtain ⟨henabled, hcoverNext⟩ := fires_le_successor hcover hfires
  exact ⟨⟨hfirst, henabled, rfl⟩, hcoverNext⟩

/-! ## Rooted covering graph -/

/-- The covering graph generated from (concrete) initial marking `m₀`. Its
states bundle a covering node with evidence that it is reachable from the
initial node. -/
def coveringGraph (net : WeightedNet P T) (m₀ : Marking P) :=
  (coveringLTS net).generatedBy (Node.initial m₀)

/-- The initial state of the rooted covering graph. -/
def coveringGraphInitial (net : WeightedNet P T) (m₀ : Marking P) :
    {node : Node P //
      (coveringLTS net).CanReach (Node.initial m₀) node} :=
  ⟨Node.initial m₀,
    Cslib.LTS.CanReach.refl (coveringLTS net) (Node.initial m₀)⟩

end FinitePlaces

end PetriNet.CoveringGraph
