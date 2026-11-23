/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph

/-!
# Increasing sequences of ω-markings

This module isolates a generic Dickson argument for infinite sequences of
`ω`-markings. It is used by the covering-graph and Karp–Miller termination
proofs.
-/

@[expose] public section

namespace PetriNet.OmegaMarking

/-- A sequence of `ω`-markings whose sets of `ω`-places grow monotonically
has a suffix on which that set is constant.

Every set of `ω`-places is a subset of the finite place type. Choose a
position at which its cardinality is maximal. Every later set contains it but
cannot have greater cardinality, so the two sets are equal. -/
theorem exists_omegaPlaces_stable_from
    {P : Type*} [Fintype P]
    (markings : ℕ → OmegaMarking P)
    (hmono : ∀ {i j}, i ≤ j →
      omegaPlaces (markings i) ⊆ omegaPlaces (markings j)) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      omegaPlaces (markings n) = omegaPlaces (markings n₀) := by
  classical
  -- Record only the number of ω-places at each position.
  let cardAt (n : ℕ) := (omegaPlaces (markings n)).card
  -- These cardinalities range over a finite set: none exceeds the total
  -- number of places.
  have himage : (cardAt '' (Set.univ : Set ℕ)).Finite := by
    apply (Set.finite_Iic (Finset.univ : Finset P).card).subset
    rintro k ⟨n, _, rfl⟩
    exact Finset.card_le_univ _
  -- Choose a position n₀ whose ω-place set has maximal cardinality.
  obtain ⟨n₀, _, hmax⟩ :=
    Set.Finite.exists_maximalFor' cardAt Set.univ himage Set.univ_nonempty
  -- We show that every later position has exactly the same ω-places.
  refine ⟨n₀, fun n hn ↦ ?_⟩
  -- Monotonicity gives inclusion from the set at n₀ into the set at n.
  have hsub := hmono hn
  -- Maximality of n₀ prevents the later set from having more elements.
  have hcard : cardAt n ≤ cardAt n₀ := by
    by_cases hle : cardAt n₀ ≤ cardAt n
    · exact hmax (Set.mem_univ n) hle
    · omega
  -- Inclusion and the cardinality bound force equality of the finite sets.
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- **Generic Dickson argument for `ω`-marking sequences.**

Consider an infinite sequence of `ω`-markings such that:

* the set of ω-places grows monotonically; and
* two comparable markings at different positions are equal whenever they
  have the same `ω`-places.

Then two different positions in the sequence carry the same marking. The
preceding stabilisation theorem supplies a suffix with constant `ω`-places,
and Dickson's lemma supplies two comparable markings on that suffix. The
second assumption makes those markings equal. -/
theorem exists_eq_pair_of_omegaPlaces_mono
    {P : Type*} [Fintype P]
    (markings : ℕ → OmegaMarking P)
    (hmono : ∀ {i j}, i ≤ j →
      omegaPlaces (markings i) ⊆ omegaPlaces (markings j))
    (heq : ∀ {i j}, i < j → markings i ≤ markings j →
      omegaPlaces (markings i) = omegaPlaces (markings j) →
      markings i = markings j) :
    ∃ i j, i < j ∧ markings i = markings j := by
  -- First choose a suffix on which the set of ω-places is constant.
  obtain ⟨n₀, hstable⟩ := exists_omegaPlaces_stable_from markings hmono
  -- Dickson's lemma finds two ordered positions in this suffix whose
  -- markings are comparable.
  obtain ⟨i, j, hij, hle⟩ :=
    exists_le_pair (fun n => markings (n₀ + n))
  -- Translate the suffix indices back to positions in the original sequence.
  let i' := n₀ + i
  let j' := n₀ + j
  have hi' : n₀ ≤ i' := by simp [i']
  have hj' : n₀ ≤ j' := by simp [j']
  have hij' : i' < j' := by omega
  -- Both positions lie in the stable suffix, so their ω-place sets agree.
  have homega : omegaPlaces (markings i') =
      omegaPlaces (markings j') :=
    (hstable i' hi').trans (hstable j' hj').symm
  -- Comparable markings with the same ω-places are equal by hypothesis.
  exact ⟨i', j', hij', heq hij' hle homega⟩

end PetriNet.OmegaMarking
