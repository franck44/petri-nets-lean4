/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph

/-!
# Termination of accelerating ω-marking sequences

This module isolates the Dickson argument shared by covering-graph and
Karp–Miller termination proofs.
-/

@[expose] public section

namespace PetriNet.OmegaMarking

/-- **Generic acceleration termination lemma.**

Consider an infinite sequence of ω-markings such that:

* the set of ω-places grows monotonically; and
* whenever two distinct markings are comparable and have the same ω-places,
  the acceleration rule would introduce a new ω-place in the later marking.

Then two positions in the sequence carry the same marking. The proof first
uses finiteness of the place type to find a suffix on which the ω-place set is
constant. Dickson's lemma supplies two comparable markings on that suffix.
If they were distinct, the second assumption would introduce a new ω-place,
contradicting stability. -/
theorem exists_eq_pair_of_omegaPlaces_mono
    {P : Type*} [Fintype P]
    (markings : ℕ → OmegaMarking P)
    (hmono : ∀ {i j}, i ≤ j →
      omegaPlaces (markings i) ⊆ omegaPlaces (markings j))
    (hgrow : ∀ {i j}, i < j → markings i ≤ markings j →
      omegaPlaces (markings i) = omegaPlaces (markings j) →
      markings i ≠ markings j →
      ∃ p, p ∉ omegaPlaces (markings i) ∧
        p ∈ omegaPlaces (markings j)) :
    ∃ i j, i < j ∧ markings i = markings j := by
  classical
  let cardAt (n : ℕ) := (omegaPlaces (markings n)).card
  have himage : (cardAt '' (Set.univ : Set ℕ)).Finite := by
    apply (Set.finite_Iic (Finset.univ : Finset P).card).subset
    rintro k ⟨n, _, rfl⟩
    exact Finset.card_le_univ _
  obtain ⟨n₀, _, hmax⟩ :=
    Set.Finite.exists_maximalFor' cardAt Set.univ himage Set.univ_nonempty
  have hstable : ∀ n, n₀ ≤ n →
      omegaPlaces (markings n) = omegaPlaces (markings n₀) := by
    intro n hn
    have hsub := hmono hn
    have hcard : cardAt n ≤ cardAt n₀ := by
      by_cases hle : cardAt n₀ ≤ cardAt n
      · exact hmax (Set.mem_univ n) hle
      · omega
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  obtain ⟨i, j, hij, hle⟩ :=
    exists_le_pair (fun n => markings (n₀ + n))
  let i' := n₀ + i
  let j' := n₀ + j
  have hi' : n₀ ≤ i' := by simp [i']
  have hj' : n₀ ≤ j' := by simp [j']
  have hij' : i' < j' := by omega
  have homega : omegaPlaces (markings i') =
      omegaPlaces (markings j') :=
    (hstable i' hi').trans (hstable j' hj').symm
  by_cases heq : markings i' = markings j'
  · exact ⟨i', j', hij', heq⟩
  · obtain ⟨p, hpold, hpnew⟩ := hgrow hij' hle homega heq
    apply False.elim
    apply hpold
    rw [homega]
    exact hpnew

end PetriNet.OmegaMarking
