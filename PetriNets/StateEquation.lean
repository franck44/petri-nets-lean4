/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Incidence
public import PetriNets.Reachability

/-!
# State equations for weighted P/T nets

Provides firing-count vectors and state equations for finite transition
sequences.

A firing-count vector is associated with each finite transition sequence. For a
list `ts`, the value `firingCount ts t` gives the number of occurrences of
transition `t` in `ts`.

The count vector is represented as an ordinary function `T → ℕ`. Although its
type does not imply finite support, its support is finite because it is
derived from a finite list.

Equality on `T` must be decidable because the firing-count vector counts
occurrences of each transition in a list.

The state equation is a necessary, but not sufficient, condition for
reachability: it records the total effect of the transitions but not whether
they can fire in the required order. In particular, two executable sequences
with the same source marking and firing-count vector have the same target
marking. This does not mean that the transitions may be reordered
arbitrarily: a different order may not be executable because an intermediate
transition is not enabled.
-/

@[expose] public section

namespace PetriNet

/-! ## Firing-count vectors -/

/-- The firing-count vector of a transition sequence. -/
def firingCount {T : Type*} [DecidableEq T] (ts : List T) : T → ℕ :=
  fun t => ts.count t

/-- The empty transition sequence has the zero firing-count vector. -/
@[simp]
theorem firingCount_nil {T : Type*} [DecidableEq T] :
    firingCount ([] : List T) = (0 : T → ℕ) := by
  funext t
  simp [firingCount]

/-- The firing-count vector of concatenated transition sequences is the
pointwise sum of their firing-count vectors. -/
@[simp]
theorem firingCount_append {T : Type*} [DecidableEq T]
    (ts₁ ts₂ : List T) :
    firingCount (ts₁ ++ ts₂) = firingCount ts₁ + firingCount ts₂ := by
  funext t
  simp [firingCount]

/-- A weighted sum of firing counts equals the sum of the corresponding values
along the transition list.

For example, let `t₁` and `t₂` be distinct transitions, let
`ts = [t₁, t₂, t₁]`, and suppose `f t₁ = 3` and `f t₂ = 5`. The count-weighted
sum is `2 * 3 + 1 * 5 = 11`, while the sum along the mapped list is
`3 + 5 + 3 = 11`. -/
theorem firingCount_weighted_sum {T : Type*} [Fintype T] [DecidableEq T]
    (ts : List T) (f : T → ℕ) :
    (∑ t, firingCount ts t * f t) = (ts.map f).sum := by
  calc
    _ = ∑ t ∈ ts.toFinset, firingCount ts t * f t := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t ht hnot
      have hnotmem : t ∉ ts := by simpa using hnot
      simp [firingCount, List.count_eq_zero.mpr hnotmem]
    _ = (ts.map f).sum := by
      simpa [firingCount, nsmul_eq_mul] using
        (Finset.sum_list_map_count ts f).symm

/-- Prepending `t` adds exactly the `t` contribution to a weighted sum of
firing counts. -/
theorem firingCount_weighted_sum_cons {T : Type*} [Fintype T] [DecidableEq T]
    (t : T) (ts : List T) (f : T → ℕ) :
    (∑ u, firingCount (t :: ts) u * f u) =
      f t + ∑ u, firingCount ts u * f u := by
  simp_rw [firingCount_weighted_sum]
  simp

/-! ## State equations -/

/-- The net token effect of a transition sequence at a place. -/
def WeightedNet.sequenceEffect {P T : Type*} (net : WeightedNet P T)
    (ts : List T) (p : P) : ℤ :=
  (ts.map (net.incidence p)).sum

/-- Repeating a transition sequence `K` times multiplies its token effect by
`K`. -/
@[simp]
theorem WeightedNet.sequenceEffect_replicate {P T : Type*}
    (net : WeightedNet P T) (ts : List T) (p : P) (K : ℕ) :
    net.sequenceEffect (List.replicate K ts).flatten p =
      K * net.sequenceEffect ts p := by
  simp [WeightedNet.sequenceEffect]

private theorem firingCount_int_weighted_sum {T : Type*} [Fintype T]
    [DecidableEq T] (ts : List T) (f : T → ℤ) :
    (∑ t, (firingCount ts t : ℤ) * f t) = (ts.map f).sum := by
  calc
    _ = ∑ t ∈ ts.toFinset, (firingCount ts t : ℤ) * f t := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t ht hnot
      have hnotmem : t ∉ ts := by simpa using hnot
      simp [firingCount, List.count_eq_zero.mpr hnotmem]
    _ = (ts.map f).sum := by
      simpa [firingCount] using (Finset.sum_list_map_count ts f).symm

private theorem WeightedNet.FiresSequence.int_effect_sum {P T : Type*}
    {net : WeightedNet P T} {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) :
    ∀ p, (tgt p : ℤ) = (src p : ℤ) + net.sequenceEffect ts p := by
  induction h with
  | nil m =>
      intro p
      simp [WeightedNet.sequenceEffect]
  | cons head tail ih =>
      intro p
      have hhead := head.int_state_equation p
      have htail := ih p
      simp only [WeightedNet.sequenceEffect] at htail ⊢
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Endpoint bounds for an executable repetition of a firing sequence.

If one execution strictly increases the places in `A` and does not decrease
the places in `B`, then an executable `K`-fold repetition reaches a marking
with at least `K` tokens on `A` and at least the source value on `B`. No
condition is imposed outside `A ∪ B`. -/
theorem WeightedNet.FiresSequence.repeated_ge_on {P T : Type*}
    {net : WeightedNet P T} {src tgt reached : Marking P} {ts : List T}
    (A B : Finset P) (K : ℕ)
    (hseq : net.FiresSequence src ts tgt)
    (hrepeated :
      net.FiresSequence src (List.replicate K ts).flatten reached)
    (hA : ∀ p ∈ A, src p < tgt p)
    (hB : ∀ p ∈ B, src p ≤ tgt p) :
    (∀ p ∈ B, src p ≤ reached p) ∧
      (∀ p ∈ A, K ≤ reached p) := by
  constructor
  · intro p hp
    have hmonoAt := hB p hp
    have heffect := hseq.int_effect_sum p
    have hrepeatedEffect := hrepeated.int_effect_sum p
    rw [net.sequenceEffect_replicate] at hrepeatedEffect
    have hnonneg : 0 ≤ net.sequenceEffect ts p := by omega
    have hmul : 0 ≤ (K : ℤ) * net.sequenceEffect ts p :=
      mul_nonneg (by positivity) hnonneg
    omega
  · intro p hp
    have hgrowthAt := hA p hp
    have heffect := hseq.int_effect_sum p
    have hrepeatedEffect := hrepeated.int_effect_sum p
    rw [net.sequenceEffect_replicate] at hrepeatedEffect
    have hone : 1 ≤ net.sequenceEffect ts p := by omega
    have hK : (0 : ℤ) ≤ K := by exact_mod_cast Nat.zero_le K
    have hmul := mul_le_mul_of_nonneg_left hone hK
    omega

/-- The integer state equation for a firing sequence. At every place, the
target marking equals the source marking plus the incidence contribution of
the firing-count vector.

The transition type `T` is finite because the incidence contribution is a sum
over all transitions. -/
theorem WeightedNet.FiresSequence.int_state_equation {P T : Type*} [Fintype T]
    [DecidableEq T] {net : WeightedNet P T} {src tgt : Marking P}
    {ts : List T} (h : net.FiresSequence src ts tgt) :
    ∀ p,
      (tgt p : ℤ) = (src p : ℤ) +
        ∑ t, (firingCount ts t : ℤ) * net.incidence p t := by
  intro p
  rw [firingCount_int_weighted_sum]
  exact h.int_effect_sum p

/-- A marking `tgt` is reachable from `src` only if there is a natural-valued
firing-count vector whose incidence contribution transforms `src` into `tgt`.

The converse does not hold in general: a solution of the state equation need
not correspond to an executable firing sequence.

The proof extracts the firing sequence witnessing reachability, applies its
integer state equation, and uses its firing-count vector as the witness.
-/
theorem WeightedNet.Reachable.int_state_equation {P T : Type*} [Fintype T]
    [DecidableEq T] {net : WeightedNet P T} {src tgt : Marking P}
    (h : net.Reachable src tgt) :
    ∃ x : T → ℕ, ∀ p,
      (tgt p : ℤ) = (src p : ℤ) +
        ∑ t, (x t : ℤ) * net.incidence p t := by
  rcases h with ⟨ts, hts⟩
  have heq := hts.int_state_equation
  use firingCount ts

end PetriNet
