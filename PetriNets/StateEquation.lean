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

A firing-count vector is associated with each finite transition sequence. For a
list `ts`, the value `firingCount ts t` gives the number of occurrences of
transition `t` in `ts`.

The count vector is represented as an ordinary function `T → ℕ`. Although its
type does not imply finite support, its support is finite because it is
derived from a finite list. Finiteness assumptions on the transition type `T`
will be introduced only when needed, typically for sums over all transitions.

Equality on `T` must be decidable because the firing-count vector counts
occurrences of each transition in a list.
-/

@[expose] public section

namespace PetriNet

/-- The firing-count vector of a transition sequence. -/
def firingCount {T : Type*} [DecidableEq T] (ts : List T) : T → ℕ :=
  fun t => ts.count t

/-- The empty transition sequence has the zero firing-count vector. -/
@[simp]
theorem firingCount_nil {T : Type*} [DecidableEq T] :
    firingCount ([] : List T) = (0 : T → ℕ) := by
  funext t
  simp [firingCount]

/-- Prepending `t` to a transition sequence increments the `t` coordinate of
its firing-count vector and leaves every other coordinate unchanged. -/
@[simp]
theorem firingCount_cons {T : Type*} [DecidableEq T] (t : T) (ts : List T) :
    firingCount (t :: ts) =
      fun u => if u = t then firingCount ts u + 1 else firingCount ts u := by
  funext u
  by_cases h : u = t
  · simp [h, firingCount]
  . simp [h, firingCount, Ne.symm, List.count_cons_of_ne]

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

/-- The natural-number token-balance equation for a firing sequence.

The transition type `T` is finite so that the total tokens consumed and
produced at a place can be expressed as finite sums over all transitions.
Decidable equality is needed to compute the firing-count vector. -/
theorem WeightedNet.FiresSequence.balance {P T : Type*} [Fintype T]
    [DecidableEq T] {net : WeightedNet P T} {src tgt : Marking P}
    {ts : List T} (h : net.FiresSequence src ts tgt) :
    ∀ p,
      tgt p + ∑ t, firingCount ts t * net.pre p t =
      src p + ∑ t, firingCount ts t * net.post p t := by
  induction h with
  | nil m =>
      intro p
      simp
  | cons head tail ih =>
      intro p
      have hhead := head.balance p
      have htail := ih p
      simp_rw [firingCount_weighted_sum_cons]
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
  have hbalance :
      (tgt p : ℤ) +
          ∑ t, (firingCount ts t : ℤ) * (net.pre p t : ℤ) =
        (src p : ℤ) +
          ∑ t, (firingCount ts t : ℤ) * (net.post p t : ℤ) := by
    exact_mod_cast h.balance p
  simp only [WeightedNet.incidence]
  simp only [mul_sub]
  simp only [Finset.sum_sub_distrib]
  omega

/-- A marking `tgt` is reachable from `src` only if there is a nonnegative
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
