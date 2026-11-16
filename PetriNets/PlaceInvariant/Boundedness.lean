/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant

/-!
# Boundedness from place invariants

A place invariant is positive for a place `p` when its coefficient at `p` is
strictly positive and all its coefficients are nonnegative. Since the
invariant value is preserved along reachability, such an invariant gives an
upper bound on the number of tokens at `p`.

Boundedness is relative to an initial marking: a place is bounded from `m₀`
when one natural-number bound applies to all markings reachable from `m₀`. A
net is bounded from `m₀` when one bound applies to every place in every
marking reachable from `m₀`.

If an invariant is positive for a place, that place is bounded for every
choice of initial marking. The bound itself may depend on the initial marking,
through the invariant value at that marking.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Section 11.4, pp. 127–129.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

/-- `inv` is positive for `p` when the coefficient at `p` is strictly positive
and every coefficient is nonnegative. This is Reisig's place-relative notion
of a positive invariant. -/
def WeightedNet.PlaceInvariant.PositiveAt {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv : WeightedNet.PlaceInvariant net)
    (p : P) : Prop :=
  0 < inv.coeff p ∧ 0 ≤ inv.coeff

/-- Place `p` is bounded from initial marking `m₀` when there exists a natural
number `B` such that every marking `m` reachable from `m₀` contains at most
`B` tokens in `p`, that is, `m p ≤ B`. The bound may depend on `m₀` and `p`,
but not on the reachable marking `m`. -/
def WeightedNet.PlaceBoundedFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (p : P) : Prop :=
  ∃ B : ℕ, ∀ m, net.Reachable m₀ m → m p ≤ B

/-- A net is bounded from initial marking `m₀` when there is one natural
number `B` such that every place contains at most `B` tokens in every marking
reachable from `m₀`. -/
def WeightedNet.BoundedFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) : Prop :=
  ∃ B : ℕ, ∀ m, net.Reachable m₀ m → ∀ p, m p ≤ B

/-- An invariant with nonnegative coefficients has a nonnegative value at
every marking. -/
theorem WeightedNet.PlaceInvariant.value_nonneg_of_coeff_nonneg
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net)
    (hcoeff : 0 ≤ inv.coeff) (m : Marking P) :
    0 ≤ inv.value m := by
  apply Finset.sum_nonneg
  intro q _
  exact mul_nonneg (hcoeff q) (Int.natCast_nonneg (m q))

/-- If all invariant coefficients are nonnegative, the weighted token count
at one place is at most the complete invariant value. The remaining terms in
the sum are nonnegative. -/
theorem WeightedNet.PlaceInvariant.weighted_token_le_value
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net)
    (hcoeff : 0 ≤ inv.coeff) (m : Marking P) (p : P) :
    inv.coeff p * (m p : ℤ) ≤ inv.value m := by
  rw [WeightedNet.PlaceInvariant.value]
  refine Finset.single_le_sum
    (f := fun q => inv.coeff q * (m q : ℤ)) ?_ (Finset.mem_univ p)
  intro q _
  exact mul_nonneg (hcoeff q) (Int.natCast_nonneg (m q))

/-- Let `inv` be positive for `p`, and let `m` be reachable from `m₀`. The
token count at `p` is bounded by the preserved invariant value divided by the
coefficient of `p`:

`m p ≤ Inv(m₀) / inv.coeff p`.

The integer invariant value and coefficient are converted to natural numbers;
their nonnegativity makes these conversions exact. -/
theorem WeightedNet.PlaceInvariant.tokens_le_value_div_of_positiveAt
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) {m₀ m : Marking P} {p : P}
    (hpos : inv.PositiveAt p) (hreach : net.Reachable m₀ m) :
    m p ≤ (inv.value m₀).toNat / (inv.coeff p).toNat := by
  have hvalue_nonneg := inv.value_nonneg_of_coeff_nonneg hpos.2 m₀
  have hk_nonneg : 0 ≤ inv.coeff p := le_of_lt hpos.1
  have hk_pos : 0 < (inv.coeff p).toNat := Int.pos_iff_toNat_pos.mp hpos.1
  have hweighted : inv.coeff p * (m p : ℤ) ≤ inv.value m₀ := by
    calc
      inv.coeff p * (m p : ℤ) ≤ inv.value m :=
        inv.weighted_token_le_value hpos.2 m p
      _ = inv.value m₀ := inv.value_eq_of_reachable hreach
  have hweighted_nat : (inv.coeff p).toNat * m p ≤ (inv.value m₀).toNat := by
    have hweighted_cast :
        (((inv.coeff p).toNat * m p : ℕ) : ℤ) ≤
          ((inv.value m₀).toNat : ℤ) := by
      simpa [Int.natCast_mul, Int.ofNat_toNat, hk_nonneg, hvalue_nonneg] using
        hweighted
    exact_mod_cast hweighted_cast
  apply (Nat.le_div_iff_mul_le hk_pos).mpr
  simpa [Nat.mul_comm] using hweighted_nat

/-- A place `p` with a positive invariant is bounded from every initial
marking `m₀`, with bound `Inv(m₀) / inv.coeff p`. The invariant and its
positivity do not depend on `m₀`, although the value of the bound may. -/
theorem WeightedNet.PlaceInvariant.placeBoundedFrom_of_positiveAt
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) {p : P}
    (hpos : inv.PositiveAt p) (m₀ : Marking P) :
    net.PlaceBoundedFrom m₀ p := by
  use (inv.value m₀).toNat / (inv.coeff p).toNat
  intro m hreach
  exact inv.tokens_le_value_div_of_positiveAt hpos hreach

/-- If every place has a place invariant positive for it, then the net is
bounded from every initial marking. Different places may use different
invariants. -/
theorem WeightedNet.boundedFrom_of_positiveAt_each
    {P T : Type*} [Fintype P] (net : WeightedNet P T)
    (hpos : ∀ p, ∃ inv : WeightedNet.PlaceInvariant net, inv.PositiveAt p)
    (m₀ : Marking P) : net.BoundedFrom m₀ := by
  classical
  choose inv hinv using hpos
  let bound := fun p => ((inv p).value m₀).toNat / ((inv p).coeff p).toNat
  obtain ⟨B, hB⟩ := Finite.bddAbove_range bound
  use B
  intro m hreach p
  exact ((inv p).tokens_le_value_div_of_positiveAt (hinv p) hreach).trans
    (hB ⟨p, rfl⟩)

end PetriNet
