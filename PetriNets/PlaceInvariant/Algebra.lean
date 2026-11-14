/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant

/-!
# Algebra of place invariants

Place invariants of a weighted P/T net are closed under zero, pointwise addition,
negation, and multiplication by an integer.

These closure properties are registered as Lean typeclass instances. This
allows the standard notation `0`, `+`, unary `-`, and `•` to be used for place
invariants, with the appropriate operations found automatically by typeclass
inference.

Together, these closure properties are the first step towards viewing the
place invariants as the integer kernel of the net's incidence matrix.
-/

@[expose] public section

namespace PetriNet

/-- The place invariant whose coefficient is zero at every place. -/
instance WeightedNet.PlaceInvariant.instZero {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : Zero (WeightedNet.PlaceInvariant net) where
  zero :=
    { coeff := 0
      condition := by simp }

/-- The pointwise sum of two place invariants. -/
instance WeightedNet.PlaceInvariant.instAdd {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : Add (WeightedNet.PlaceInvariant net) where
  add inv₁ inv₂ :=
    { coeff := inv₁.coeff + inv₂.coeff
      condition := by
        intro t
        simp only [Pi.add_apply]
        simp only [add_mul, Finset.sum_add_distrib]
        simp only [inv₁.condition t, inv₂.condition t, add_zero] }

/-- The pointwise negation of a place invariant. -/
instance WeightedNet.PlaceInvariant.instNeg {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : Neg (WeightedNet.PlaceInvariant net) where
  neg inv :=
    { coeff := -inv.coeff
      condition := by
        intro t
        simp only [Pi.neg_apply]
        simp only [neg_mul, Finset.sum_neg_distrib]
        simp only [inv.condition t, neg_zero] }

/-- Multiplication of a place invariant by an integer. -/
instance WeightedNet.PlaceInvariant.instSMul {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : SMul ℤ (WeightedNet.PlaceInvariant net) where
  smul k inv :=
    { coeff := fun p => k * inv.coeff p
      condition := by
        intro t
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, inv.condition t, mul_zero] }

/-- The zero invariant has coefficient zero at every place. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_zero {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (p : P) :
    (0 : WeightedNet.PlaceInvariant net).coeff p = 0 := rfl

/-- Addition of place invariants adds their coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_add {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv₁ inv₂ : WeightedNet.PlaceInvariant net)
    (p : P) : (inv₁ + inv₂).coeff p = inv₁.coeff p + inv₂.coeff p := rfl

/-- Negation of a place invariant negates its coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_neg {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv : WeightedNet.PlaceInvariant net) (p : P) :
    (-inv).coeff p = -inv.coeff p := rfl

/-- Integer scalar multiplication multiplies the coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_smul {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (k : ℤ) (inv : WeightedNet.PlaceInvariant net)
    (p : P) : (k • inv).coeff p = k * inv.coeff p := rfl

end PetriNet
