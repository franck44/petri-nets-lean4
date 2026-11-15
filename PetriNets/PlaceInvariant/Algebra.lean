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

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 12.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

/-- Two place invariants are equal when their coefficient functions are equal. -/
@[ext]
theorem WeightedNet.PlaceInvariant.ext {P T : Type*} [Fintype P]
    {net : WeightedNet P T} {inv₁ inv₂ : WeightedNet.PlaceInvariant net}
    (h : inv₁.coeff = inv₂.coeff) : inv₁ = inv₂ := by
  exact
    match inv₁, inv₂ with
    | ⟨coeff₁, condition₁⟩, ⟨coeff₂, condition₂⟩ => by
        cases h
        rfl

/-- Taking the coefficient function is injective on place invariants. This is
used to transport the additive commutative group structure of functions
`P → ℤ` to place invariants in `instAddCommGroup`. -/
theorem WeightedNet.PlaceInvariant.coeff_injective
    {P T : Type*} [Fintype P] {net : WeightedNet P T} :
    Function.Injective
      (fun inv : WeightedNet.PlaceInvariant net => inv.coeff) := by
  intro inv₁ inv₂ h
  exact WeightedNet.PlaceInvariant.ext h

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

/-- Subtraction of place invariants is addition of the pointwise negation. -/
instance WeightedNet.PlaceInvariant.instSub {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : Sub (WeightedNet.PlaceInvariant net) where
  sub inv₁ inv₂ := inv₁ + -inv₂

/-- Natural-number scalar multiplication is repeated addition of an
invariant. -/
instance WeightedNet.PlaceInvariant.instNatSMul {P T : Type*} [Fintype P]
    {net : WeightedNet P T} : SMul ℕ (WeightedNet.PlaceInvariant net) where
  smul := nsmulRec

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
    {net : WeightedNet P T} :
    (0 : WeightedNet.PlaceInvariant net).coeff = 0 := rfl

/-- Addition of place invariants adds their coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_add {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv₁ inv₂ : WeightedNet.PlaceInvariant net) :
    (inv₁ + inv₂).coeff = inv₁.coeff + inv₂.coeff := rfl

/-- Negation of a place invariant negates its coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_neg {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv : WeightedNet.PlaceInvariant net) :
    (-inv).coeff = -inv.coeff := rfl

/-- Subtraction of place invariants subtracts their coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_sub {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv₁ inv₂ : WeightedNet.PlaceInvariant net) :
    (inv₁ - inv₂).coeff = inv₁.coeff - inv₂.coeff := by
  change (inv₁ - inv₂).coeff = (inv₁ + -inv₂).coeff
  change inv₁.coeff - inv₂.coeff = inv₁.coeff + -inv₂.coeff
  rfl

/-- Natural-number scalar multiplication acts pointwise on coefficients. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_nsmul {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (n : ℕ) (inv : WeightedNet.PlaceInvariant net) :
    (n • inv).coeff = n • inv.coeff := by
    induction n with
     | zero =>
        rw [show (0 : ℕ) • inv = 0 from rfl]
        simp
     | succ n ih =>
        rw [show ((n + 1) • inv) = n • inv + inv from rfl]
        rw [WeightedNet.PlaceInvariant.coeff_add]
        rw [ih]
        rw [succ_nsmul]

/-- Integer scalar multiplication multiplies the coefficients pointwise. -/
@[simp]
theorem WeightedNet.PlaceInvariant.coeff_smul {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (k : ℤ) (inv : WeightedNet.PlaceInvariant net) :
    (k • inv).coeff = k • inv.coeff := by
      funext p
      change k * inv.coeff p = (k • inv.coeff) p
      simp

/-- Place invariants of a net form an additive commutative group under
their pointwise operations. -/
instance WeightedNet.PlaceInvariant.instAddCommGroup
    {P T : Type*} [Fintype P] {net : WeightedNet P T} :
    AddCommGroup (WeightedNet.PlaceInvariant net) :=
  Function.Injective.addCommGroup
    (fun inv : WeightedNet.PlaceInvariant net => inv.coeff)
    WeightedNet.PlaceInvariant.coeff_injective
    WeightedNet.PlaceInvariant.coeff_zero
    WeightedNet.PlaceInvariant.coeff_add
    WeightedNet.PlaceInvariant.coeff_neg
    WeightedNet.PlaceInvariant.coeff_sub
    -- `addCommGroup` expects the invariant before the scalar, whereas the
    -- coefficient lemmas take the scalar first.
    (fun inv n => WeightedNet.PlaceInvariant.coeff_nsmul n inv)
    (fun inv k => WeightedNet.PlaceInvariant.coeff_smul k inv)

end PetriNet
