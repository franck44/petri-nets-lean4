/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant.Synthesis
public import Mathlib.Data.Fin.VecNotation

/-!
# Example: synthesising a place invariant

Provides a concrete use of `placeInvariantEquivKer` to synthesise a place
invariant for a three-place, two-transition net and characterises all place
invariants of that net.

```text
(p0) ──▶ [t0] ──▶ (p1) ──▶ [t1] ──▶ (p2)
```

The coefficient vector `(1, 1, 1)` belongs to the kernel of
`placeInvariantMap`. Applying the reverse direction of the linear equivalence
constructs the place invariant expressing conservation of the total number of
tokens.
-/

@[expose] public section

namespace PetriNet.ThreePlaceNet

/-! ## The three-place net -/

/-- The three places of the net, p0, p1, and p2. -/
abbrev P := Fin 3

/-- The two transitions of the net. -/
abbrev T := Fin 2

/-- The first, second, and third places. -/
def p0 : P := 0
def p1 : P := 1
def p2 : P := 2

/-- The first and second transitions. -/
def t0 : T := 0
def t1 : T := 1

/-- The weighted P/T net in which `t0` moves a token from `p0` to `p1` and
`t1` moves a token from `p1` to `p2`. -/
def net : WeightedNet P T where
  pre p t :=
    match p.val, t.val with
    | 0, 0 => 1
    | 1, 1 => 1
    | _, _ => 0
  post p t :=
    match p.val, t.val with
    | 1, 0 => 1
    | 2, 1 => 1
    | _, _ => 0

/-! ## Synthesising the token-count invariant -/

/-- The candidate coefficient vector that counts every token with weight one. -/
def tokenCountCoeffs : P → ℤ := ![1, 1, 1]

/-- The token-count coefficient vector belongs to the kernel of
`placeInvariantMap`. -/
theorem tokenCountCoeffs_mem_ker :
    tokenCountCoeffs ∈ LinearMap.ker net.placeInvariantMap := by
  rw [LinearMap.mem_ker]
  funext t
  fin_cases t <;>
    simp [WeightedNet.placeInvariantMap, WeightedNet.incidence, Matrix.vecMul,
      dotProduct, Fin.sum_univ_three, net, tokenCountCoeffs]

/-- The element of `placeInvariantMap`'s kernel represented by `tokenCountCoeffs`. -/
def tokenCountKernelElement : LinearMap.ker net.placeInvariantMap :=
  ⟨tokenCountCoeffs, tokenCountCoeffs_mem_ker⟩

/-- The token-count place invariant synthesised from the kernel element. -/
def tokenCountInvariant : WeightedNet.PlaceInvariant net :=
  (net.placeInvariantEquivKer).symm tokenCountKernelElement

/-- Synthesis preserves the coefficient vector used to construct the
invariant. -/
@[simp]
theorem tokenCountInvariant_coeff :
    tokenCountInvariant.coeff = tokenCountCoeffs := by
  simp [tokenCountInvariant, tokenCountKernelElement]

/-! ## Characterising all invariants -/

/-- If `inv` is a place invariant of this net, then its coefficient vector is
of the form `(k, k, k)` for some integer `k`. -/
theorem coeff_eq_of_invariant (inv : WeightedNet.PlaceInvariant net) :
    ∃ k : ℤ, inv.coeff = ![k, k, k] := by
  have h0 : -inv.coeff p0 + inv.coeff p1 = 0 := by
    simpa [Fin.sum_univ_three, WeightedNet.incidence, net, p0, p1, t0] using
      inv.condition t0
  have h1 : -inv.coeff p1 + inv.coeff p2 = 0 := by
    simpa [Fin.sum_univ_three, WeightedNet.incidence, net, p1, p2, t1] using
      inv.condition t1
  have h01 : inv.coeff p0 = inv.coeff p1 := by omega
  have h12 : inv.coeff p1 = inv.coeff p2 := by omega
  have h02 : inv.coeff p0 = inv.coeff p2 := by omega
  use inv.coeff p0
  funext p
  fin_cases p
  · simp [p0]
  · simpa [p0, p1] using h01.symm
  · simpa [p0, p2] using h02.symm

/-- A coefficient function whose values at the three places are equal defines
a place invariant of this net. -/
def invariantOfCoeffsEq (y : P → ℤ)
    (h01 : y p0 = y p1) (h12 : y p1 = y p2) :
    WeightedNet.PlaceInvariant net where
  coeff := y
  condition := by
    have h01' : y 0 = y 1 := by simpa [p0, p1] using h01
    have h12' : y 1 = y 2 := by simpa [p1, p2] using h12
    intro t
    fin_cases t <;>
      simp [Fin.sum_univ_three, WeightedNet.incidence, net] <;>
      omega

/-- Every place invariant `inv` of this net is of the form
`k • tokenCountInvariant` for some integer `k`. More precisely,
`k = inv.coeff p0`.
 -/
theorem eq_smul_tokenCountInvariant (inv : WeightedNet.PlaceInvariant net) :
    inv = inv.coeff p0 • tokenCountInvariant := by
  obtain ⟨k, hcoeff⟩ := coeff_eq_of_invariant inv
  have hk : k = inv.coeff p0 := by
    have hp0 := congrFun hcoeff p0
    simpa [p0] using hp0.symm
  subst k
  apply WeightedNet.PlaceInvariant.ext
  rw [WeightedNet.PlaceInvariant.coeff_smul, tokenCountInvariant_coeff]
  funext p
  rw [hcoeff]
  fin_cases p <;> simp [tokenCountCoeffs, p0]

end PetriNet.ThreePlaceNet
