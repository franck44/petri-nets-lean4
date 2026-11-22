/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Incidence
public import PetriNets.Reachability

/-!
# Place invariants of weighted P/T nets

Provides place invariants for weighted P/T nets, their values at markings,
preservation under firing and reachability, and the resulting non reachability
of markings not satisfying an invariant.

A place invariant consists of a coefficient function `y : P → ℤ` and a proof
that every transition preserves its value. With our
place-by-transition incidence matrix `C`, this structural condition is the
equation `yᵀ C = 0` that corresponds to the preservation of the invariant by every transition.

The property of being a place invariant depends on the net, but not on an initial marking.

Once an initial marking `m₀` is fixed, a place invariant induces the marking
predicate

```text
inv.value m = inv.value m₀.
```

This predicate holds at `m₀` and is preserved by every firing, so it holds
at every marking reachable from `m₀`.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, especially Chapter 11,
  pp. 123–129. DOI: 10.1007/978-3-642-33278-4.
* T. Murata, "Petri Nets: Properties, Analysis and Applications",
  *Proceedings of the IEEE* 77(4), 1989, Section V-A.
  DOI: 10.1109/5.24143.
-/

@[expose] public section

namespace PetriNet

/-- A place invariant of `net` consists of a coefficient function on places
together with a proof that every transition has zero weighted incidence
contribution. Thus, constructing a value of type `PlaceInvariant net` requires
both the function `coeff` and a proof of `condition`; the type guarantees that
every place invariant satisfies the invariant condition.

This is a structural property of `net` and does not depend on an initial
marking. -/
structure WeightedNet.PlaceInvariant {P T : Type*} [Fintype P]
    (net : WeightedNet P T) where
  coeff : P → ℤ
  condition : ∀ t, ∑ p, coeff p * net.incidence p t = 0

/-- For a place invariant `inv`, let `y = inv.coeff`. Viewing `y` as a row
vector and `net.incidence` as the incidence matrix `C`, we have `y · C = 0`.

This theorem packages the componentwise condition stored in `inv`; it does not
require the transition type to be finite. -/
theorem WeightedNet.PlaceInvariant.coeff_vecMul_incidence_eq_zero
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) :
    Matrix.vecMul inv.coeff net.incidence = 0 := by
  funext t
  exact inv.condition t

/-- The weighted value of a place invariant at a marking. This is defined for
every marking, whether reachable or not. -/
def WeightedNet.PlaceInvariant.value {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv : WeightedNet.PlaceInvariant net)
    (m : Marking P) : ℤ :=
  ∑ p, inv.coeff p * (m p : ℤ)

/-- For each transition, a place invariant assigns the same total weight to
the tokens produced and the tokens consumed. This is the invariant condition
written in terms of `post` and `pre`, rather than the incidence matrix. -/
theorem WeightedNet.PlaceInvariant.post_eq_pre
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) (t : T) :
    ∑ p, inv.coeff p * (net.post p t : ℤ) =
      ∑ p, inv.coeff p * (net.pre p t : ℤ) := by
  have h := inv.condition t
  simp_rw [WeightedNet.incidence, mul_sub] at h
  rw [Finset.sum_sub_distrib] at h
  exact sub_eq_zero.mp h

/-- The value of a place invariant is preserved after the firing of any
transition. -/
theorem WeightedNet.PlaceInvariant.value_eq_of_fires {P T : Type*} [Fintype P]
    {net : WeightedNet P T} (inv : WeightedNet.PlaceInvariant net)
    {m m' : Marking P} {t : T} (h : net.Fires m t m') :
    inv.value m' = inv.value m := by
  simp only [WeightedNet.PlaceInvariant.value]
  simp_rw [h.int_state_equation, mul_add]
  rw [Finset.sum_add_distrib, inv.condition t, add_zero]

/-- The value of a place invariant is preserved after firing any transition
sequence.
This generalises the previous theorem to sequences of transitions. -/
theorem WeightedNet.PlaceInvariant.value_eq_of_firesSequence
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) : inv.value tgt = inv.value src := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
      exact ih.trans (inv.value_eq_of_fires head)

/-- If `tgt` is reachable from `src`, every place invariant has the same value
at both markings. -/
theorem WeightedNet.PlaceInvariant.value_eq_of_reachable
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) {src tgt : Marking P}
    (h : net.Reachable src tgt) : inv.value tgt = inv.value src := by
  rcases h with ⟨ts, hts⟩
  exact inv.value_eq_of_firesSequence hts

/-- The contrapositive of `value_eq_of_reachable`: if a place invariant has
different values at `src` and `tgt`, then `tgt` is not reachable from `src`.
This is the standard use of place invariants as a necessary reachability
condition. -/
theorem WeightedNet.PlaceInvariant.not_reachable_of_value_ne
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    (inv : WeightedNet.PlaceInvariant net) {src tgt : Marking P}
    (h : inv.value tgt ≠ inv.value src) : ¬net.Reachable src tgt := by
  intro hreach
  apply h
  exact inv.value_eq_of_reachable hreach

end PetriNet
