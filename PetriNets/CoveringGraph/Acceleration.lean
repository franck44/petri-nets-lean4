/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability
public import PetriNets.Monotonicity

/-!
# Acceleration of ω-markings

Provides acceleration of ω-markings and proves when acceleration preserves
coverability in a weighted P/T net.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace OmegaMarking

/-! ## ω-places -/

/-- The finite set of places at which a given ω-marking has value `ω`.

For example, if a three-place marking has values

```text
m = (3, ω, ω),
```

then `omegaPlaces m` is the set containing the second and third places. The
function does not construct or enumerate ω-markings: it takes one marking and
records precisely which of its components are `ω`.

The result is a `Finset P` because the place type `P` is finite. It is obtained
by filtering the finite set of all places. -/
noncomputable def omegaPlaces {P : Type*} [Fintype P]
    (m : OmegaMarking P) : Finset P := by
  classical
  exact Finset.univ.filter fun p => m p = ⊤

/-- A place belongs to `omegaPlaces m` exactly when its value in `m` is `ω`.

This theorem is the membership interface for `omegaPlaces`: it allows proofs
to move between the finite-set statement `p ∈ omegaPlaces m` and the marking
equation `m p = ⊤`. -/
@[simp]
theorem mem_omegaPlaces {P : Type*} [Fintype P]
    {m : OmegaMarking P} {p : P} :
    p ∈ omegaPlaces m ↔ m p = ⊤ := by
  classical
  simp [omegaPlaces]

/-! ## Acceleration -/

/-- `accelerate A m` is the ω-marking obtained from `m` by replacing the
values at the chosen set `A` of places by `ω`. At every place outside `A`, it
retains the value of `m`. The set `A` records exactly which places are
accelerated. -/
noncomputable def accelerate {P : Type*} (A : Set P)
    (m : OmegaMarking P) : OmegaMarking P := by
  classical
  exact fun p => if p ∈ A then ⊤ else m p

/-- Executable acceleration for a finite set of places. -/
def accelerateFinset {P : Type*} [DecidableEq P] (A : Finset P)
    (m : OmegaMarking P) : OmegaMarking P :=
  fun p => if p ∈ A then ⊤ else m p

/-- A place selected for acceleration has value `ω`. -/
@[simp]
theorem accelerate_apply_of_mem {P : Type*} {A : Set P}
    {m : OmegaMarking P} {p : P} (hp : p ∈ A) :
    accelerate A m p = ⊤ := by
  classical
  simp [accelerate, hp]

/-- A place not selected for acceleration retains its original value. -/
@[simp]
theorem accelerate_apply_of_not_mem {P : Type*} {A : Set P}
    {m : OmegaMarking P} {p : P} (hp : p ∉ A) :
    accelerate A m p = m p := by
  classical
  simp [accelerate, hp]

end OmegaMarking

/-! ## Coverability under acceleration -/

/-- Suppose `tgt` is ω-coverable from `m₀` and an ω-firing sequence
`ts` takes `src` to `tgt` with `src ≤ tgt` and `src p < tgt p`.
Then replacing `tgt p` by ω preserves ω-coverability from `m₀`.

For any finite token demand at `p`, take enough repetitions of a concrete
replay of `ts` to meet it. The required starting marking lies below `tgt`,
so some reachable marking covers it. Monotonicity lets the repetitions
fire from that reachable marking, meeting the demand at `p` while still
covering the chosen concretisation of `tgt` at the other places. -/
theorem WeightedNet.omegaCoverableFrom_accelerate_of_growsAt
    {P T : Type*} [Fintype P] {net : WeightedNet P T}
    {m₀ : Marking P} {src tgt : OmegaMarking P} {ts : List T} {p : P}
    (htgt : net.OmegaCoverableFrom m₀ tgt)
    (hexec : net.omegaMarkingLTS.MTr src ts tgt)
    (hgrowth : src <[p] tgt) :
    net.OmegaCoverableFrom m₀ (OmegaMarking.accelerate ({p} : Set P) tgt) := by
  classical
  apply net.omegaCoverableFrom_iff_forall_kCoverableFrom.mpr
  intro K
  obtain ⟨base, reached, hbase, hrepeat, hgain, hcover⟩ :=
    net.exists_concrete_replay_repeated_growsAt hexec hgrowth.1 hgrowth.2 (K + 1) K
  obtain ⟨m, hm, hbase⟩ := htgt base (hbase.trans hgrowth.1)
  obtain ⟨m', hm', hend⟩ := (show net.Reachable _ _ from ⟨_, hrepeat⟩).mono hbase
  refine ⟨m', hm.trans hm', fun q => ?_⟩
  by_cases hq : q = p
  · subst q
    have hp : K ≤ reached p := by omega
    simpa [OmegaMarking.accelerate] using hp.trans (hend p)
  · simpa [OmegaMarking.concretise, OmegaMarking.accelerate, hq] using
      (hcover (Nat.succ_pos K) q).trans (hend q)

/-- Suppose `tgt` is ω-coverable from `m₀`. For each `p ∈ A`, suppose
there is an ω-firing sequence ending at `tgt` from a source at most `tgt`
and strictly smaller at `p`. Then setting all places in the finite set
`A` to ω preserves ω-coverability from `m₀`.

Accelerate one place at a time. For the next place `p`, set the already
accelerated places to ω at both ends of its witness execution. This gives
an execution ending at the current target and leaves strict growth at
`p` intact. The single-place theorem then accelerates `p`. -/
theorem WeightedNet.omegaCoverableFrom_accelerateFinset_of_growsAt
    {P T : Type*} [Fintype P] [DecidableEq P] {net : WeightedNet P T}
    {m₀ : Marking P} {tgt : OmegaMarking P} (A : Finset P)
    (htgt : net.OmegaCoverableFrom m₀ tgt)
    (hwitness : ∀ p ∈ A, ∃ src ts,
      net.omegaMarkingLTS.MTr src ts tgt ∧ src <[p] tgt) :
    net.OmegaCoverableFrom m₀ (OmegaMarking.accelerateFinset A tgt) := by
  classical
  induction A using Finset.induction with
  | empty =>
      have heq : OmegaMarking.accelerateFinset ∅ tgt = tgt := by
        funext q
        simp [OmegaMarking.accelerateFinset]
      rw [heq]
      exact htgt
  | @insert p A hp ih =>
      have hcover := ih (fun q hq => hwitness q (Finset.mem_insert_of_mem hq))
      obtain ⟨src, ts, hexec, hgrowth⟩ := hwitness p (Finset.mem_insert_self p A)
      let d : OmegaMarking P := fun q => if q ∈ A then ⊤ else 0
      have ht : tgt + d = OmegaMarking.accelerateFinset A tgt := by
        funext q
        by_cases hq : q ∈ A <;> simp [d, OmegaMarking.accelerateFinset, hq]
      have hstep := net.omegaCoverableFrom_accelerate_of_growsAt
        (ht.symm ▸ hcover) (net.omegaMTr_add hexec d)
        (show (src + d) <[p] (tgt + d) from
          ⟨add_le_add_left hgrowth.1 d, by simpa [d, hp] using hgrowth.2⟩)
      rw [ht] at hstep
      convert hstep using 1
      funext q
      by_cases hq : q = p <;> simp [OmegaMarking.accelerateFinset,
        OmegaMarking.accelerate, hq]

end PetriNet
