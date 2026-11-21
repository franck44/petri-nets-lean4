/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller
import PetriNets.Monotonicity
import PetriNets.StateEquation

/-!
# Soundness of the Karp–Miller construction

This module proves that the ω-markings stored in a Karp–Miller tree do not
introduce false coverability claims. An ω-marking is sound from an initial
marking when every ordinary marking below it is covered by some reachable
marking.

The quantifiers are important: each finite marking may have a different
reachable witness. In particular, an ω component represents arbitrarily large
reachable token counts, not one ordinary marking containing ω tokens.

The proof will establish soundness first for the initial marking, then show
that it is preserved by ordinary successors and by acceleration.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*} {net : WeightedNet P T}

/-- At a place which is finite after a DFS step, the target component is the
raw firing result. Acceleration can only replace a component by `ω`, so it
cannot have affected this place. -/
private theorem marking_apply_eq_succMarking_of_tr_of_ne_top
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {t : T} {p : P}
    (htr : (dfsLTS net).Tr src t tgt) (hp : tgt.marking p ≠ ⊤) :
    tgt.marking p = succMarking net src.marking t p := by
  obtain ⟨_, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  exact succBranch_marking_apply_eq_succMarking_of_ne_top src t hp

/-- A Karp–Miller DFS edge whose target contains no `ω` is a
concrete firing between the corresponding markings.

The set of `ω`-places can only grow along a DFS edge, so the source is finite
whenever the target is finite. Since the target has no `ω`, the step cannot
have introduced an accelerated place. Its source and target therefore embed
the concrete markings `src.marking.toNat` and `tgt.marking.toNat`, and the
underlying ω-firing reflects to an ordinary firing. -/
theorem fires_of_dfsLTS_tr_of_omegaPlaces_eq_empty
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt)
    (hsrcFinite : OmegaMarking.omegaPlaces src.marking = ∅)
    (htgtFinite : OmegaMarking.omegaPlaces tgt.marking = ∅) :
    net.Fires (src.marking.toNat hsrcFinite) t
      (tgt.marking.toNat htgtFinite) := by
  obtain ⟨_, henabled, htarget⟩ := mem_dfsSuccessors_iff.mp htr
  have hmarking : tgt.marking = succMarking net src.marking t := by
    rw [← htarget]
    apply succBranch_marking_eq_succMarking_of_omegaPlaces_eq
    rw [hsrcFinite, htarget, htgtFinite]
  have homega : net.OmegaFires src.marking t tgt.marking := by
    exact ⟨henabled, fun p => congrFun hmarking p⟩
  apply (net.fires_iff_omegaFires_toOmega
    (src.marking.toNat hsrcFinite) (tgt.marking.toNat htgtFinite) t).mpr
  simpa [OmegaMarking.toOmega_toNat_eq_self hsrcFinite,
    OmegaMarking.toOmega_toNat_eq_self htgtFinite] using homega

/-- A finite DFS execution whose endpoints contain no `ω` is a concrete
firing sequence between the corresponding ordinary markings.

Although only endpoint finiteness appears in the statement, every
intermediate branch is finite as well: the set of `ω`-places can only grow
along a DFS execution, and the final set is empty. The proof therefore applies
`fires_of_dfsLTS_tr_of_omegaPlaces_eq_empty` to the first edge and proceeds
inductively along the remaining execution. -/
theorem firesSequence_of_dfsLTS_mTr_of_omegaPlaces_eq_empty
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {ts : List T}
    (hexec : (dfsLTS net).MTr src ts tgt)
    (hsrcFinite : OmegaMarking.omegaPlaces src.marking = ∅)
    (htgtFinite : OmegaMarking.omegaPlaces tgt.marking = ∅) :
    net.FiresSequence (src.marking.toNat hsrcFinite) ts
      (tgt.marking.toNat htgtFinite) := by
  induction hexec with
  | refl =>
      exact WeightedNet.FiresSequence.nil _
  | @stepL src t mid ts tgt htr htail ih =>
      have hmidFinite : OmegaMarking.omegaPlaces mid.marking = ∅ := by
        apply Finset.subset_empty.mp
        simpa [htgtFinite] using omegaPlaces_mono_of_mTr htail
      exact WeightedNet.FiresSequence.cons
        (fires_of_dfsLTS_tr_of_omegaPlaces_eq_empty
          htr hsrcFinite hmidFinite)
        (ih hmidFinite htgtFinite)

/-- Firing from an ω-marking with no `ω`-places produces a successor with
no `ω`-places.

The function `succMarking` only applies the ordinary Petri-net update

```text
src(p) - pre(p, t) + post(p, t)
```

The proof is that subtraction and addition of finite values in `ℕ∞` remain finite. -/
private theorem omegaPlaces_succMarking_eq_empty_of_src_eq_empty
    [Fintype P] {src : OmegaMarking P} {t : T}
    (hfinite : OmegaMarking.omegaPlaces src = ∅) :
    OmegaMarking.omegaPlaces (succMarking net src t) = ∅ := by
  apply Finset.subset_empty.mp
  intro p hp
  rw [OmegaMarking.mem_omegaPlaces] at hp
  have hsrc : src p ≠ ⊤ := by
    intro htop
    have : p ∈ OmegaMarking.omegaPlaces src :=
      OmegaMarking.mem_omegaPlaces.mpr htop
    rw [hfinite] at this
    simp at this
  rw [succMarking, ← ENat.natCast_toNat hsrc] at hp
  simp at hp

/-- Concretise one enabled firing from an ω-marking with no `ω`-places.

If `src` is finite and enables `t`, its ordinary representation enables the
same transition. The standard firing rule therefore provides an ordinary
target whose embedding is exactly the ω-firing result:

```text
src.toNat ──t──▶ tgt
    │              │
 toOmega        toOmega
    │              │
    ▼              ▼
   src ──t──▶ succMarking net src t
```
-/
theorem exists_fires_to_succMarking_of_omegaPlaces_eq_empty
    [Fintype P] {src : OmegaMarking P} {t : T}
    (hfinite : OmegaMarking.omegaPlaces src = ∅)
    (henabled : net.OmegaEnabled src t) :
    ∃ tgt : Marking P,
      net.Fires (src.toNat hfinite) t tgt ∧
      tgt.toOmega = succMarking net src t := by
  have hsrcEmbed : (src.toNat hfinite).toOmega = src :=
    OmegaMarking.toOmega_toNat_eq_self hfinite
  have henabledNat : net.Enabled (src.toNat hfinite) t := by
    apply (net.enabled_iff_omegaEnabled_toOmega _ t).mpr
    rwa [hsrcEmbed]
  obtain ⟨tgt, hfires⟩ :=
    (net.enabled_iff_exists_fires _ t).mp henabledNat
  refine ⟨tgt, hfires, ?_⟩
  have homega := (net.fires_iff_omegaFires_toOmega _ _ t).mp hfires
  rw [hsrcEmbed] at homega
  funext p
  exact homega.2 p

/-- Soundness of a DFS step which introduces no new `ω`-place.

When the source and target have the same set of `ω`-places, the target is
exactly the ordinary omega firing successor. Its soundness therefore follows
from `WeightedNet.omegaCoverableFrom_of_omegaFires`.

More explicitly, take an arbitrary concrete marking `demand` below
`tgt.marking`. We compute the least marking `srcDemand` such that firing `t`
from `srcDemand` covers `demand`. Its embedding satisfies
`srcDemand.toOmega ≤ src.marking`, so `hsound` makes `srcDemand` coverable
from `m₀`. Monotonicity of firing then makes `demand` coverable from `m₀`. -/
theorem omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_eq
    [FinEnum P] [FinEnum T] {m₀ : Marking P}
    {src tgt : Branch P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ src.marking)
    (htr : (dfsLTS net).Tr src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  rw [marking_eq_succMarking_of_tr_of_omegaPlaces_eq htr homega]
  apply net.omegaCoverableFrom_of_omegaFires hsound
  exact ⟨(mem_dfsSuccessors_iff.mp htr).2.1, fun _ => rfl⟩

/-- A newly introduced `ω`-place has a growth witness in the source history.

If a DFS step changes `p` from finite to `ω`, then `p` was selected by the
acceleration rule. Consequently, some marking `a` in `src.history` is below
the raw firing successor and is strictly smaller there at `p`:

```text
a ∈ src.history       a ≤ raw       a(p) < raw(p)

src ──t──▶ raw ──accelerate p──▶ tgt
```
-/
theorem exists_history_growth_witness_of_new_omegaPlace
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {t : T} {p : P}
    (htr : (dfsLTS net).Tr src t tgt)
    (hpSrc : p ∉ OmegaMarking.omegaPlaces src.marking)
    (hpTgt : p ∈ OmegaMarking.omegaPlaces tgt.marking) :
    ∃ a ∈ src.history,
      a ≤ succMarking net src.marking t ∧
      a p < succMarking net src.marking t p := by
  obtain ⟨_, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  have hpAccelerated :=
    mem_acceleratedPlaces_of_mem_omegaPlaces_succBranch
      (net := net) src t hpSrc hpTgt
  simpa [Branch.acceleratedPlaces] using hpAccelerated

/-- A newly introduced `ω`-place has a growth witness realised by an earlier
branch on the DFS prefix.

The historical marking supplied by
`exists_history_growth_witness_of_new_omegaPlace` is either `src.marking`
itself or the marking of an earlier branch `ancestor`. In both cases the
prefix can be split into a path reaching `ancestor` and a segment from
`ancestor` to `src`:

```text
Branch.initial m₀ ──before──▶ ancestor ──segment──▶ src ──t──▶ raw
                                │                              │
                                └──── ancestor.marking ≤ raw ──┘
                                      strict at p
```
-/
theorem exists_branch_growth_witness_of_new_omegaPlace
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {labels : List T}
    {src tgt : Branch P} {t : T} {p : P}
    (hprefix : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (htr : (dfsLTS net).Tr src t tgt)
    (hpSrc : p ∉ OmegaMarking.omegaPlaces src.marking)
    (hpTgt : p ∈ OmegaMarking.omegaPlaces tgt.marking) :
    ∃ ancestor before segment,
      (dfsLTS net).MTr (Branch.initial m₀) before ancestor ∧
      (dfsLTS net).MTr ancestor segment src ∧
      ancestor.marking ≤ succMarking net src.marking t ∧
      ancestor.marking p < succMarking net src.marking t p := by
  obtain ⟨a, ha, hle, hlt⟩ :=
    exists_history_growth_witness_of_new_omegaPlace htr hpSrc hpTgt
  rw [Branch.history, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rcases ancestor_eq_predecessor_of_mTr hprefix ha with hroot |
        ⟨before, ancestor, segment, _, hbefore, hsegment, _, hmarking⟩
    · simp [Branch.initial, Branch.root] at hroot
    · subst a
      exact ⟨ancestor, before, segment, hbefore, hsegment, hle, hlt⟩
  · exact ⟨src, labels, [], hprefix, Cslib.LTS.MTr.refl, hle, hlt⟩

/-- The finite set of places which are `ω` in `tgt` but not in `src`.

This proof-only definition directly uses the mathematical omega-place sets;
it is not intended to be executed by the Karp–Miller algorithm. -/
noncomputable def newOmegaPlaces [FinEnum P]
    (src tgt : Branch P) : Finset P :=
  OmegaMarking.omegaPlaces tgt.marking \
    OmegaMarking.omegaPlaces src.marking

/-- Lift the growth-witness theorem from one new `ω`-place to all new
`ω`-places of a DFS step.

The lifting introduces no additional Petri-net argument. Membership
`p ∈ newOmegaPlaces src tgt` unfolds into exactly the two hypotheses required
by `exists_branch_growth_witness_of_new_omegaPlace`:

```text
p ∈ omegaPlaces tgt.marking     p ∉ omegaPlaces src.marking.
```

Applying that theorem pointwise therefore gives a possibly different earlier
branch and path segment for every newly accelerated place. This finite family
is the input required by the later combined-pumping construction. -/
theorem branch_growth_witnesses_of_newOmegaPlaces
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {labels : List T}
    {src tgt : Branch P} {t : T}
    (hprefix : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (htr : (dfsLTS net).Tr src t tgt) :
    ∀ p ∈ newOmegaPlaces src tgt,
      ∃ ancestor before segment,
        (dfsLTS net).MTr (Branch.initial m₀) before ancestor ∧
        (dfsLTS net).MTr ancestor segment src ∧
        ancestor.marking ≤ succMarking net src.marking t ∧
        ancestor.marking p < succMarking net src.marking t p := by
  intro p hp
  rw [newOmegaPlaces, Finset.mem_sdiff] at hp
  exact exists_branch_growth_witness_of_new_omegaPlace
    hprefix htr hp.2 hp.1

/- The natural-number token balance of a DFS execution at a place which is
finite in its target. Finiteness propagates backwards because DFS steps
preserve every existing `ω`-place. Accelerations therefore do not affect this
coordinate, and its balance is the ordinary Petri-net balance. -/
private theorem dfsMTr_balance_at_of_ne_top
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {ts : List T} {p : P}
    (hexec : (dfsLTS net).MTr src ts tgt)
    (htgt : tgt.marking p ≠ ⊤) :
    (tgt.marking p).toNat +
        ∑ t, firingCount ts t * net.pre p t =
      (src.marking p).toNat +
        ∑ t, firingCount ts t * net.post p t := by
  induction hexec with
  | refl => simp
  | @stepL src t mid ts tgt htr htail ih =>
      have hmid : mid.marking p ≠ ⊤ := by
        intro hp
        apply htgt
        rw [← OmegaMarking.mem_omegaPlaces]
        exact omegaPlaces_mono_of_mTr htail
          (OmegaMarking.mem_omegaPlaces.mpr hp)
      have hsrc : src.marking p ≠ ⊤ := by
        intro hp
        apply hmid
        rw [← OmegaMarking.mem_omegaPlaces]
        exact omegaPlaces_mono_of_tr htr
          (OmegaMarking.mem_omegaPlaces.mpr hp)
      have hstep :
          (mid.marking p).toNat + net.pre p t =
            (src.marking p).toNat + net.post p t := by
        have henabled : net.pre p t ≤ (src.marking p).toNat := by
          apply ENat.natCast_le_natCast.mp
          rw [ENat.natCast_toNat hsrc]
          exact (mem_dfsSuccessors_iff.mp htr).2.1 p
        have hmarking :=
          marking_apply_eq_succMarking_of_tr_of_ne_top htr hmid
        rw [succMarking, ← ENat.natCast_toNat hsrc,
          ← ENat.natCast_toNat hmid] at hmarking
        have hmarkingNat :
            (mid.marking p).toNat =
              (src.marking p).toNat - net.pre p t + net.post p t := by
          exact_mod_cast hmarking
        omega
      have htailBalance := ih htgt
      simp_rw [firingCount_weighted_sum_cons]
      omega

/- A target demand at a finite coordinate can be propagated backwards along
a DFS execution without exceeding the token count at the abstract source.

Accelerations at other places are irrelevant. Since the target coordinate is
finite, it remained finite throughout the path, and every DFS edge follows
the ordinary firing equation at that coordinate. -/
private theorem leastPreMarkingSequence_apply_le_of_dfsMTr
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {ts : List T}
    {demand : Marking P} {p : P}
    (hexec : (dfsLTS net).MTr src ts tgt)
    (htgt : tgt.marking p ≠ ⊤)
    (hdemand : (demand p : ℕ∞) ≤ tgt.marking p) :
    net.leastPreMarkingSequence ts demand p ≤
      (src.marking p).toNat := by
  induction hexec with
  | refl =>
      rw [← ENat.natCast_toNat htgt] at hdemand
      exact ENat.natCast_le_natCast.mp hdemand
  | @stepL src t mid ts tgt htr htail ih =>
      have hmid : mid.marking p ≠ ⊤ := by
        intro hp
        apply htgt
        rw [← OmegaMarking.mem_omegaPlaces]
        exact omegaPlaces_mono_of_mTr htail
          (OmegaMarking.mem_omegaPlaces.mpr hp)
      have hsrc : src.marking p ≠ ⊤ := by
        intro hp
        apply hmid
        rw [← OmegaMarking.mem_omegaPlaces]
        exact omegaPlaces_mono_of_tr htr
          (OmegaMarking.mem_omegaPlaces.mpr hp)
      have htailDemand :
          net.leastPreMarkingSequence ts demand p ≤
            (mid.marking p).toNat := ih htgt hdemand
      have henabled : net.pre p t ≤ (src.marking p).toNat := by
        apply ENat.natCast_le_natCast.mp
        rw [ENat.natCast_toNat hsrc]
        exact (mem_dfsSuccessors_iff.mp htr).2.1 p
      have hmarking :=
        marking_apply_eq_succMarking_of_tr_of_ne_top htr hmid
      rw [succMarking, ← ENat.natCast_toNat hsrc,
        ← ENat.natCast_toNat hmid] at hmarking
      have hmarkingNat :
          (mid.marking p).toNat =
            (src.marking p).toNat - net.pre p t + net.post p t := by
        exact_mod_cast hmarking
      simp only [WeightedNet.leastPreMarkingSequence,
        WeightedNet.leastPreMarking]
      omega

/-- Concretise one abstract branch-growth witness.

Suppose `ancestor` is an earlier branch on the DFS prefix and its marking is
below the raw successor, with strict inequality at the newly accelerated
place `p`:

```text
Branch.initial m₀ ──before──▶ ancestor ──segment──▶ src ──t──▶ raw
                                │                              │
                                └──── ancestor.marking ≤ raw ──┘
                                      strict at p
```

The theorem constructs an ordinary firing sequence which has the same effect
on every newly accelerated place:

```text
concreteSrc ──ts──▶ concreteEnd

concreteSrc(q) ≤ concreteEnd(q)  for every newly accelerated q
concreteSrc(p) < concreteEnd(p)
```

The endpoint remains below `raw`. The path may lose tokens at places which
were already `ω`; those losses will later be paid for by budget-backed
repetition. -/
theorem exists_concrete_growth_path_of_branch_witness
    [FinEnum P] [FinEnum T]
    {ancestor src tgt : Branch P} {segment : List T}
    {t : T} {p : P}
    (hsegment : (dfsLTS net).MTr ancestor segment src)
    (htr : (dfsLTS net).Tr src t tgt)
    (hp : p ∈ newOmegaPlaces src tgt)
    (hle : ancestor.marking ≤ succMarking net src.marking t)
    (hlt : ancestor.marking p < succMarking net src.marking t p) :
    ∃ concreteSrc concreteEnd ts,
      net.FiresSequence concreteSrc ts concreteEnd ∧
      (∀ q, succMarking net src.marking t q ≠ ⊤ →
        concreteSrc q ≤ concreteEnd q) ∧
      concreteSrc p < concreteEnd p ∧
      concreteEnd.toOmega ≤ succMarking net src.marking t := by
  let raw := succMarking net src.marking t
  let target := raw.finiteApprox 0
  let labels := segment ++ [t]
  let concreteSrc := net.leastPreMarkingSequence labels target
  let concreteEnd := net.firingSequenceResult concreteSrc labels
  have htargetRaw : target.toOmega ≤ raw :=
    raw.finiteApprox_toOmega_le 0
  have homega : net.OmegaFires src.marking t raw := by
    exact ⟨(mem_dfsSuccessors_iff.mp htr).2.1, fun _ => rfl⟩
  have htailDemand :
      (net.leastPreMarking t target).toOmega ≤ src.marking :=
    net.leastPreMarking_toOmega_le_of_omegaFires homega htargetRaw
  have hsrcFinite_of_raw {q : P} (hraw : raw q ≠ ⊤) :
      src.marking q ≠ ⊤ := by
    intro htop
    apply hraw
    have hmem : q ∈ OmegaMarking.omegaPlaces src.marking :=
      OmegaMarking.mem_omegaPlaces.mpr htop
    have := (show OmegaMarking.omegaPlaces raw =
        OmegaMarking.omegaPlaces src.marking by
      simpa [raw] using omegaPlaces_succMarking (net := net)
        (m := src.marking) (t := t))
    rw [← OmegaMarking.mem_omegaPlaces, this]
    exact hmem
  have hrequiredAncestor {q : P} (hraw : raw q ≠ ⊤) :
      concreteSrc q ≤ (ancestor.marking q).toNat := by
    have hsrcFinite := hsrcFinite_of_raw hraw
    dsimp only [concreteSrc, labels]
    rw [net.leastPreMarkingSequence_append]
    change net.leastPreMarkingSequence segment
        (net.leastPreMarking t target) q ≤ (ancestor.marking q).toNat
    apply leastPreMarkingSequence_apply_le_of_dfsMTr
      (net := net) hsegment hsrcFinite
    exact htailDemand q
  have hsrcRaw : concreteSrc.toOmega ≤ raw := by
    intro q
    by_cases hraw : raw q = ⊤
    · simp [hraw]
    · have hrequired := hrequiredAncestor hraw
      have hancestorFinite : ancestor.marking q ≠ ⊤ := by
        intro htop
        exact hraw (top_unique (by simpa [htop] using hle q))
      have hancestorRaw :
          (ancestor.marking q).toNat ≤ (raw q).toNat := by
        apply ENat.natCast_le_natCast.mp
        rw [ENat.natCast_toNat hancestorFinite,
          ENat.natCast_toNat hraw]
        exact hle q
      change (concreteSrc q : ℕ∞) ≤ raw q
      rw [← ENat.natCast_toNat hraw]
      exact ENat.natCast_le_natCast.mpr (hrequired.trans hancestorRaw)
  obtain ⟨hsequence, htargetEnd⟩ :=
    net.firesSequence_cover_of_leastPreMarkingSequence_le
      labels target (by rfl)
  have effect_at {q : P} (hraw : raw q ≠ ⊤) :
      concreteEnd q +
          ∑ u, firingCount labels u * net.pre q u =
        concreteSrc q +
          ∑ u, firingCount labels u * net.post q u ∧
      (raw q).toNat +
          ∑ u, firingCount labels u * net.pre q u =
        (ancestor.marking q).toNat +
          ∑ u, firingCount labels u * net.post q u := by
    have hconcreteInt := hsequence.int_state_equation q
    change (concreteEnd q : ℤ) =
      (concreteSrc q : ℤ) +
        ∑ u, (firingCount labels u : ℤ) * net.incidence q u at hconcreteInt
    have hconcrete :
        concreteEnd q +
            ∑ u, firingCount labels u * net.pre q u =
          concreteSrc q +
            ∑ u, firingCount labels u * net.post q u := by
      have hcast :
          (concreteEnd q : ℤ) +
              ∑ u, (firingCount labels u : ℤ) * (net.pre q u : ℤ) =
            (concreteSrc q : ℤ) +
              ∑ u, (firingCount labels u : ℤ) * (net.post q u : ℤ) := by
        simp only [WeightedNet.incidence, mul_sub,
          Finset.sum_sub_distrib] at hconcreteInt
        omega
      exact_mod_cast hcast
    have hsrcFinite := hsrcFinite_of_raw hraw
    have hsegmentBalance :=
      dfsMTr_balance_at_of_ne_top (net := net) hsegment hsrcFinite
    have henabled : net.pre q t ≤ (src.marking q).toNat := by
      apply ENat.natCast_le_natCast.mp
      rw [ENat.natCast_toNat hsrcFinite]
      exact homega.1 q
    have hrawEq :
        (raw q).toNat =
          (src.marking q).toNat - net.pre q t + net.post q t := by
      have heq : raw q = src.marking q - net.pre q t + net.post q t := rfl
      rw [← ENat.natCast_toNat hsrcFinite,
        ← ENat.natCast_toNat hraw] at heq
      exact_mod_cast heq
    constructor
    · exact hconcrete
    · simp_rw [firingCount_weighted_sum] at hsegmentBalance ⊢
      simp [labels] at ⊢
      omega
  have hendRaw : concreteEnd.toOmega ≤ raw := by
    intro q
    by_cases hraw : raw q = ⊤
    · simp [hraw]
    · obtain ⟨hconcrete, habstract⟩ := effect_at hraw
      have hsrcLe := hrequiredAncestor hraw
      change (concreteEnd q : ℕ∞) ≤ raw q
      rw [← ENat.natCast_toNat hraw]
      exact ENat.natCast_le_natCast.mpr (by omega)
  refine ⟨concreteSrc, concreteEnd, labels, hsequence, ?_, ?_, hendRaw⟩
  · intro q hraw
    obtain ⟨hconcrete, habstract⟩ := effect_at hraw
    have hancestorRaw : (ancestor.marking q).toNat ≤ (raw q).toNat := by
      have hancestorFinite : ancestor.marking q ≠ ⊤ := by
        intro htop
        exact hraw (top_unique (by simpa [htop] using hle q))
      apply ENat.natCast_le_natCast.mp
      rw [ENat.natCast_toNat hancestorFinite, ENat.natCast_toNat hraw]
      exact hle q
    omega
  · have hpRaw : raw p ≠ ⊤ := by
      intro htop
      have hpParts := hp
      rw [newOmegaPlaces, Finset.mem_sdiff] at hpParts
      apply hpParts.2
      have hmem : p ∈ OmegaMarking.omegaPlaces raw :=
        OmegaMarking.mem_omegaPlaces.mpr htop
      have heq : OmegaMarking.omegaPlaces raw =
          OmegaMarking.omegaPlaces src.marking := by
        simpa [raw] using omegaPlaces_succMarking (net := net)
          (m := src.marking) (t := t)
      rwa [heq] at hmem
    obtain ⟨hconcrete, habstract⟩ := effect_at hpRaw
    have hpAncestorFinite : ancestor.marking p ≠ ⊤ := by
      intro htop
      exact hpRaw (top_unique (by simpa [htop] using hle p))
    have hpStrict : (ancestor.marking p).toNat < (raw p).toNat := by
      apply ENat.natCast_lt_natCast.mp
      rw [ENat.natCast_toNat hpAncestorFinite, ENat.natCast_toNat hpRaw]
      exact hlt
    omega

/- Combine finitely many concrete paths while allowing losses only at the
`omega` components of a common abstract upper bound.

The initial base has the exact value of `raw` at every finite component. At
an `omega` component it accumulates the sources of the paths still to be
executed, which acts as their budget. Consequently every path can be shifted
to the current endpoint and appended. -/
private theorem exists_combined_growth_below_omega
    {A : Finset P} {raw : OmegaMarking P} (budget : Marking P)
    (hAfin : ∀ p ∈ A, raw p ≠ ⊤)
    (hpaths : ∀ p ∈ A, ∃ src tgt ts,
      net.FiresSequence src ts tgt ∧
      (∀ q, raw q ≠ ⊤ → src q ≤ tgt q) ∧
      src p < tgt p ∧ tgt.toOmega ≤ raw) :
    ∃ base tgt ts,
      base.toOmega ≤ raw ∧
      net.FiresSequence base ts tgt ∧
      (∀ q, raw q ≠ ⊤ → base q ≤ tgt q) ∧
      (∀ q, raw q ≠ ⊤ → base q = (raw q).toNat) ∧
      (∀ q, raw q = ⊤ → budget q ≤ tgt q) ∧
      ∀ p ∈ A, base p < tgt p := by
  classical
  have combine : ∀ I : Finset P, I ⊆ A →
      ∃ base tgt ts,
        base.toOmega ≤ raw ∧
        net.FiresSequence base ts tgt ∧
        (∀ q, raw q ≠ ⊤ → base q ≤ tgt q) ∧
        (∀ q, raw q ≠ ⊤ → base q = (raw q).toNat) ∧
        (∀ q, raw q = ⊤ → budget q ≤ tgt q) ∧
        ∀ p ∈ I, base p < tgt p := by
    intro I hIA
    induction I using Finset.induction with
    | empty =>
        let base := raw.finiteApprox budget
        refine ⟨base, base, [], raw.finiteApprox_toOmega_le budget,
          WeightedNet.FiresSequence.nil base, by simp, ?_, ?_, by simp⟩
        · intro q hq
          simp [base, OmegaMarking.finiteApprox, hq]
        · intro q hq
          simp [base, hq]
    | @insert p I hp ih =>
        have hpA : p ∈ A := hIA (by simp)
        have hIA' : I ⊆ A := fun q hq => hIA (by simp [hq])
        obtain ⟨base, end_, before, hbaseRaw, hbefore, hmono,
          hbaseFinite, hbudgetEnd, hgrows⟩ := ih hIA'
        obtain ⟨srcP, tgtP, path, hpath, hpathMono, hpGrowth,
          htgtRaw⟩ := hpaths p hpA
        let extra : Marking P := fun q => if raw q = ⊤ then srcP q else 0
        let mid : Marking P := end_ + extra
        have hsrcMid : srcP ≤ mid := by
          intro q
          by_cases hq : raw q = ⊤
          · simp [mid, extra, hq]
          · have hsrcTgt : srcP q ≤ tgtP q := hpathMono q hq
            have htgtLe : tgtP q ≤ (raw q).toNat := by
              apply ENat.natCast_le_natCast.mp
              rw [ENat.natCast_toNat hq]
              exact htgtRaw q
            have hrawBase : (raw q).toNat = base q :=
              (hbaseFinite q hq).symm
            exact hsrcTgt.trans <| htgtLe.trans <|
              hrawBase.le.trans <| (hmono q hq).trans (by simp [mid])
        let d : Marking P := mid - srcP
        have hmidEq : srcP + d = mid := by
          funext q
          exact Nat.add_sub_of_le (hsrcMid q)
        have hbeforeShifted := hbefore.add extra
        have hpathShifted :
            net.FiresSequence mid path (tgtP + d) := by
          rw [← hmidEq]
          exact hpath.add d
        let newBase := base + extra
        let newEnd := tgtP + d
        have hcombined : net.FiresSequence newBase (before ++ path) newEnd :=
          hbeforeShifted.append hpathShifted
        have hnewBaseRaw : newBase.toOmega ≤ raw := by
          intro q
          by_cases hq : raw q = ⊤
          · simp [hq]
          · change ((newBase q : ℕ) : ℕ∞) ≤ raw q
            simp [newBase, extra, hq, hbaseFinite q hq,
              ENat.natCast_toNat hq]
        have hnewBaseFinite : ∀ q, raw q ≠ ⊤ →
            newBase q = (raw q).toNat := by
          intro q hq
          simp [newBase, extra, hq, hbaseFinite q hq]
        have hnewMono : ∀ q, raw q ≠ ⊤ →
            newBase q ≤ newEnd q := by
          intro q hq
          have hsrcLe := hsrcMid q
          have hpathLe := hpathMono q hq
          have hbaseMid : newBase q ≤ mid q := by
            exact Nat.add_le_add_right (hmono q hq) (extra q)
          dsimp [newEnd, d]
          omega
        refine ⟨newBase, newEnd, before ++ path, hnewBaseRaw, hcombined,
          hnewMono, hnewBaseFinite, ?_, ?_⟩
        · intro q hq
          have hbudget := hbudgetEnd q hq
          have hd : d q = end_ q := by
            simp [d, mid, extra, hq]
          simp [newEnd, hd]
          exact hbudget.trans (Nat.le_add_left _ _)
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · have hpFinite := hAfin _ hpA
          have hbaseMid : newBase q ≤ mid q := by
            exact Nat.add_le_add_right (hmono q hpFinite) (extra q)
          have hshiftGrowth : mid q < newEnd q := by
            have hmidPoint := congrFun hmidEq q
            dsimp [newEnd, d]
            omega
          exact hbaseMid.trans_lt hshiftGrowth
        · have hqA := hIA' hq
          have hqFinite := hAfin q hqA
          have hbaseEq : newBase q = base q := by
            simp [newBase, extra, hqFinite]
          have hendLe : end_ q ≤ newEnd q := by
            have hpathLe := hpathMono q hqFinite
            have hmidPoint := congrFun hmidEq q
            have hendMid : end_ q ≤ mid q := by simp [mid, extra, hqFinite]
            dsimp [newEnd, d]
            omega
          rw [hbaseEq]
          exact (hgrows q hq).trans_le hendLe
  exact combine A Finset.Subset.rfl

/- Shift concrete growth paths to a common endpoint while preserving the two
side conditions required by Karp–Miller soundness. -/
private theorem exists_common_growth_base_below
    {A : Finset P} {raw : OmegaMarking P} {demand seed : Marking P}
    (hseedRaw : seed.toOmega ≤ raw)
    (hseedDemand : ∀ q ∉ A, demand q ≤ seed q)
    (hpaths : ∀ p ∈ A, ∃ src tgt ts,
      net.FiresSequence src ts tgt ∧ src ≤ tgt ∧ src p < tgt p ∧
      tgt.toOmega ≤ raw ∧ ∀ q ∉ A, demand q ≤ tgt q) :
    ∃ base,
      base.toOmega ≤ raw ∧
      (∀ q ∉ A, demand q ≤ base q) ∧
      ∀ p ∈ A, ∃ src ts,
        net.FiresSequence src ts base ∧ src ≤ base ∧ src p < base p := by
  classical
  have merge : ∀ B : Finset P, B ⊆ A →
      ∃ base,
        base.toOmega ≤ raw ∧
        (∀ q ∉ A, demand q ≤ base q) ∧
        ∀ p ∈ B, ∃ src ts,
          net.FiresSequence src ts base ∧ src ≤ base ∧ src p < base p := by
    intro B hBA
    induction B using Finset.induction with
    | empty =>
        exact ⟨seed, hseedRaw, hseedDemand, by simp⟩
    | @insert p B hp ih =>
        have hpA : p ∈ A := hBA (by simp)
        have hBA' : B ⊆ A := fun q hq => hBA (by simp [hq])
        obtain ⟨srcP, endP, tsP, hseqP, hleP, hltP, hendPRaw,
          hendPDemand⟩ := hpaths p hpA
        obtain ⟨baseB, hbaseBRaw, hbaseBDemand, hbaseB⟩ := ih hBA'
        let base : Marking P := endP ⊔ baseB
        have hendP : endP ≤ base := le_sup_left
        have hbaseB_le : baseB ≤ base := le_sup_right
        have hbaseRaw : base.toOmega ≤ raw := by
          intro q
          change ((max (endP q) (baseB q) : ℕ) : ℕ∞) ≤ raw q
          by_cases hle : endP q ≤ baseB q
          · rw [max_eq_right hle]
            exact hbaseBRaw q
          · rw [max_eq_left (Nat.le_of_not_ge hle)]
            exact hendPRaw q
        have hbaseDemand : ∀ q ∉ A, demand q ≤ base q := by
          intro q hq
          exact (hendPDemand q hq).trans (hendP q)
        have shift {q : P} {src end_ : Marking P} {ts : List T}
            (hseq : net.FiresSequence src ts end_)
            (hle : src ≤ end_) (hlt : src q < end_ q)
            (hend : end_ ≤ base) :
            ∃ shiftedSrc,
              net.FiresSequence shiftedSrc ts base ∧
              shiftedSrc ≤ base ∧ shiftedSrc q < base q := by
          let d : Marking P := base - end_
          have hendEq : end_ + d = base := by
            funext r
            exact Nat.add_sub_of_le (hend r)
          refine ⟨src + d, ?_, ?_, ?_⟩
          · rw [← hendEq]
            exact hseq.add d
          · rw [← hendEq]
            exact fun r => Nat.add_le_add_right (hle r) (d r)
          · rw [← hendEq]
            exact Nat.add_lt_add_right hlt (d q)
        refine ⟨base, hbaseRaw, hbaseDemand, ?_⟩
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · obtain ⟨shiftedSrc, hseq, hle, hlt⟩ :=
            shift hseqP hleP hltP hendP
          exact ⟨shiftedSrc, tsP, hseq, hle, hlt⟩
        · obtain ⟨srcQ, tsQ, hseqQ, hleQ, hltQ⟩ := hbaseB q hq
          obtain ⟨shiftedSrc, hseq, hle, hlt⟩ :=
            shift hseqQ hleQ hltQ hbaseB_le
          exact ⟨shiftedSrc, tsQ, hseq, hle, hlt⟩
  exact merge A Finset.Subset.rfl

/-- Outside the newly introduced `ω`-places, a finite raw component is not
changed by acceleration.

If the DFS target were `ω` at `q`, while the raw successor were finite there,
then `q` would belong to `newOmegaPlaces src tgt`, contrary to `hq`.
Therefore the target is finite at `q`, and its value is the raw firing result.
-/
theorem target_eq_raw_of_not_mem_newOmegaPlaces
    [FinEnum P] [FinEnum T] {src tgt : Branch P} {t : T} {q : P}
    (htr : (dfsLTS net).Tr src t tgt)
    (hq : q ∉ newOmegaPlaces src tgt)
    (hraw : succMarking net src.marking t q ≠ ⊤) :
    tgt.marking q = succMarking net src.marking t q := by
  have htgtFinite : tgt.marking q ≠ ⊤ := by
    intro htgt
    have htgtMem : q ∈ OmegaMarking.omegaPlaces tgt.marking :=
      OmegaMarking.mem_omegaPlaces.mpr htgt
    have hsrcMem : q ∈ OmegaMarking.omegaPlaces src.marking := by
      by_contra hsrc
      apply hq
      rw [newOmegaPlaces, Finset.mem_sdiff]
      exact ⟨htgtMem, hsrc⟩
    apply hraw
    rw [← OmegaMarking.mem_omegaPlaces, omegaPlaces_succMarking]
    exact hsrcMem
  exact marking_apply_eq_succMarking_of_tr_of_ne_top htr htgtFinite

/-- A finite approximation of the raw successor already covers the demand at
every place which is not newly accelerated.

At an existing `ω`-place, `finiteApprox` stores `demand q` directly. At a
finite raw component, `target_eq_raw_of_not_mem_newOmegaPlaces` identifies the
DFS target with the raw value, so the result follows from `hdemand`. -/
theorem demand_le_finiteApprox_raw_of_not_mem_newOmegaPlaces
    [FinEnum P] [FinEnum T] {demand : Marking P}
    {src tgt : Branch P} {t : T} {q : P}
    (htr : (dfsLTS net).Tr src t tgt)
    (hdemand : demand.toOmega ≤ tgt.marking)
    (hq : q ∉ newOmegaPlaces src tgt) :
    demand q ≤ (succMarking net src.marking t).finiteApprox demand q := by
  let raw := succMarking net src.marking t
  by_cases hraw : raw q = ⊤
  · simp [raw, hraw]
  · have htgtRaw : tgt.marking q = raw q := by
      simpa [raw] using
        target_eq_raw_of_not_mem_newOmegaPlaces htr hq (by simpa [raw])
    have hqDemand := hdemand q
    change (demand q : ℕ∞) ≤ tgt.marking q at hqDemand
    rw [htgtRaw, ← ENat.natCast_toNat hraw] at hqDemand
    have := ENat.natCast_le_natCast.mp hqDemand
    simpa [raw, OmegaMarking.finiteApprox, hraw] using this

/-- Combine and repeat the concrete branch witnesses until they cover a
prescribed finite demand.

The combined path is nondecreasing at every finite component of `raw` and
strictly increasing at every newly accelerated place. Possible losses occur
only at existing `ω` components. `repeat_with_budget_ge_on` pays for those
losses in the source, which therefore still embeds below `raw`.

```text
concreteSrc ──combined witnesses, repeated with a budget──▶ reached
     │                                                          ▲
     └── toOmega ≤ raw                              demand ≤ ─┘
```
-/
theorem exists_concrete_growth_execution
    [FinEnum P] [FinEnum T] {m₀ demand : Marking P}
    {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt)
    (hwitnesses : ∀ p ∈ newOmegaPlaces src tgt,
      ∃ ancestor before segment,
        (dfsLTS net).MTr (Branch.initial m₀) before ancestor ∧
        (dfsLTS net).MTr ancestor segment src ∧
        ancestor.marking ≤ succMarking net src.marking t ∧
        ancestor.marking p < succMarking net src.marking t p)
    (hdemand : demand.toOmega ≤ tgt.marking) :
    ∃ concreteSrc reached ts,
      concreteSrc.toOmega ≤ succMarking net src.marking t ∧
      net.FiresSequence concreteSrc ts reached ∧
      demand ≤ reached := by
  let A := newOmegaPlaces src tgt
  let raw := succMarking net src.marking t
  have hAfin : ∀ p ∈ A, raw p ≠ ⊤ := by
    intro p hp htop
    change p ∈ newOmegaPlaces src tgt at hp
    rw [newOmegaPlaces, Finset.mem_sdiff] at hp
    apply hp.2
    have hmem : p ∈ OmegaMarking.omegaPlaces raw :=
      OmegaMarking.mem_omegaPlaces.mpr htop
    have heq : OmegaMarking.omegaPlaces raw =
        OmegaMarking.omegaPlaces src.marking := by
      simpa [raw] using omegaPlaces_succMarking (net := net)
        (m := src.marking) (t := t)
    rwa [heq] at hmem
  have hpaths : ∀ p ∈ A, ∃ concreteSrc concreteEnd ts,
      net.FiresSequence concreteSrc ts concreteEnd ∧
      (∀ q, raw q ≠ ⊤ → concreteSrc q ≤ concreteEnd q) ∧
      concreteSrc p < concreteEnd p ∧ concreteEnd.toOmega ≤ raw := by
    intro p hp
    obtain ⟨ancestor, _before, segment, _hbefore, hsegment, hle, hlt⟩ :=
      hwitnesses p hp
    simpa [raw] using exists_concrete_growth_path_of_branch_witness
      hsegment htr hp hle hlt
  obtain ⟨base, grown, combined, hbaseRaw, hcombined, hmono,
    hbaseFinite, hbudgetGrown, hgrows⟩ :=
    exists_combined_growth_below_omega (net := net) demand hAfin hpaths
  obtain ⟨hrepeated, hgrownReached, hbounds⟩ :=
    hcombined.repeat_with_budget_ge_on_each A demand hgrows
  let n := ∑ p ∈ A, demand p
  let concreteSrc := base + n • (base - grown)
  let reached := grown + n • (grown - base)
  have hconcreteSrcRaw : concreteSrc.toOmega ≤ raw := by
    intro q
    by_cases hq : raw q = ⊤
    · simp [hq]
    · have hloss : base q - grown q = 0 :=
        Nat.sub_eq_zero_of_le (hmono q hq)
      have hsrcEq : concreteSrc q = base q := by
        simp [concreteSrc, hloss]
      change ((concreteSrc q : ℕ) : ℕ∞) ≤ raw q
      rw [hsrcEq, hbaseFinite q hq, ENat.natCast_toNat hq]
  refine ⟨concreteSrc, reached, (List.replicate (n + 1) combined).flatten,
    hconcreteSrcRaw, ?_, ?_⟩
  · simpa [concreteSrc, reached, n] using hrepeated
  · intro q
    by_cases hqA : q ∈ A
    · simpa [reached, n] using hbounds q hqA
    · by_cases hq : raw q = ⊤
      · exact (hbudgetGrown q hq).trans (hgrownReached q)
      · have hdemandBase : demand q ≤ base q := by
          have := demand_le_finiteApprox_raw_of_not_mem_newOmegaPlaces
            htr hdemand hqA
          simpa [raw, OmegaMarking.finiteApprox, hq,
            hbaseFinite q hq] using this
        exact hdemandBase.trans ((hmono q hq).trans (hgrownReached q))

/-- Realise a finite demand using growth witnesses for every newly
accelerated place.

The hypotheses provide, for each `p ∈ newOmegaPlaces src tgt`, an earlier
branch whose marking is below the raw successor and is strictly smaller at
`p`. The intended proof concretises these abstract branch segments with
sufficient budgets at the already-`ω` places, combines their positive
effects using `FiresSequence.exists_combined_growth`, and repeats the combined
sequence until all components of `demand` are covered.

```text
                            src ──t──▶ raw ──accelerate──▶ tgt.marking
                             ▲           ▲                       ▲
                             │           │                       │
ancestorₚ ──segmentₚ─────────┘           │                       │
    │                                    │                       │
    └──── marking ≤ raw, strict at p ────┘                       │
                                                                 │
m₀ ──reachable──▶ finiteRaw ──combined pumps──▶ reached           │
                                                   demand ≤ reached
```

The conclusion is the concrete witness required by `CoverableFrom`: one
marking reachable from `m₀` which covers the prescribed demand. -/
theorem exists_reachable_cover_of_branch_growth_witnesses
    [FinEnum P] [FinEnum T] {m₀ demand : Marking P}
    {src tgt : Branch P} {t : T}
    (hsound : net.OmegaCoverableFrom m₀ src.marking)
    (htr : (dfsLTS net).Tr src t tgt)
    (_hnew : (newOmegaPlaces src tgt).Nonempty)
    (hwitnesses : ∀ p ∈ newOmegaPlaces src tgt,
      ∃ ancestor before segment,
        (dfsLTS net).MTr (Branch.initial m₀) before ancestor ∧
        (dfsLTS net).MTr ancestor segment src ∧
        ancestor.marking ≤ succMarking net src.marking t ∧
        ancestor.marking p < succMarking net src.marking t p)
    (hdemand : demand.toOmega ≤ tgt.marking) :
    ∃ reached, net.Reachable m₀ reached ∧ demand ≤ reached := by
  let A := newOmegaPlaces src tgt
  let raw := succMarking net src.marking t
  obtain ⟨concreteSrc, concreteEnd, labels, hsrcRaw, hsequence,
    hdemandEnd⟩ :=
    exists_concrete_growth_execution htr hwitnesses hdemand
  have hrawSound : net.OmegaCoverableFrom m₀ raw := by
    apply net.omegaCoverableFrom_of_omegaFires hsound
    exact ⟨(mem_dfsSuccessors_iff.mp htr).2.1, fun _ => rfl⟩
  obtain ⟨reachableSrc, hreachableSrc, hsrcBelow⟩ :=
    hrawSound concreteSrc hsrcRaw
  obtain ⟨reached, hreachableReached, hendBelow⟩ :=
    WeightedNet.Reachable.mono (net := net)
      (⟨labels, hsequence⟩ : net.Reachable concreteSrc concreteEnd)
      hsrcBelow
  exact ⟨reached, hreachableSrc.trans hreachableReached,
    hdemandEnd.trans hendBelow⟩

/-- Soundness of a DFS step which introduces at least one new `ω`-place.

For an arbitrary finite demand below `tgt.marking`, the intended proof:

1. extracts from `hprefix` the historical segments witnessing each newly
   accelerated place;
2. chooses enough repetitions to meet the demand at those places;
3. propagates backwards the budget required at already-`ω` places;
4. uses `hsound` to obtain a reachable concrete source with that budget; and
5. executes the final transition and pumping segments forwards.

The abstract prefix provides, for each newly accelerated place `p`, an earlier
marking and a suffix which, followed by `t`, ends at the unaccelerated
successor `raw`:

```text
Branch.initial m₀ ──pre──▶ ⋯ ──▶ ancestorₚ ──suffixₚ──▶ src ──t──▶ raw
                                      │                              │
                                      └──── ancestorₚ ≤ raw ─────────┘
                                            ancestorₚ(p) < raw(p)

raw ──accelerate new ω-places──▶ tgt.marking
```

After combining the growing segments and calculating the required budget,
the concrete witness execution has the form:

```text
m₀ ──reachable──▶ concreteSrc ──t──▶ concreteRaw
                                         │
                                         └──pump──▶ ⋯ ──pump──▶ reached
                                                                    │
                                                             demand ≤ reached
```

`concreteSrc` is chosen large enough at the old ω-places to enable the final
transition and every pumping repetition. The repetitions make all newly
accelerated places large enough for `demand`.

This is the remaining acceleration-specific soundness obligation. -/
theorem omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_ssubset
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {pre : List T}
    {src tgt : Branch P} {t : T}
    (hprefix : (dfsLTS net).MTr (Branch.initial m₀) pre src)
    (hsound : net.OmegaCoverableFrom m₀ src.marking)
    (htr : (dfsLTS net).Tr src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking ⊂
      OmegaMarking.omegaPlaces tgt.marking) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  intro demand hdemand
  obtain ⟨p, hpTgt, hpSrc⟩ := Finset.exists_of_ssubset homega
  have hnew : (newOmegaPlaces src tgt).Nonempty := by
    refine ⟨p, ?_⟩
    rw [newOmegaPlaces, Finset.mem_sdiff]
    exact ⟨hpTgt, hpSrc⟩
  apply exists_reachable_cover_of_branch_growth_witnesses
    hsound htr hnew ?_ hdemand
  exact branch_growth_witnesses_of_newOmegaPlaces hprefix htr

/-- Extend soundness by one step along a Karp–Miller DFS execution.

`Branch.initial m₀` is the root branch: its current ω-marking is
`m₀.toOmega` and its ancestor list is empty.

The hypothesis `hprefix` specifies a finite DFS execution from this root to `src`,
with transition labels `pre`.
The hypothesis `hsound` is the induction hypothesis for that prefix: every
concrete marking below the ω-marking `src.marking` is coverable from `m₀`.
Finally, `htr` extends the execution by one transition `t`:

```text
Branch.initial m₀ ─────────pre─────────▶ src ──t──▶ tgt
                                          │          │
                                        sound  ⇒   sound
```

The proof distinguishes whether the set of `ω`-places is unchanged or grows
strictly. The equality case is handled by
`omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_eq`; the strict-subset case is
handled by `omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_ssubset`.
-/
theorem omegaCoverableFrom_of_dfsLTS_tr
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {pre : List T}
    {src tgt : Branch P} {t : T}
    (hprefix : (dfsLTS net).MTr (Branch.initial m₀) pre src)
    (hsound : net.OmegaCoverableFrom m₀ src.marking)
    (htr : (dfsLTS net).Tr src t tgt) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  by_cases homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking
  · exact omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_eq
      hsound htr homega
  · apply omegaCoverableFrom_of_dfsLTS_tr_of_omegaPlaces_ssubset
      hprefix hsound htr
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨omegaPlaces_mono_of_tr htr, homega⟩

private theorem omegaCoverableFrom_of_dfsMTr_from
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {pre labels : List T}
    {src tgt : Branch P}
    (hprefix : (dfsLTS net).MTr (Branch.initial m₀) pre src)
    (hsound : net.OmegaCoverableFrom m₀ src.marking)
    (hexec : (dfsLTS net).MTr src labels tgt) :
    net.OmegaCoverableFrom m₀ tgt.marking := by
  induction hexec generalizing pre with
  | refl => exact hsound
  | @stepL src t mid labels tgt htr htail ih =>
      have hmidSound := omegaCoverableFrom_of_dfsLTS_tr
        hprefix hsound htr
      exact ih (Cslib.LTS.MTr.stepR (dfsLTS net) hprefix htr) hmidSound

/-- Every marking reached by the Karp–Miller DFS is omega coverable from the
initial marking.

The proof starts with soundness of the embedded initial marking and repeatedly
applies `omegaCoverableFrom_of_dfsLTS_tr` along the DFS execution. -/
theorem omegaCoverableFrom_of_dfsMTr
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {labels : List T}
    {branch : Branch P}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels branch) :
    net.OmegaCoverableFrom m₀ branch.marking := by
  exact omegaCoverableFrom_of_dfsMTr_from
    Cslib.LTS.MTr.refl (net.omegaCoverableFrom_initial m₀) hexec

/-- **Soundness of the Karp–Miller tree.** Every ω-marking stored in the tree
generated from `m₀` is omega coverable from `m₀`.

The tree/DFS equivalence supplies a reachable branch carrying the stored
marking; `omegaCoverableFrom_of_dfsMTr` supplies its soundness. -/
theorem karpMillerDFS_omegaCoverableFrom_of_hasNode
    [FinEnum P] [FinEnum T] (net : WeightedNet P T) (m₀ : Marking P)
    {mω : OmegaMarking P}
    (hnode :
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω) :
    net.OmegaCoverableFrom m₀ mω := by
  obtain ⟨labels, branch, hexec, hmarking⟩ :=
    (karpMillerDFS_hasNode_iff_exists_dfsMTr net
      (Branch.initial m₀) mω).mp hnode
  rw [← hmarking]
  exact omegaCoverableFrom_of_dfsMTr hexec

end KarpMiller

end PetriNet
