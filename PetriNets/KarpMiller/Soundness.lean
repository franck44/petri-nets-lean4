/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

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

/-- Soundness of a DFS step which introduces at least one new `ω`-place.

For an arbitrary finite demand below `tgt.marking`, the intended proof:

1. extracts from `hprefix` the historical segments witnessing each newly
   accelerated place;
2. chooses enough repetitions to meet the demand at those places;
3. propagates backwards the reserve required at already-`ω` places;
4. uses `hsound` to obtain a reachable concrete source with that reserve; and
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

After combining the growing segments and calculating the required reserve,
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
  sorry

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
