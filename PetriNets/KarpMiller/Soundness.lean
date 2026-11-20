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

/-- An ω-marking `mω` is omega coverable from `m₀` when every concrete (no omega)
marking below `mω` is coverable from `m₀`.

Equivalently, the downward closure of `mω` among concrete markings is
contained in the downward closure of a marking reachable from `m₀`:

```text
∀ concrete marking m, m.toOmega ≤ mω → ∃ m', Reachable m₀ m' ∧ m ≤ m'.
```
-/
def WeightedNet.OmegaCoverableFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (mω : OmegaMarking P) : Prop :=
  ∀ m, m.toOmega ≤ mω → net.CoverableFrom m₀ m

/-- The initial marking embedded as an ω-marking is coverable from itself.
Every ordinary marking below `m₀.toOmega` is covered by the reachable
marking `m₀`. -/
theorem WeightedNet.omegaCoverableFrom_initial
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.OmegaCoverableFrom m₀ m₀.toOmega := by
  intro m hle
  refine ⟨m₀, WeightedNet.Reachable.refl net m₀, ?_⟩
  intro p
  exact ENat.natCast_le_natCast.mp (hle p)

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

/-- Every node stored in the Karp–Miller tree is the marking of a branch
reachable in the DFS transition system.

This is the structural connection between the executable tree and `dfsLTS`:

```text
tree.HasNode mω
        ⇒
∃ branch, initial m₀ ──labels──▶ branch ∧ branch.marking = mω
```

The proof will follow the recursive construction of `karpMillerDFS`. -/
private theorem exists_dfsMTr_of_karpMillerDFS_hasNode_from
    [FinEnum P] [FinEnum T] (src : Branch P) {mω : OmegaMarking P}
    (hnode : (karpMillerDFS net src).HasNode mω) :
    ∃ labels branch,
      (dfsLTS net).MTr src labels branch ∧ branch.marking = mω := by
  rw [karpMillerDFS] at hnode
  cases hnode with
  | root =>
      exact ⟨[], src, Cslib.LTS.MTr.refl, rfl⟩
  | @child root children t subtree mω hchild hsubtree =>
      simp only [List.mem_map] at hchild
      obtain ⟨candidate, hcandidate, heq⟩ := hchild
      rcases candidate with ⟨⟨u, next⟩, hnext⟩
      simp only at heq
      cases heq
      obtain ⟨labels, branch, hexec, hmarking⟩ :=
        exists_dfsMTr_of_karpMillerDFS_hasNode_from next hsubtree
      exact ⟨t :: labels, branch, hexec.stepL hnext, hmarking⟩
termination_by (dfsCall_wellFounded (net := net) (T := T)).wrap src
decreasing_by
  exact ⟨t, hnext⟩

/-- Every node stored in the Karp–Miller tree generated from `m₀` is the
marking of a branch reachable from `Branch.initial m₀` in `dfsLTS`. -/
theorem exists_dfsMTr_of_karpMillerDFS_hasNode
    [FinEnum P] [FinEnum T] {m₀ : Marking P} {mω : OmegaMarking P}
    (hnode :
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω) :
    ∃ labels branch,
      (dfsLTS net).MTr (Branch.initial m₀) labels branch ∧
      branch.marking = mω := by
  exact exists_dfsMTr_of_karpMillerDFS_hasNode_from
    (Branch.initial m₀) hnode
end KarpMiller

end PetriNet
