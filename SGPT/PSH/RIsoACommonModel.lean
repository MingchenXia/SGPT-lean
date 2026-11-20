import SGPT.PSH.CompactSmoothCommonModel
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.ConstantRankImage

/-!
# Common models over compact, possibly disconnected, complex manifolds

`SGPT.PSH.CompactSmoothCommonModel.exists_actual_compact_smooth_common_model` constructs, for two
modifications (`IsAnalyticModification`: proper holomorphic, biholomorphic off nowhere dense closed
analytic sets) `c₀ : Y₀ → X`, `c₁ : Y₁ → X` of a compact **connected** complex manifold `X`, a
compact complex manifold `Z` with modifications `g₀ : Z → Y₀`, `g₁ : Z → Y₁` and
`c₀ ∘ g₀ = c₁ ∘ g₁`.  This file removes the connectedness hypothesis
(`exists_compact_common_model`): no resolution theorem is involved, only the componentwise
assembly.

* `restrictMap c U` : the restriction `c⁻¹(U) → U` of a modification over an open set `U` is a
  modification (`isAnalyticModification_restrictMap`);
* `glueMap gP gQ` : for a clopen partition `Y = P ⊔ Q`, modifications `ZP → P` and `ZQ → Q` glue to
  a modification `ZP ⊕ ZQ → Y` (`isAnalyticModification_glueMap`);
* `card_connectedComponents_lt` : a proper nonempty clopen subset has fewer connected components;
* `exists_compact_common_model` : strong induction on the number of connected components.

Blueprint: `claude-r-iso-a.tex`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.PSH.RIsoACommonModel

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending AnalyticModificationLocalDiscrepancy AnalyticSubsetOpens

universe u

variable {n : ℕ}

/-! ### Basic facts -/

section Basic

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- A modification is surjective: its image is closed (proper maps are closed) and contains the
dense complement of the exceptional set. -/
theorem surjective_of_isAnalyticModification {c : Y → X}
    (hc : IsAnalyticModification (n := n) c) : Function.Surjective c := by
  obtain ⟨_, B, s, -, -, -, -, -, hBi, -, -, hright, -⟩ := hc.2.2
  have hclosed : IsClosed (range c) := hc.2.1.isClosedMap.isClosed_range
  have hdense : Dense (range c) := by
    refine (interior_eq_empty_iff_dense_compl.mp hBi).mono ?_
    intro x hx
    exact ⟨s x, hright x hx⟩
  intro x
  have : x ∈ closure (range c) := hdense x
  rw [hclosed.closure_eq] at this
  exact this

/-- Any map between empty manifolds is a modification. -/
theorem isAnalyticModification_of_isEmpty [IsEmpty X] [IsEmpty Y] (f : Y → X) :
    IsAnalyticModification (n := n) f := by
  refine ⟨fun y => isEmptyElim y, ?_, ∅, ∅, fun x => isEmptyElim x, isClosed_empty,
    fun x => isEmptyElim x, interior_empty, isClosed_empty, fun x => isEmptyElim x,
    interior_empty, by simp, fun x _ => isEmptyElim x, fun x _ => isEmptyElim x,
    fun y _ => isEmptyElim y⟩
  exact (continuous_of_discreteTopology (f := f)).isProperMap

end Basic

/-! ### Restriction over an open set -/

section Restrict

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The open preimage `c⁻¹(U)`. -/
def preOpen {c : Y → X} (hc : Continuous c) (U : Opens X) : Opens Y :=
  ⟨c ⁻¹' U, U.isOpen.preimage hc⟩

/-- The restriction `c⁻¹(U) → U`. -/
def restrictMap {c : Y → X} (hc : Continuous c) (U : Opens X) : preOpen hc U → U :=
  fun y => ⟨c y, y.2⟩

theorem interior_preimage_val_eq_empty {M : Type*} [TopologicalSpace M] (U : Opens M)
    {A : Set M} (hA : interior A = ∅) : interior (((↑) : U → M) ⁻¹' A) = ∅ := by
  have h := U.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    continuous_subtype_val (s := A)
  rw [hA, preimage_empty] at h
  exact h.symm

/-- **Restriction.** The restriction of a modification over an open set is a modification. -/
theorem isAnalyticModification_restrictMap {c : Y → X}
    (hc : IsAnalyticModification (n := n) c) (U : Opens X) :
    IsAnalyticModification (n := n) (restrictMap hc.1.continuous U) := by
  classical
  have hsurj := surjective_of_isAnalyticModification hc
  obtain ⟨A, B, s, hAc, hAa, hAi, hBc, hBa, hBi, hpre, hs, hright, hleft⟩ := hc.2.2
  let P := preOpen hc.1.continuous U
  -- the restricted inverse
  let s' : U → P := fun x =>
    if h : s x.1 ∈ P then ⟨s x.1, h⟩ else
      ⟨Classical.choose (hsurj x.1), by
        change c (Classical.choose (hsurj x.1)) ∈ U
        rw [Classical.choose_spec (hsurj x.1)]
        exact x.2⟩
  have hs'_eq : ∀ x : U, x.1 ∉ B → (s' x).1 = s x.1 := by
    intro x hx
    have hmem : s x.1 ∈ P := by
      change c (s x.1) ∈ U
      rw [hright x.1 hx]
      exact x.2
    simp only [s', dif_pos hmem]
  refine ⟨?_, ?_, ((↑) : P → Y) ⁻¹' A, ((↑) : U → X) ⁻¹' B, s', hAc.preimage continuous_subtype_val,
    isComplexAnalyticSubset_preimage_val hAa P, interior_preimage_val_eq_empty P hAi,
    hBc.preimage continuous_subtype_val, isComplexAnalyticSubset_preimage_val hBa U,
    interior_preimage_val_eq_empty U hBi, ?_, ?_, ?_, ?_⟩
  · intro y
    rw [← ContMDiffAt.subtypeVal_comp_iff]
    exact contMDiffAt_subtype_iff.mpr (hc.1 y.1)
  · exact hc.2.1.restrictPreimage (U : Set X)
  · ext y
    simp only [mem_preimage, restrictMap]
    rw [← mem_preimage (f := c), hpre]
  · intro x hx
    have hxB : x.1 ∉ B := hx
    have hopen : IsOpen (((↑) : U → X) ⁻¹' B)ᶜ := (hBc.preimage continuous_subtype_val).isOpen_compl
    refine (ContMDiffAt.contMDiffWithinAt ?_)
    rw [← ContMDiffAt.subtypeVal_comp_iff]
    have hev : (fun x : U => s x.1) =ᶠ[𝓝 x] (Subtype.val ∘ s') := by
      filter_upwards [hopen.mem_nhds hx] with z hz
      exact (hs'_eq z hz).symm
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hev.symm
    exact contMDiffAt_subtype_iff.mpr
      ((hs x.1 hxB).contMDiffAt (hBc.isOpen_compl.mem_nhds hxB))
  · intro x hx
    apply Subtype.ext
    change c (s' x).1 = x.1
    rw [hs'_eq x hx]
    exact hright x.1 hx
  · intro y hy
    have hyA : y.1 ∉ A := hy
    have hcy : c y.1 ∉ B := by
      intro h
      apply hyA
      rw [← hpre]
      exact h
    apply Subtype.ext
    exact (hs'_eq (restrictMap hc.1.continuous U y) hcy).trans (hleft y.1 hyA)

end Restrict

/-! ### Gluing over a clopen partition -/

section Glue

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]
  {ZP ZQ : Type u} [TopologicalSpace ZP] [ChartedSpace (ComplexModel n) ZP]
  [IsComplexManifold n ZP] [TopologicalSpace ZQ] [ChartedSpace (ComplexModel n) ZQ]
  [IsComplexManifold n ZQ]

instance instIsComplexManifoldSum : IsComplexManifold n (ZP ⊕ ZQ) where

/-- The glued map `ZP ⊕ ZQ → Y`. -/
def glueMap {P Q : Opens Y} (gP : ZP → P) (gQ : ZQ → Q) : ZP ⊕ ZQ → Y :=
  Sum.elim (fun z => (gP z).1) (fun z => (gQ z).1)

private theorem isComplexAnalyticSubset_sum {AP : Set ZP} {AQ : Set ZQ}
    (hAP : IsComplexAnalyticSubset (n := n) AP) (hAQ : IsComplexAnalyticSubset (n := n) AQ) :
    IsComplexAnalyticSubset (n := n) (Sum.inl '' AP ∪ Sum.inr '' AQ : Set (ZP ⊕ ZQ)) := by
  refine isComplexAnalyticSubset_of_forall_opens fun z => ?_
  cases z with
  | inl a =>
    let O : Opens (ZP ⊕ ZQ) := ⟨range Sum.inl, isOpen_range_inl⟩
    let ψ : O → ZP := fun w => Sum.elim id (fun _ => a) w.1
    have hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ :=
      (ContMDiff.sumElim contMDiff_id contMDiff_const).comp contMDiff_subtype_val
    refine ⟨O, ⟨a, rfl⟩, ?_⟩
    have heq : ((↑) ⁻¹' (Sum.inl '' AP ∪ Sum.inr '' AQ) : Set O) = ψ ⁻¹' AP := by
      ext ⟨w, b, rfl⟩
      simp [ψ]
    rw [heq]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hψ hAP
  | inr a =>
    let O : Opens (ZP ⊕ ZQ) := ⟨range Sum.inr, isOpen_range_inr⟩
    let ψ : O → ZQ := fun w => Sum.elim (fun _ => a) id w.1
    have hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ :=
      (ContMDiff.sumElim contMDiff_const contMDiff_id).comp contMDiff_subtype_val
    refine ⟨O, ⟨a, rfl⟩, ?_⟩
    have heq : ((↑) ⁻¹' (Sum.inl '' AP ∪ Sum.inr '' AQ) : Set O) = ψ ⁻¹' AQ := by
      ext ⟨w, b, rfl⟩
      simp [ψ]
    rw [heq]
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hψ hAQ

private theorem interior_sum_eq_empty {AP : Set ZP} {AQ : Set ZQ} (hAP : interior AP = ∅)
    (hAQ : interior AQ = ∅) : interior (Sum.inl '' AP ∪ Sum.inr '' AQ : Set (ZP ⊕ ZQ)) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro z hz
  have hO := isOpen_interior (s := (Sum.inl '' AP ∪ Sum.inr '' AQ : Set (ZP ⊕ ZQ)))
  cases z with
  | inl a =>
    have hsub : Sum.inl ⁻¹' interior (Sum.inl '' AP ∪ Sum.inr '' AQ : Set (ZP ⊕ ZQ)) ⊆ AP := by
      intro b hb
      have := interior_subset hb
      simpa using this
    have := interior_maximal hsub (hO.preimage continuous_inl)
    rw [hAP] at this
    exact this hz
  | inr a =>
    have hsub : Sum.inr ⁻¹' interior (Sum.inl '' AP ∪ Sum.inr '' AQ : Set (ZP ⊕ ZQ)) ⊆ AQ := by
      intro b hb
      have := interior_subset hb
      simpa using this
    have := interior_maximal hsub (hO.preimage continuous_inr)
    rw [hAQ] at this
    exact this hz

private theorem interior_image_val_eq_empty (U : Opens Y) {B : Set U} (hB : interior B = ∅) :
    interior (((↑) : U → Y) '' B) = ∅ := by
  apply eq_empty_of_forall_notMem
  intro y hy
  have hO := isOpen_interior (s := ((↑) : U → Y) '' B)
  have hyU : y ∈ U := by
    obtain ⟨b, -, rfl⟩ := interior_subset hy
    exact b.2
  have hsub : ((↑) : U → Y) ⁻¹' interior (((↑) : U → Y) '' B) ⊆ B := by
    intro b hb
    have := interior_subset hb
    rwa [Subtype.val_injective.mem_set_image] at this
  have := interior_maximal hsub (hO.preimage continuous_subtype_val)
  rw [hB] at this
  exact this (show (⟨y, hyU⟩ : U) ∈ ((↑) : U → Y) ⁻¹' interior (((↑) : U → Y) '' B) from hy)

/-- **Gluing.** Let `Y = P ⊔ Q` be a partition into two open (hence clopen) sets and let
`gP : ZP → P`, `gQ : ZQ → Q` be modifications of compact manifolds.  Then the glued map
`ZP ⊕ ZQ → Y` is a modification. -/
theorem isAnalyticModification_glueMap [CompactSpace ZP] [CompactSpace ZQ] {P Q : Opens Y}
    (hPQ : ∀ y, y ∈ P ↔ y ∉ Q) {gP : ZP → P} {gQ : ZQ → Q}
    (hgP : IsAnalyticModification (n := n) gP) (hgQ : IsAnalyticModification (n := n) gQ) :
    IsAnalyticModification (n := n) (glueMap gP gQ) := by
  classical
  obtain ⟨AP, BP, sP, hAPc, hAPa, hAPi, hBPc, hBPa, hBPi, hpreP, hsP, hrightP, hleftP⟩ := hgP.2.2
  obtain ⟨AQ, BQ, sQ, hAQc, hAQa, hAQi, hBQc, hBQa, hBQi, hpreQ, hsQ, hrightQ, hleftQ⟩ := hgQ.2.2
  have hPc : IsClosed (P : Set Y) := by
    have : (P : Set Y) = (Q : Set Y)ᶜ := by ext y; exact hPQ y
    rw [this]
    exact Q.isOpen.isClosed_compl
  have hQc : IsClosed (Q : Set Y) := by
    have : (Q : Set Y) = (P : Set Y)ᶜ := by ext y; simp [hPQ y]
    rw [this]
    exact P.isOpen.isClosed_compl
  have hBPimc : IsClosed (((↑) : P → Y) '' BP) :=
    hPc.isClosedEmbedding_subtypeVal.isClosedMap _ hBPc
  have hBQimc : IsClosed (((↑) : Q → Y) '' BQ) :=
    hQc.isClosedEmbedding_subtypeVal.isClosedMap _ hBQc
  let s : Y → ZP ⊕ ZQ := fun y =>
    if h : y ∈ P then Sum.inl (sP ⟨y, h⟩) else Sum.inr (sQ ⟨y, (hPQ y).not_left.mp h⟩)
  have hBmemP : ∀ y : P, (y : Y) ∈ ((↑) : P → Y) '' BP ∪ ((↑) : Q → Y) '' BQ ↔ y ∈ BP := by
    intro y
    constructor
    · rintro (⟨b, hb, hby⟩ | ⟨b, -, hby⟩)
      · rwa [← Subtype.ext hby]
      · exact absurd y.2 ((hPQ y).not.mpr (not_not.mpr (hby ▸ b.2)))
    · intro hy
      exact Or.inl ⟨y, hy, rfl⟩
  have hBmemQ : ∀ y : Q, (y : Y) ∈ ((↑) : P → Y) '' BP ∪ ((↑) : Q → Y) '' BQ ↔ y ∈ BQ := by
    intro y
    constructor
    · rintro (⟨b, -, hby⟩ | ⟨b, hb, hby⟩)
      · exact absurd y.2 ((hPQ y).mp (hby ▸ b.2))
      · rwa [← Subtype.ext hby]
    · intro hy
      exact Or.inr ⟨y, hy, rfl⟩
  refine ⟨ContMDiff.sumElim (contMDiff_subtype_val.comp hgP.1) (contMDiff_subtype_val.comp hgQ.1),
    ?_, Sum.inl '' AP ∪ Sum.inr '' AQ, ((↑) : P → Y) '' BP ∪ ((↑) : Q → Y) '' BQ, s,
    (isClosedMap_inl _ hAPc).union (isClosedMap_inr _ hAQc),
    isComplexAnalyticSubset_sum hAPa hAQa, interior_sum_eq_empty hAPi hAQi,
    hBPimc.union hBQimc,
    ConstantRankImage.IsComplexAnalyticSubset.union (isComplexAnalyticSubset_image_val hBPa hBPimc)
      (isComplexAnalyticSubset_image_val hBQa hBQimc), ?_, ?_, ?_, ?_, ?_⟩
  · exact (ContMDiff.sumElim (contMDiff_subtype_val.comp hgP.1)
      (contMDiff_subtype_val.comp hgQ.1)).continuous.isProperMap
  · rw [interior_union_isClosed_of_interior_empty hBPimc (interior_image_val_eq_empty Q hBQi)]
    exact interior_image_val_eq_empty P hBPi
  · ext z
    cases z with
    | inl a =>
      change ((gP a : Y) ∈ ((↑) : P → Y) '' BP ∪ ((↑) : Q → Y) '' BQ) ↔ _
      rw [hBmemP (gP a), ← mem_preimage (f := gP), hpreP]
      simp
    | inr a =>
      change ((gQ a : Y) ∈ ((↑) : P → Y) '' BP ∪ ((↑) : Q → Y) '' BQ) ↔ _
      rw [hBmemQ (gQ a), ← mem_preimage (f := gQ), hpreQ]
      simp
  · intro y hy
    refine (ContMDiffAt.contMDiffWithinAt ?_)
    by_cases hyP : y ∈ P
    · have hyB : (⟨y, hyP⟩ : P) ∉ BP := fun h => hy ((hBmemP ⟨y, hyP⟩).mpr h)
      have hfun : (fun x : P => s x) = fun x : P => Sum.inl (sP x) := by
        funext x
        simp only [s, dif_pos x.2]
      have hat : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
          (fun x : P => s x) ⟨y, hyP⟩ := by
        rw [hfun]
        exact ContMDiff.inl.contMDiffAt.comp _
          ((hsP _ hyB).contMDiffAt (hBPc.isOpen_compl.mem_nhds hyB))
      exact contMDiffAt_subtype_iff.mp hat
    · have hyQ : y ∈ Q := (hPQ y).not_left.mp hyP
      have hyB : (⟨y, hyQ⟩ : Q) ∉ BQ := fun h => hy ((hBmemQ ⟨y, hyQ⟩).mpr h)
      have hfun : (fun x : Q => s x) = fun x : Q => Sum.inr (sQ x) := by
        funext x
        have hx : (x : Y) ∉ P := (hPQ x).not.mpr (not_not.mpr x.2)
        simp only [s, dif_neg hx]
      have hat : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
          (fun x : Q => s x) ⟨y, hyQ⟩ := by
        rw [hfun]
        exact ContMDiff.inr.contMDiffAt.comp _
          ((hsQ _ hyB).contMDiffAt (hBQc.isOpen_compl.mem_nhds hyB))
      exact contMDiffAt_subtype_iff.mp hat
  · intro y hy
    by_cases hyP : y ∈ P
    · have hyB : (⟨y, hyP⟩ : P) ∉ BP := fun h => hy ((hBmemP ⟨y, hyP⟩).mpr h)
      simp only [s, dif_pos hyP, glueMap, Sum.elim_inl]
      exact congrArg Subtype.val (hrightP _ hyB)
    · have hyQ : y ∈ Q := (hPQ y).not_left.mp hyP
      have hyB : (⟨y, hyQ⟩ : Q) ∉ BQ := fun h => hy ((hBmemQ ⟨y, hyQ⟩).mpr h)
      simp only [s, dif_neg hyP, glueMap, Sum.elim_inr]
      exact congrArg Subtype.val (hrightQ _ hyB)
  · intro z hz
    cases z with
    | inl a =>
      have haA : a ∉ AP := fun h => hz (Or.inl ⟨a, h, rfl⟩)
      have hmem : (gP a : Y) ∈ P := (gP a).2
      simp only [glueMap, Sum.elim_inl, s, dif_pos hmem, Subtype.coe_eta, hleftP a haA]
    | inr a =>
      have haA : a ∉ AQ := fun h => hz (Or.inr ⟨a, h, rfl⟩)
      have hmem : (gQ a : Y) ∉ P := (hPQ _).not.mpr (not_not.mpr (gQ a).2)
      simp only [glueMap, Sum.elim_inr, s, dif_neg hmem, Subtype.coe_eta, hleftQ a haA]

end Glue

/-! ### Counting connected components -/

section Components

variable {X : Type u} [TopologicalSpace X]

/-- A nonempty proper clopen subset of a space with finitely many connected components has
strictly fewer connected components. -/
theorem card_connectedComponents_lt [Finite (ConnectedComponents X)] {U : Set X}
    (hU : IsClopen U) {p : X} (hp : p ∉ U) :
    Nat.card (ConnectedComponents U) < Nat.card (ConnectedComponents X) := by
  classical
  let f : ConnectedComponents U → ConnectedComponents X :=
    continuous_subtype_val.connectedComponentsMap
  have hsub : ∀ x : U, connectedComponent (x : X) ⊆ U := fun x =>
    hU.connectedComponent_subset x.2
  have hf : Function.Injective f := by
    intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have hxy : ConnectedComponents.mk (x : X) = ConnectedComponents.mk (y : X) := hab
    rw [ConnectedComponents.coe_eq_coe] at hxy
    rw [ConnectedComponents.coe_eq_coe]
    -- `y ∈ connectedComponent x` in `U`
    have hyX : (y : X) ∈ connectedComponent (x : X) := hxy ▸ mem_connectedComponent
    have hpre : IsPreconnected (((↑) : U → X) ⁻¹' connectedComponent (x : X)) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image,
        image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub x)]
      exact isPreconnected_connectedComponent
    exact connectedComponent_eq (hpre.subset_connectedComponent
      (show (x : X) ∈ connectedComponent (x : X) from mem_connectedComponent) hyX)
  have hnot : ConnectedComponents.mk p ∉ range f := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    have hx : ConnectedComponents.mk (x : X) = ConnectedComponents.mk p := ha
    rw [ConnectedComponents.coe_eq_coe'] at hx
    exact hp (hsub x ((connectedComponent_eq hx) ▸ (mem_connectedComponent : p ∈ _)))
  have : Finite (ConnectedComponents U) := Finite.of_injective f hf
  let := Fintype.ofFinite (ConnectedComponents U)
  let := Fintype.ofFinite (ConnectedComponents X)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_of_notMem f hf (fun h => hnot h)

end Components

/-! ### Common models over compact bases -/

private theorem common_model_aux (k : ℕ) :
    ∀ (X Y₀ Y₁ : Type u) [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
      [IsComplexManifold n X] [CompactSpace X]
      [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
      [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
      (c₀ : Y₀ → X) (c₁ : Y₁ → X), Nat.card (ConnectedComponents X) = k →
      IsAnalyticModification (n := n) c₀ → IsAnalyticModification (n := n) c₁ →
      ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
        (_ : IsComplexManifold n Z) (_ : CompactSpace Z) (g₀ : Z → Y₀) (g₁ : Z → Y₁),
        IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
          c₀ ∘ g₀ = c₁ ∘ g₁ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro X Y₀ Y₁ _ _ _ _ _ _ _ _ _ _ c₀ c₁ hk hc₀ hc₁
  have : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel n) X
  by_cases hpc : PreconnectedSpace X
  · by_cases hne : Nonempty X
    · have : ConnectedSpace X := ⟨hne⟩
      obtain ⟨Z, i₁, i₂, i₃, _, i₅, g₀, g₁, hg₀, hg₁, hcomm⟩ :=
        CompactSmoothCommonModel.exists_actual_compact_smooth_common_model hc₀ hc₁
      exact ⟨Z, i₁, i₂, i₃, i₅, g₀, g₁, hg₀, hg₁, hcomm⟩
    · rw [not_nonempty_iff] at hne
      have : IsEmpty Y₀ := ⟨fun y => isEmptyElim (c₀ y)⟩
      have : IsEmpty Y₁ := ⟨fun y => isEmptyElim (c₁ y)⟩
      refine ⟨Y₀, inferInstance, inferInstance, inferInstance, inferInstance, id,
        fun y => isEmptyElim y, isAnalyticModification_of_isEmpty _,
        isAnalyticModification_of_isEmpty _, ?_⟩
      funext y
      exact isEmptyElim y
  · rw [preconnectedSpace_iff_clopen] at hpc
    push Not at hpc
    obtain ⟨S, hS, hSne, hSuniv⟩ := hpc
    obtain ⟨q, hq⟩ := hSne
    obtain ⟨p, hp⟩ := (ne_univ_iff_exists_notMem S).mp hSuniv
    let U : Opens X := ⟨S, hS.isOpen⟩
    let V : Opens X := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
    have : CompactSpace U := isCompact_iff_compactSpace.mp hS.isClosed.isCompact
    have : CompactSpace V := isCompact_iff_compactSpace.mp hS.compl.isClosed.isCompact
    have hkU : Nat.card (ConnectedComponents U) < k :=
      hk ▸ card_connectedComponents_lt hS hp
    have hkV : Nat.card (ConnectedComponents V) < k :=
      hk ▸ card_connectedComponents_lt hS.compl (p := q) (fun h => h hq)
    obtain ⟨ZU, _, _, _, _, gU₀, gU₁, hgU₀, hgU₁, hcU⟩ :=
      ih _ hkU U (preOpen hc₀.1.continuous U) (preOpen hc₁.1.continuous U) (restrictMap hc₀.1.continuous U) (restrictMap hc₁.1.continuous U) rfl
        (isAnalyticModification_restrictMap hc₀ U) (isAnalyticModification_restrictMap hc₁ U)
    obtain ⟨ZV, _, _, _, _, gV₀, gV₁, hgV₀, hgV₁, hcV⟩ :=
      ih _ hkV V (preOpen hc₀.1.continuous V) (preOpen hc₁.1.continuous V) (restrictMap hc₀.1.continuous V) (restrictMap hc₁.1.continuous V) rfl
        (isAnalyticModification_restrictMap hc₀ V) (isAnalyticModification_restrictMap hc₁ V)
    refine ⟨ZU ⊕ ZV, inferInstance, inferInstance, inferInstance, inferInstance,
      glueMap gU₀ gV₀, glueMap gU₁ gV₁,
      isAnalyticModification_glueMap (fun y => by simp [preOpen, U, V]) hgU₀ hgV₀,
      isAnalyticModification_glueMap (fun y => by simp [preOpen, U, V]) hgU₁ hgV₁, ?_⟩
    funext z
    cases z with
    | inl a => exact congrArg Subtype.val (congrFun hcU a)
    | inr a => exact congrArg Subtype.val (congrFun hcV a)

/-- **Common models over compact complex manifolds.** Let `X` be a compact complex manifold (not
necessarily connected) and `c₀ : Y₀ → X`, `c₁ : Y₁ → X` modifications.  Then there are a compact
complex manifold `Z` and modifications `g₀ : Z → Y₀`, `g₁ : Z → Y₁` with `c₀ ∘ g₀ = c₁ ∘ g₁`. -/
theorem exists_compact_common_model {X Y₀ Y₁ : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    {c₀ : Y₀ → X} {c₁ : Y₁ → X} (hc₀ : IsAnalyticModification (n := n) c₀)
    (hc₁ : IsAnalyticModification (n := n) c₁) :
    ∃ (Z : Type u) (_ : TopologicalSpace Z) (_ : ChartedSpace (ComplexModel n) Z)
      (_ : IsComplexManifold n Z) (_ : CompactSpace Z) (g₀ : Z → Y₀) (g₁ : Z → Y₁),
      IsAnalyticModification (n := n) g₀ ∧ IsAnalyticModification (n := n) g₁ ∧
        c₀ ∘ g₀ = c₁ ∘ g₁ :=
  common_model_aux _ X Y₀ Y₁ c₀ c₁ rfl hc₀ hc₁

end SGPT.PSH.RIsoACommonModel
