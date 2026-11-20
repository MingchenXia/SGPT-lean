import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeInclusion
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction

/-! Exact actual ambient range window of an original carrier-open inclusion.
Blueprint: prime-nov16-analytic-normalization-original-native-open-image.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenImage
open PrimeNov16AnalyticNormalizationOriginalNativeInclusion
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

variable {n : ℕ} (U W : Opens (ComplexModel n)) {C : Set U} {D : Set W}
  (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D)
  (hUW : U ≤ W) (hCD : ∀ c : C,(⟨c.val.val,hUW c.val.property⟩ : W) ∈ D)
  (V : Opens (sourceReducedComplexSpaceModel U C hC).obj.left) [ParacompactSpace V]

def openNativeMap : restrictedBase V ⟶ sourceReducedComplexSpaceModel W D hD :=
  baseInclusion V ≫ nativeInclusion U W hC hD hUW hCD

theorem openNativeMap_point (v : V) :
    ((openNativeMap U W hC hD hUW hCD V).hom.left.base v).val.val=v.val.val.val :=
  nativeInclusion_point U W hC hD hUW hCD v.val

theorem openNativeMap_embedding :
    Topology.IsEmbedding (openNativeMap U W hC hD hUW hCD V).hom.left.base :=
  (nativeInclusion_embedding U W hC hD hUW hCD).comp
    (baseInclusion_isOpenImmersion V).base_open.isEmbedding

theorem exists_actual_ambient_range_window (c0 : V) :
    ∃ O : Set (ComplexModel n),IsOpen O ∧ c0.val.val.val ∈ O ∧ O ⊆ (U : Set (ComplexModel n)) ∧
      ∀ b : D,b.val.val ∈ O →
        (b ∈ range (openNativeMap U W hC hD hUW hCD V).hom.left.base ↔
          b.val.val ∈ (Subtype.val : U → ComplexModel n) '' C) := by
  let V0 : Set C := fun c => (show (sourceReducedComplexSpaceModel U C hC).obj.left from c) ∈ V
  have hVC : IsOpen V0 := V.isOpen
  obtain ⟨O0,hO0,hO0V⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hVC
  obtain ⟨O,hO,hOO0⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hO0
  let c : C := c0.val
  have hcO0 : c.val ∈ O0 := by
    change c ∈ Subtype.val ⁻¹' O0
    rw [hO0V]
    exact c0.property
  have hcO : c.val.val ∈ O := by
    exact (show c.val ∈ (Subtype.val : U → ComplexModel n) ⁻¹' O from hOO0.symm ▸ hcO0)
  refine ⟨O ∩ U,hO.inter U.isOpen,⟨hcO,c0.val.val.property⟩,inter_subset_right,?_⟩
  intro b hb
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨v.val.val,v.val.property,(openNativeMap_point U W hC hD hUW hCD V v).symm⟩
  · rintro ⟨u,hu,he⟩
    have huO : u.val ∈ O := he.symm ▸ hb.1
    have huO0 : u ∈ O0 := by
      rw [← hOO0]
      exact huO
    have hcV : (show (sourceReducedComplexSpaceModel U C hC).obj.left from (⟨u,hu⟩ : C)) ∈ V := by
      change (⟨u,hu⟩ : C) ∈ V0
      rw [← hO0V]
      exact huO0
    refine ⟨⟨⟨u,hu⟩,hcV⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact (openNativeMap_point U W hC hD hUW hCD V _).trans he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenImage
