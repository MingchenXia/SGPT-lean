import SGPT.PSH.PrimeNov16OriginalFibreDictionary
import SGPT.PSH.PrimeNov16OriginalComponentClosure

/-! Intrinsic ENTIRE-fibre strict transforms and literal ENTIRE original closure.
The actual fibre dictionary derives the differential exceptional comparison.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalStrictTransform
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

/-- The intrinsic singleton ENTIRE original fibre locus. -/
def singletonLocus {S Y : SourceReducedComplexSpace} (G : S ⟶ Y) : Set S.obj.left :=
  {x | ∀ t : S.obj.left, G.hom.left.base t = G.hom.left.base x → t = x}

/-- Literal closure in the ENTIRE original source. For actual smooth-source PB
maps the actual fibre dictionary proves this is the differential strict transform. -/
def originalStrictTransform {S Y : SourceReducedComplexSpace} (G : S ⟶ Y) (E : Set Y.obj.left) : Set S.obj.left :=
  closure (G.hom.left.base ⁻¹' E ∩ singletonLocus G)

variable {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
  (G : S ⟶ Y) (hG : IsProperBimeromorphic G)
  (cS : ConnectedComponents S.obj.left) (cY : ConnectedComponents Y.obj.left)
  {n : ℕ} (N M : CMfd n)
  (I₀ : wholeModel (n := n) N ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS cS)
  (I₁ : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY cY)
  (f : N → M) (hf : IsAnalyticModification (n := n) f)
  (hfull : nativeMorphism hf.1 ≫ (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
    I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G)
  (E : Set Y.obj.left) (hEc : E ⊆ OriginalSmoothComponents.componentSet cY)

include hG hfull hEc

theorem original_strictTransform_eq_native_image :
    originalStrictTransform G E =
      pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) ''
        strictTransform n f (pointMap (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) ⁻¹' E) := by
  let J₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let J₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let H₀ : N ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    (Homeomorph.Set.univ N).symm.trans (isoHomeomorph I₀)
  let A := G.hom.left.base ⁻¹' E ∩ singletonLocus G
  let B := f ⁻¹' (pointMap J₁ ⁻¹' E) \ exceptionalLocus n f
  have hpoint (z : N) : pointMap J₁ (f z) = G.hom.left.base (pointMap J₀ z) :=
    congrArg (fun F : wholeModel (n := n) N ⟶ Y => F.hom.left.base ⟨z, mem_univ z⟩) hfull
  have hpre := PrimeNov16OriginalFibreDictionary.component_preimage_eq_of_actual_native_lift
    hS hY G hG cS cY N M I₀ I₁ f hf hfull
  have hgood : A = pointMap J₀ '' B := by
    ext t
    constructor
    · intro ht
      have htc : t ∈ OriginalSmoothComponents.componentSet cS := hpre ▸ hEc ht.1
      let p : (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left := ⟨t, htc⟩
      let z := H₀.symm p
      have hz : pointMap J₀ z = t := congrArg Subtype.val (H₀.apply_symm_apply p)
      refine ⟨z, ⟨?_, ?_⟩, hz⟩
      · change pointMap J₁ (f z) ∈ E
        exact (hpoint z).symm ▸ ((congrArg G.hom.left.base hz).symm ▸ ht.1)
      · apply (PrimeNov16OriginalFibreDictionary.not_mem_exceptional_iff_original_singleton
          hS hY G hG cS cY N M I₀ I₁ f hf hfull z).mpr
        intro u hu
        have hut : G.hom.left.base u = G.hom.left.base t := hu.trans (congrArg G.hom.left.base hz)
        exact (ht.2 u hut).trans hz.symm
    · rintro ⟨z, hz, rfl⟩
      have htE : G.hom.left.base (pointMap J₀ z) ∈ E :=
        Eq.mp (congrArg (fun y : Y.obj.left => y ∈ E) (hpoint z)) hz.1
      refine ⟨htE, ?_⟩
      exact (PrimeNov16OriginalFibreDictionary.not_mem_exceptional_iff_original_singleton
        hS hY G hG cS cY N M I₀ I₁ f hf hfull z).mp hz.2
  change closure A = pointMap J₀ '' closure B
  exact (congrArg closure hgood).trans
    (PrimeNov16OriginalComponentClosure.closure_native_component_image hS cS N I₀ B)

theorem original_strictTransform_absent_other_components
    (d : ConnectedComponents S.obj.left) (hcd : cS ≠ d) :
    Disjoint (originalStrictTransform G E) (OriginalSmoothComponents.componentSet d) := by
  let B := f ⁻¹' (pointMap (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) ⁻¹' E) \ exceptionalLocus n f
  have heq : originalStrictTransform G E =
      closure (pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) '' B) :=
    (original_strictTransform_eq_native_image hS hY G hG cS cY N M I₀ I₁ f hf hfull E hEc).trans
      (PrimeNov16OriginalComponentClosure.closure_native_component_image hS cS N I₀ B).symm
  exact heq.symm ▸ PrimeNov16OriginalComponentClosure.disjoint_closure_image_other_component hS cS d hcd N I₀ B

end SGPT.PSH.PrimeNov16OriginalStrictTransform
