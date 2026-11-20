import SGPT.PSH.PrimeNov16OriginalComponentPreimage
import SGPT.Foundations.Analysis.Pending.AnalyticModificationSingletonFibreInverse
import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalFibres

/-! ENTIRE original fibres, actual component preimages and native critical loci.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalFibreDictionary
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

variable {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
  (G : S ⟶ Y) (hG : IsProperBimeromorphic G)
  (cS : ConnectedComponents S.obj.left) (cY : ConnectedComponents Y.obj.left)
  {n : ℕ} (N M : CMfd n)
  (I₀ : wholeModel (n := n) N ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hS cS)
  (I₁ : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY cY)
  (f : N → M) (hf : IsAnalyticModification (n := n) f)
  (hfull : nativeMorphism hf.1 ≫ (I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY) =
    I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G)

include hG hfull

theorem component_preimage_eq_of_actual_native_lift :
    G.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet cY = OriginalSmoothComponents.componentSet cS := by
  obtain ⟨pair, hpair⟩ := PrimeNov16OriginalComponentPreimage.exists_actual_component_preimage_pairing hS hY G hG
  let H₀ : N ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    (Homeomorph.Set.univ N).symm.trans (isoHomeomorph I₀)
  let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected cS)
  let : ConnectedSpace N := H₀.connectedSpace_iff.mpr inferInstance
  obtain ⟨x⟩ := (inferInstance : Nonempty N)
  let J₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let J₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  have hpoint : pointMap J₁ (f x) = G.hom.left.base (pointMap J₀ x) :=
    congrArg (fun F : wholeModel (n := n) N ⟶ Y => F.hom.left.base ⟨x, mem_univ x⟩) hfull
  have htarget : G.hom.left.base (pointMap J₀ x) ∈ OriginalSmoothComponents.componentSet cY :=
    hpoint ▸ (I₁.hom.hom.left.base ⟨f x, mem_univ _⟩).property
  have hsource : pointMap J₀ x ∈ OriginalSmoothComponents.componentSet cS :=
    (I₀.hom.hom.left.base ⟨x, mem_univ x⟩).property
  have hpaired : pointMap J₀ x ∈ OriginalSmoothComponents.componentSet (pair cY) := hpair cY ▸ htarget
  have hc : cS = pair cY := hsource.symm.trans hpaired
  exact (hpair cY).trans (congrArg OriginalSmoothComponents.componentSet hc.symm)

theorem singleton_fibre_iff_native (x : N) :
    (∀ t : S.obj.left,
      G.hom.left.base t = G.hom.left.base (pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) x) →
      t = pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) x) ↔
    ∀ z : N, f z = f x → z = x := by
  let J₀ := I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let J₁ := I₁.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let H₀ : N ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left :=
    (Homeomorph.Set.univ N).symm.trans (isoHomeomorph I₀)
  let H₁ : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY cY).obj.left :=
    (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I₁)
  have hinj₀ : Function.Injective (pointMap J₀) := fun a b h => H₀.injective (Subtype.ext h)
  have hinj₁ : Function.Injective (pointMap J₁) := fun a b h => H₁.injective (Subtype.ext h)
  have hpoint (z : N) : pointMap J₁ (f z) = G.hom.left.base (pointMap J₀ z) :=
    congrArg (fun F : wholeModel (n := n) N ⟶ Y => F.hom.left.base ⟨z, mem_univ z⟩) hfull
  have hpre := component_preimage_eq_of_actual_native_lift hS hY G hG cS cY N M I₀ I₁ f hf hfull
  constructor
  · intro hsingle z hz
    apply hinj₀
    apply hsingle
    exact (hpoint z).symm.trans ((congrArg (pointMap J₁) hz).trans (hpoint x))
  · intro hsingle t ht
    have htarget : G.hom.left.base t ∈ OriginalSmoothComponents.componentSet cY := by
      exact ht.symm ▸ ((hpoint x) ▸ (H₁ (f x)).property)
    have htc : t ∈ OriginalSmoothComponents.componentSet cS := hpre ▸ htarget
    let p : (HironakaG1NoncompactSmoothComponentModel.componentObject hS cS).obj.left := ⟨t, htc⟩
    let z := H₀.symm p
    have hz : pointMap J₀ z = t := congrArg Subtype.val (H₀.apply_symm_apply p)
    have hfib : f z = f x := hinj₁ ((hpoint z).trans
      ((congrArg G.hom.left.base hz).trans (ht.trans (hpoint x).symm)))
    exact hz.symm.trans (congrArg (pointMap J₀) (hsingle z hfib))

theorem not_mem_exceptional_iff_original_singleton (x : N) :
    x ∉ exceptionalLocus n f ↔ ∀ t : S.obj.left,
      G.hom.left.base t = G.hom.left.base (pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) x) →
      t = pointMap (I₀.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS) x := by
  rw [singleton_fibre_iff_native hS hY G hG cS cY N M I₀ I₁ f hf hfull x]
  exact ⟨fun hx z hz => AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hf hx hz,
    AnalyticModificationSingletonFibreInverse.not_mem_exceptionalLocus_of_unique_fibre hf x⟩

end SGPT.PSH.PrimeNov16OriginalFibreDictionary
