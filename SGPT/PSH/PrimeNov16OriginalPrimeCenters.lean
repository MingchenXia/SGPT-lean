import SGPT.PSH.PrimeNov16OriginalPrimeQuotient
import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.AnalyticModificationDivisorStrictTransform

/-! Literal ENTIRE original strict-transform images and genuine quotient centres.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalPrimeCenters
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex
  HironakaReducedComplexAnalyticSpaces AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative
  OriginalSmoothSourceAnalytic
open PrimeNov16OriginalHypersurface PrimeNov16OriginalStrictTransform
  PrimeNov16OriginalPrimePresentation PrimeNov16OriginalPrimeQuotient

theorem image_original_strictTransform
    {Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (G : S ⟶ Y) (hG : IsProperBimeromorphic G) {E : Set Y.obj.left}
    (hE : IsOriginalHypersurface Y E) :
    G.hom.left.base '' originalStrictTransform G E = E := by
  obtain ⟨cY, n, M, IY, k, hD, hcodim, himage⟩ := exists_actual_native_hypersurface hY hE
  let JY := IY.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY cY
  let D := pointMap JY ⁻¹' E
  have hEc : E ⊆ OriginalSmoothComponents.componentSet cY := by
    intro y hy
    have hym := himage.symm ▸ hy
    obtain ⟨z, _hz, rfl⟩ := hym
    exact (IY.hom.hom.left.base ⟨z, mem_univ z⟩).property
  obtain ⟨cS, N, IS, F, hF, hsq⟩ :=
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hS hY G hG cY M IY
  let JS := IS.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS
  let f := nativePointMap F
  have hmod := isAnalyticModification_of_isProperBimeromorphic F hF
  have hnative : nativeMorphism hmod.1 = F := nativeMorphism_nativePointMap F
  have hfull : nativeMorphism hmod.1 ≫ JY = IS.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS cS ≫ G := by
    rw [hnative]
    exact hsq
  have hstrict := original_strictTransform_eq_native_image hS hY G hG cS cY N M IS IY f hmod hfull E hEc
  obtain ⟨V, hV, hdV⟩ := SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hD
  have hVdim : V.dim+1=n := by rw [hdV]; exact hcodim
  obtain ⟨W, hW, _hdW, hImg, _hReader⟩ := AnalyticModificationDivisorStrictTransform.exists_strictTransform_reader hmod V hVdim
  have hcarrier : strictTransform n f D = W.carrier :=
    (congrArg (strictTransform n f) hV).symm.trans hW.symm
  have hNativeImage : f '' strictTransform n f D = D :=
    (congrArg (fun A => f '' A) hcarrier).trans (hImg.trans hV)
  have hpoint (z : N) : pointMap JY (f z) = G.hom.left.base (pointMap JS z) :=
    congrArg (fun K : wholeModel (n := n) N ⟶ Y => K.hom.left.base ⟨z, mem_univ z⟩) hsq
  calc
    _ = G.hom.left.base '' (pointMap JS '' strictTransform n f D) := congrArg (fun A => G.hom.left.base '' A) hstrict
    _ = (G.hom.left.base ∘ pointMap JS) '' strictTransform n f D := image_image _ _ _
    _ = (pointMap JY ∘ f) '' strictTransform n f D :=
      congrArg (fun h => h '' strictTransform n f D) (funext (fun z => (hpoint z).symm))
    _ = pointMap JY '' (f '' strictTransform n f D) := (image_image (pointMap JY) f (strictTransform n f D)).symm
    _ = pointMap JY '' D := congrArg (fun A => pointMap JY '' A) hNativeImage
    _ = E := himage

theorem presentationCenter_eq_of_commonResolution
    {X : SourceReducedComplexSpace} {p q : PrimePresentation X} (h : CommonResolutionGeometry p q) :
    presentationCenter p = presentationCenter q := by
  have hp := image_original_strictTransform h.smooth p.smooth h.left h.left_modification p.hypersurface
  have hq := image_original_strictTransform h.smooth q.smooth h.right h.right_modification q.hypersurface
  calc
    _ = p.projection.hom.left.base '' (h.left.hom.left.base '' originalStrictTransform h.left p.divisor) :=
      congrArg (fun A => p.projection.hom.left.base '' A) hp.symm
    _ = (h.left ≫ p.projection).hom.left.base '' originalStrictTransform h.left p.divisor := image_image _ _ _
    _ = (h.right ≫ q.projection).hom.left.base '' originalStrictTransform h.right q.divisor :=
      congrArg₂ (fun (F : h.model ⟶ X) A => F.hom.left.base '' A) h.over_base h.strict_equal
    _ = q.projection.hom.left.base '' (h.right.hom.left.base '' originalStrictTransform h.right q.divisor) :=
      (image_image q.projection.hom.left.base h.right.hom.left.base (originalStrictTransform h.right q.divisor)).symm
    _ = presentationCenter q := congrArg (fun A => q.projection.hom.left.base '' A) hq

variable {X : SourceReducedComplexSpace}

def center : PrimeOver X → Set X.obj.left :=
  Quot.lift presentationCenter (by
    intro p q hpq
    obtain ⟨h⟩ := hpq
    exact presentationCenter_eq_of_commonResolution h)

theorem center_mk (p : PrimePresentation X) :
    center (Quot.mk commonResolutionRelation p) = presentationCenter p := rfl

def weightedCenter (p : WeightedPrimeOver X) : Set X.obj.left := center p.2

end SGPT.PSH.PrimeNov16OriginalPrimeCenters
