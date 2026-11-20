import SGPT.Trace.BertiniOriginalFullBaseHodgeLowerSemicontinuity
import SGPT.Trace.BertiniNativeQuotientHodge

/-! Actual native multiplier quotient frames and FULL affine-base Hodge LSC. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem nativeBertiniPhysicalQuotientHodgeEnergy_combination (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)) (m : ℕ)
    (S : Fin m → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
    (v : Fin m → ℂ) :
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ
      (∑ j, v j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ (S j)) =
    nativeBertiniAdjunctionHodgeEnergy p i ζ hsm L φ
      (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L)
        (fun j => NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) (S j).val) v) := by
  classical
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let K := nativeCanonicalBundle (n := d + 1) (X := X)
  let P := nativeBertiniHyperplaneBundle p
  let A := tensor (tensor K L) P
  let B := tensor (tensor K P) L
  let W := fullHolomorphicIdealSections (n := d + 1) B.Fiber (sourceDegreeMultiplierIdeal 1 φ)
  let F : nativeMultiplierSections A φ →ₗ[ℂ] HolomorphicSections (n := d + 1) B.Fiber :=
    W.subtype.comp (nativeMultiplierSwapLastSectionMap K L P hφ)
  let Q := (nativeMultiplierSectionMap (tensor K L) P hφ (nativeBertiniAffineSection p i ζ)).range
  have hQ : (∑ j, v j • Q.mkQ (S j)) = Q.mkQ (∑ j, v j • S j) := by
    rw [map_sum]
    simp only [map_smul]
  change nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (∑ j, v j • Q.mkQ (S j)) = _
  rw [hQ,nativeBertiniPhysicalQuotientHodgeEnergy_mk]
  have hsum : NativeTensorSwap.swapLastSection K L P (∑ j, v j • S j).val =
      nativeSectionCombination B (fun j => NativeTensorSwap.swapLastSection K L P (S j).val) v := by
    change F (∑ j, v j • S j) = nativeSectionCombination B (fun j => F (S j)) v
    rw [map_sum]
    simp only [map_smul,nativeSectionCombination]
  rw [hsum]

theorem exists_native_fullBase_quotient_frame_hodge_lowerSemicontinuity [ConnectedSpace X]
    (ℓ₀ : HyperplaneSpace N) (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀)
    (hproper : ∃ x : X, x ∉ member p ℓ₀) :
    ∃ (r : ℕ) (S : Fin r → nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (V : TopologicalSpace.Opens (ComplexModel N)) (_hV : affineChart (chartIndex ℓ₀) ℓ₀ ∈ V)
      (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val)),
      (∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ),
        ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) ζ.val)).range.mkQ (S j)) ∧
      LowerSemicontinuous (fun q : (Fin r → ℂ) × V =>
        nativeBertiniPhysicalQuotientHodgeEnergy p (chartIndex ℓ₀) q.2.val (hsV q.2) L hφ
          (∑ j, q.1 j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
            (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) q.2.val)).range.mkQ (S j))) := by
  classical
  let i := chartIndex ℓ₀
  let a := affineChart i ℓ₀
  have hℓ : affinePoint i a = ℓ₀ := (affineChart i).left_inv (mem_affineChart_chartIndex ℓ₀)
  obtain ⟨V₀,haV₀,hs₀,hjoint⟩ := exists_original_fullBase_adjunctionHodge_lowerSemicontinuity p hφ.1 ℓ₀ hsm₀
  obtain ⟨r,S,W,hW,haW,hframe⟩ := exists_nativeBertiniHyperplane_quotientBasis p
    (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) hφ i a
    (by simpa only [hℓ] using hproper)
  let V : TopologicalSpace.Opens (ComplexModel N) := ⟨(V₀ : Set _) ∩ W,V₀.isOpen.inter hW⟩
  let hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ.val) :=
    fun ζ => hs₀ ⟨ζ.val,ζ.property.1⟩
  refine ⟨r,S,V,⟨haV₀,haW⟩,hsV,?_,?_⟩
  · intro ζ
    exact hframe ζ.val ζ.property.2
  · let B := tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L
    let H : Fin r → HolomorphicSections (n := d + 1) B.Fiber :=
      fun j => NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
        (nativeBertiniHyperplaneBundle p) (S j).val
    let F : ((Fin r → ℂ) × V) → ((Fin r → ℂ) × V₀) := fun q => (q.1,⟨q.2.val,q.2.property.1⟩)
    have hF : Continuous F := continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    have hl := (hjoint L r H).comp hF
    have heq : (fun q : (Fin r → ℂ) × V =>
        nativeBertiniPhysicalQuotientHodgeEnergy p i q.2.val (hsV q.2) L hφ
          (∑ j, q.1 j • (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
            (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i q.2.val)).range.mkQ (S j))) =
        (fun q : (Fin r → ℂ) × V => nativeBertiniAdjunctionHodgeEnergy p i q.2.val (hsV q.2) L φ (nativeSectionCombination B H q.1)) := by
      funext q
      exact nativeBertiniPhysicalQuotientHodgeEnergy_combination p L hφ i q.2.val (hsV q.2) r S q.1
    rw [heq]
    exact hl

end SGPT.Trace.Bertini
