import SGPT.Trace.BertiniUniversalFrameAE

/-! Produced genuine original quotient bases and dense ENTIRE finite
intrinsic Hodge fibres, with actual AE finiteness manufactured internally. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem exists_original_fullBase_entire_quotient_finite_fibres
    (ℓ₀ : HyperplaneSpace (k + 1)) (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀)
    (hproper : ∃ x : X, x ∉ member p ℓ₀)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) :
    ∃ (r : ℕ) (S : Fin r → nativeMultiplierSections
        (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
      (V : TopologicalSpace.Opens (ComplexModel (k + 1))) (_hV : affineChart (chartIndex ℓ₀) ℓ₀ ∈ V)
      (hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val)),
      (∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ),
        ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
          (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) ζ.val)).range.mkQ (S j)) ∧
      ∀ U : TopologicalSpace.Opens (ComplexModel (k + 1)), U ≤ V → (U : Set (ComplexModel (k + 1))).Nonempty →
        ∃ ζ : V, ζ.val ∈ U ∧ ∀ q : NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ,
          nativeBertiniPhysicalQuotientHodgeEnergy p (chartIndex ℓ₀) ζ.val (hsV ζ) L hφ q ≠ ⊤ := by
  obtain ⟨r,S,W,hW,hsW,hBasis,_hLSC⟩ :=
    exists_native_fullBase_quotient_frame_hodge_lowerSemicontinuity p L hφ ℓ₀ hsm₀ hproper
  obtain ⟨V,hV,hVW,hAE⟩ := exists_original_fullBase_quotientFrame_ae_finite p hφ ℓ₀ hsm₀ W hW hsW
  let hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val) :=
    fun ζ => hsW ⟨ζ.val,hVW ζ.property⟩
  have hb : ∀ ζ : V, ∃ b : Module.Basis (Fin r) ℂ (NativeBertiniMultiplierQuotient p (chartIndex ℓ₀) ζ.val L hφ),
      ∀ j, b j = (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p (chartIndex ℓ₀) ζ.val)).range.mkQ (S j) :=
    fun ζ => hBasis ⟨ζ.val,hVW ζ.property⟩
  refine ⟨r,S,V,hV,hsV,hb,?_⟩
  intro U hUV hU
  exact exists_native_quotient_finite_fibre_in_open_of_ae_frame p (chartIndex ℓ₀) V hsV L hφ S hb
    (hAE L r S μ hμ) U hUV hU

end SGPT.Trace.BertiniUniversal
