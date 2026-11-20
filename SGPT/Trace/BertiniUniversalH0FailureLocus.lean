import SGPT.Trace.BertiniUniversalH0Infinity
import SGPT.Trace.BertiniNativeQuotientInfiniteLocus

/-! Actual original intrinsic multiplier-H0 image failure is EXACTLY the
same native quotient infinity locus after ONE uniform auxiliary twist. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology ENNReal TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft SGPT.Trace.Bertini
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

def originalIntrinsicH0ImageFailureLocus (i : Fin (N + 1))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) : Set (ComplexModel N) :=
  {ζ | ∃ hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ),
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ).range ≠
      fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))}

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_uniform_original_intrinsicH0_failure_locus_eq_infinite
    (G : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k → ∀ i : Fin (N + 1),
      originalIntrinsicH0ImageFailureLocus p i (twistedPower G U k) hφ =
        nativeBertiniQuotientInfiniteLocus p i (twistedPower G U k) hφ := by
  obtain ⟨k₀,hk₀,hAll⟩ := exists_uniform_original_quotient_intrinsicH0_finite_iff p G hG hGpos φ hφ
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hk i
  ext ζ
  exact exists_congr (fun hsm => (hAll U hU hUpos k hk i ζ hsm).2)

end SGPT.Trace.BertiniUniversal
