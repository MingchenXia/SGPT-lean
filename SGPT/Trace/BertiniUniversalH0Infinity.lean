import SGPT.Trace.BertiniUniversalH0Range
import SGPT.Trace.BertiniNativeQuotientHodge

/-! Actual intrinsic original multiplier H0 is the restriction image at
an ENTIRE finite literal original quotient fibre, uniformly in H/twists.
The finite-fibre condition remains explicit for the generic metric consumer. -/
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
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

theorem exists_uniform_original_quotient_intrinsicH0_finite_iff
    (G : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k → ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
        (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)),
      letI := nativeBertiniMemberChartedSpace p i ζ hsm
      letI := nativeBertiniMemberComplex p i ζ hsm
      letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
      let L := twistedPower G U k
      let R := nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
      let M := fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))
      (R.range = M ↔ ∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
        nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q < ⊤) ∧
      (R.range ≠ M ↔ ∃ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
        nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q = ⊤) := by
  classical
  obtain ⟨k₀,hk₀,hRange⟩ := exists_uniform_original_quotient_intrinsicH0_range p G hG hGpos φ hφ
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hk i ζ hsm
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro L R M
  have hiff : R.range = M ↔ ∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q < ⊤ := by
    constructor
    · intro heq q
      apply (nativeBertiniPhysicalQuotientHodgeEnergy_finite_iff p i ζ hsm L hφ q).mpr
      change R q ∈ M
      rw [← heq]
      exact ⟨q,rfl⟩
    · exact hRange U hU hUpos k hk i ζ hsm
  refine ⟨hiff,?_⟩
  constructor
  · intro hne
    by_contra hno
    apply hne
    apply hiff.mpr
    intro q
    by_contra hq
    exact hno ⟨q,le_antisymm le_top (le_of_not_gt hq)⟩
  · rintro ⟨q,hq⟩ heq
    exact ((hiff.mp heq) q).ne hq

end SGPT.Trace.BertiniUniversal
