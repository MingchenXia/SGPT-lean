import SGPT.Trace.BertiniPhysicalQuotientRestriction
import SGPT.Trace.BertiniHodgeSemicontinuity

/-! Intrinsic Hodge energy on the LITERAL original native multiplier quotient.
Its exact kernel is the genuine restriction kernel; no all-member exactness. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

abbrev NativeBertiniMultiplierQuotient :=
  (nativeMultiplierSections
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ) ⧸
    (nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
      (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range

def nativeBertiniPhysicalQuotientHodgeEnergy :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    NativeBertiniMultiplierQuotient p i ζ L hφ → ℝ≥0∞ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  exact fun q => nativeBertiniMemberHodgeEnergy p i ζ hsm L φ
    (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q)

theorem nativeBertiniPhysicalQuotientHodgeEnergy_mk
    (S : nativeMultiplierSections
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ
      ((nativeMultiplierSectionMap (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L)
        (nativeBertiniHyperplaneBundle p) hφ (nativeBertiniAffineSection p i ζ)).range.mkQ S) =
      nativeBertiniAdjunctionHodgeEnergy p i ζ hsm L φ
        (NativeTensorSwap.swapLastSection (nativeCanonicalBundle (n := d + 1) (X := X)) L
          (nativeBertiniHyperplaneBundle p) S.val) := rfl

private theorem actualQuotientMemberHodgeZero :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    nativeBertiniMemberHodgeEnergy p i ζ hsm L φ 0 = 0 := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)
  have h := nativePhysicalHodgeEnergy_smul LH (fun _ => 0) (fun y => multiplierWeight 1 (φ y.val)) (0 : ℂ)
  have hzero : (0 : ℂ) • (fun y => (0 : (tensor
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ))) LH).Fiber y)) =
      (fun y => (0 : (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ))) LH).Fiber y)) := by
    funext y
    exact zero_smul ℂ (0 : (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ))) LH).Fiber y)
  rw [hzero] at h
  change nativePhysicalHodgeEnergy LH (fun _ => 0) (fun y => multiplierWeight 1 (φ y.val)) = 0
  simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul] using h

theorem nativeBertiniPhysicalQuotientHodgeEnergy_eq_zero_iff :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q = 0 ↔
        nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q = 0 := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro q
  constructor
  · intro hzero
    by_contra hnonzero
    have hpos := nativeBertiniMemberHodgeEnergy_pos p i ζ hsm L hφ.1
      (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q) hnonzero
    exact hpos.ne' hzero
  · intro hzero
    unfold nativeBertiniPhysicalQuotientHodgeEnergy
    rw [hzero]
    exact actualQuotientMemberHodgeZero p i ζ hsm L

theorem nativeBertiniPhysicalQuotientHodgeEnergy_pos_iff :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
      0 < nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q ↔
        nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q ≠ 0 := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro q
  constructor
  · intro hpos hzero
    exact hpos.ne' ((nativeBertiniPhysicalQuotientHodgeEnergy_eq_zero_iff p i ζ hsm L hφ q).mpr hzero)
  · intro hnonzero
    exact nativeBertiniMemberHodgeEnergy_pos p i ζ hsm L hφ.1
      (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q) hnonzero

theorem nativeBertiniPhysicalQuotientHodgeEnergy_finite_iff :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ,
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q < ⊤ ↔
        nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q ∈ fullHolomorphicIdealSections (n := d)
          (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
            (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
          (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro q
  exact (nativeBertiniMemberHodgeEnergy_finite_iff_full_originalIdeal_allDimensions p i ζ hsm L hφ.1
    (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ q)).symm

theorem nativeBertiniPhysicalQuotientHodgeEnergy_positive_iff_injective :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (∀ q : NativeBertiniMultiplierQuotient p i ζ L hφ, q ≠ 0 →
      0 < nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ q) ↔
      Function.Injective (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let R := nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
  constructor
  · intro hpos q₁ q₂ hR
    by_contra hne
    have hrzero : R (q₁ - q₂) = 0 := by rw [map_sub,hR,sub_self]
    have hezero := (nativeBertiniPhysicalQuotientHodgeEnergy_eq_zero_iff p i ζ hsm L hφ (q₁ - q₂)).mpr hrzero
    exact (hpos (q₁ - q₂) (sub_ne_zero.mpr hne)).ne' hezero
  · intro hR q hq
    apply (nativeBertiniPhysicalQuotientHodgeEnergy_pos_iff p i ζ hsm L hφ q).mpr
    intro hzero
    exact hq (hR (hzero.trans (map_zero R).symm))

end SGPT.Trace.Bertini
