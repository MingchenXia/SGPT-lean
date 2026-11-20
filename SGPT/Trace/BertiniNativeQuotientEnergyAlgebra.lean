import SGPT.Trace.BertiniNativeQuotientHodge
import SGPT.Trace.BertiniHodgeQuadratic
import SGPT.Trace.BertiniSliceNormLowerSemicontinuity

/-! Literal original quotient extended Hodge homogeneity and parallelogram. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem nativeBertiniPhysicalQuotientHodgeEnergy_smul (a : ℂ)
    (v : NativeBertiniMultiplierQuotient p i ζ L hφ) :
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (a • v) =
      ENNReal.ofReal (‖a‖ ^ 2) * nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ v := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)
  let R := nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
  let W : member p (affinePoint i ζ) → ℝ≥0∞ := fun y => multiplierWeight 1 (φ y.val)
  change nativePhysicalHodgeEnergy LH (R (a • v)) W = ENNReal.ofReal (‖a‖ ^ 2) * nativePhysicalHodgeEnergy LH (R v) W
  rw [map_smul]
  exact nativePhysicalHodgeEnergy_smul LH (R v) W a

theorem nativeBertiniPhysicalQuotientHodgeEnergy_parallelogram
    (v w : NativeBertiniMultiplierQuotient p i ζ L hφ) :
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (v + w) +
      nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (v - w) =
      2 * (nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ v +
        nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ w) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)
  let R := nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ
  let W : member p (affinePoint i ζ) → ℝ≥0∞ := fun y => multiplierWeight 1 (φ y.val)
  have hW : Measurable W := ((lowerSemicontinuous_originalMultiplierWeight hφ.1).comp continuous_subtype_val).measurable
  change nativePhysicalHodgeEnergy LH (R (v + w)) W + nativePhysicalHodgeEnergy LH (R (v - w)) W =
    2 * (nativePhysicalHodgeEnergy LH (R v) W + nativePhysicalHodgeEnergy LH (R w) W)
  rw [map_add,map_sub]
  exact nativePhysicalHodgeEnergy_parallelogram LH (R v) (R w) W hW

theorem nativeBertiniPhysicalQuotientHodgeEnergy_add_le
    (v w : NativeBertiniMultiplierQuotient p i ζ L hφ) :
    nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ (v + w) ≤
      2 * (nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ v +
        nativeBertiniPhysicalQuotientHodgeEnergy p i ζ hsm L hφ w) := by
  rw [← nativeBertiniPhysicalQuotientHodgeEnergy_parallelogram p i ζ hsm L hφ v w]
  exact le_add_right le_rfl

end SGPT.Trace.Bertini
