import SGPT.Trace.BertiniUniversalCompactMass
import SGPT.Trace.BertiniUniversalCutoffSupport

/-! Actual whole-tangent joint cutoff physical residue mass is finite
from original global I(phi), without energy/integrability input. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
attribute [local instance] Classical.propDecidable
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

def originalCutoffResidueSourceDensity (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : ∀ x, (OriginalAmbientPhysicalBundle p L).Fiber x) (β : X → ℝ) (w : X → ℝ≥0∞)
    (z : ComplexModel (k + 1 + d)) : ℝ≥0∞ :=
  ENNReal.ofReal (β (originalQSourceX p c z)) * originalMemberResidueSourceDensity p c L T w z

variable [MeasurableSpace X] [BorelSpace X]

theorem originalCutoffResidueSource_integral_lt_top
    (a : X) (ha : c.e = complexChartAt (n := d + 1) a)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {C : Set (ComplexModel (k + 1))} (hC : IsCompact C) (hCb : C ⊆ ball c.ζ₀ c.r)
    (β : X → ℝ) (hβ : HasCompactSupport β) (hβle : ∀ x, β x ≤ 1)
    (hsource : ∀ ζ ∈ C, tsupport β ⊆ c.originalSliceAmbientSource ζ)
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)
    (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) :
    (∫⁻ z in (fun z : ComplexModel (k + 1 + d) => ((prodModelEquiv (k + 1) d).symm z).1) ⁻¹' C,
      originalCutoffResidueSourceDensity p c L T.val β (fun x => multiplierWeight 1 (φ x)) z) < ⊤ := by
  let K := originalCutoffCoordinateSupport p c C β
  have hK : IsCompact K := isCompact_originalCutoffCoordinateSupport p c hC β hβ hsource
  have hKU : K ⊆ originalQSourceDomain p c := originalCutoffCoordinateSupport_subset_source p c hCb β hsource
  let f := originalMemberResidueSourceDensity p c L T.val (fun x => multiplierWeight 1 (φ x))
  have hfin : (∫⁻ z in K, f z) < ⊤ := originalResidue_multiplier_compact_integral_lt_top p c a ha L hK hKU hφ T μ hμ
  let A := (fun z : ComplexModel (k + 1 + d) => ((prodModelEquiv (k + 1) d).symm z).1) ⁻¹' C
  have hA : MeasurableSet A := hC.isClosed.measurableSet.preimage ((prodModelEquiv (k + 1) d).symm.continuous.fst).measurable
  have hp (z : ComplexModel (k + 1 + d)) (hzA : z ∈ A) :
      originalCutoffResidueSourceDensity p c L T.val β (fun x => multiplierWeight 1 (φ x)) z ≤ K.indicator f z := by
    by_cases hz : z ∈ originalQSourceDomain p c
    · let q := originalQSourcePair p c ⟨z,hz⟩
      have hpoint : prodModelEquiv (k + 1) d (q.1.val,q.2.val) = z := (prodModelEquiv (k + 1) d).apply_symm_apply z
      by_cases hzero : β (originalQSourceX p c z) = 0
      · change ENNReal.ofReal (β (originalQSourceX p c z)) * f z ≤ _
        rw [hzero,ENNReal.ofReal_zero,zero_mul]
        exact zero_le
      · have hsupport : c.tangentPoint q ∈ tsupport β := subset_tsupport β (Function.mem_support.mpr hzero)
        have hmem := originalPoint_mem_cutoffCoordinateSupport p c β q hzA hsupport
        rw [hpoint] at hmem
        rw [indicator_of_mem hmem f]
        change ENNReal.ofReal (β (originalQSourceX p c z)) * f z ≤ f z
        calc
          _ ≤ 1 * f z := mul_le_mul' (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hβle (originalQSourceX p c z))) le_rfl
          _ = _ := one_mul _
    · have hzero : f z = 0 := dif_neg hz
      change ENNReal.ofReal (β (originalQSourceX p c z)) * f z ≤ _
      rw [hzero,mul_zero]
      exact zero_le
  have hi : (∫⁻ z in A, originalCutoffResidueSourceDensity p c L T.val β (fun x => multiplierWeight 1 (φ x)) z) ≤
      ∫⁻ z in K, f z := by
    calc
      _ ≤ ∫⁻ z in A, K.indicator f z := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with z hz
        exact hp z hz
      _ ≤ ∫⁻ z, K.indicator f z := setLIntegral_le_lintegral _ _
      _ = _ := lintegral_indicator hK.isClosed.measurableSet f
  exact hi.trans_lt hfin

end SGPT.Trace.BertiniUniversal
