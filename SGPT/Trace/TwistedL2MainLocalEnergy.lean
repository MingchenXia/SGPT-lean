import SGPT.Trace.TwistedL2MainLocalMeasure
import SGPT.Foundations.Analysis.Pending.OTWeakDbar

/-!
# Pointwise chart energy of the actual twisted correction

These identities are the input for the chart-density change of measure. They
concern the actual L² representative and actual frame coefficient, not an
abstract replacement solution.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.Hormander SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-- The chart weight representing the H₁ norm of an actual section. -/
def localH1Weight (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  localWeight T.L c e ρ T.φ z + Real.log (T.a (c.val.symm z) + T.b (c.val.symm z))

/-- The H₁ chart weight is continuous where the actual local test pieces live. -/
theorem continuousOn_localH1Weight (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    ContinuousOn (T.localH1Weight c e ρ) (T.pieceDomain c e) := by
  have hab : ContDiffOn ℝ ∞ (fun z => T.a (c.val.symm z) + T.b (c.val.symm z))
      (T.pieceDomain c e) :=
    ((T.a_smooth c).add (T.b_smooth c)).mono (T.pieceDomain_subset_chartSmooth c e)
  have hlog := hab.log fun z hz => (T.ab_pos hz.2).ne'
  exact (T.contDiffOn_localWeight e hρ).continuousOn.add hlog.continuousOn

/-- The H₁ chart density factors into the frame norm, original H₁ weight,
and the chart-volume density. -/
theorem exp_neg_localH1Weight (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) :
    Real.exp (-T.localH1Weight c e ρ z) =
      frameNormSq T.L e (c.val.symm z) * T.H1weight (c.val.symm z) * ρ z := by
  have hab := T.ab_pos hz.2
  rw [localH1Weight,
    show -(localWeight T.L c e ρ T.φ z + Real.log (T.a (c.val.symm z) + T.b (c.val.symm z))) =
      -localWeight T.L c e ρ T.φ z - Real.log (T.a (c.val.symm z) + T.b (c.val.symm z)) by ring,
    Real.exp_sub, Real.exp_log hab, T.exp_neg_localWeight e hρ hz.1, H1weight]
  ring

/-- The Euclidean weighted energy of the actual local correction coefficient
is exactly the scalar representative's energy times the actual chart-volume
density. This is pointwise on the chart-frame domain over `U`. -/
theorem correctionFrameCoeff_local_energy (u : Lp ℂ 2 (T.μ.restrict T.U))
    (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ)
    {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) :
    ‖T.correctionFrameCoeff u e (c.val.symm z)‖ ^ 2 *
        Real.exp (-T.localH1Weight c e ρ z) =
      ‖(u : X → ℂ) (c.val.symm z)‖ ^ 2 * ρ z := by
  have hnorm := T.correctionSection_weighted_norm_sq u hz.2
  rw [norm_sq_eq_frameCoeff e hz.1.2 (T.correctionSection u (c.val.symm z)),
    ← T.correctionFrameCoeff_of_mem u e hz.1.2, H1weight] at hnorm
  have hab := T.ab_pos hz.2
  rw [localH1Weight,
    show -(localWeight T.L c e ρ T.φ z + Real.log (T.a (c.val.symm z) + T.b (c.val.symm z))) =
      -localWeight T.L c e ρ T.φ z - Real.log (T.a (c.val.symm z) + T.b (c.val.symm z)) by ring,
    Real.exp_sub, Real.exp_log hab, T.exp_neg_localWeight e hρ hz.1]
  calc
    ‖T.correctionFrameCoeff u e (c.val.symm z)‖ ^ 2 *
        (frameNormSq T.L e (c.val.symm z) * Real.exp (-T.φ (c.val.symm z)) * ρ z /
          (T.a (c.val.symm z) + T.b (c.val.symm z))) =
      (‖T.correctionFrameCoeff u e (c.val.symm z)‖ ^ 2 * frameNormSq T.L e (c.val.symm z) *
        (Real.exp (-T.φ (c.val.symm z)) / (T.a (c.val.symm z) + T.b (c.val.symm z)))) * ρ z := by ring
    _ = ‖(u : X → ℂ) (c.val.symm z)‖ ^ 2 * ρ z := by rw [hnorm]


/-- Lebesgue measure on a local piece, transported to the manifold by the
inverse chart, is absolutely continuous with respect to the original volume
on `U`. Positivity of the chart density is essential here. -/
theorem inverseChart_piece_absolutelyContinuous (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    Measure.map c.val.symm (volume.restrict (T.pieceDomain c e)) ≪ T.μ.restrict T.U := by
  let D := T.pieceDomain c e
  have hDm : MeasurableSet D := (T.isOpen_pieceDomain c e).measurableSet
  have hDt : D ⊆ c.val.target := T.pieceDomain_subset_target c e
  have hrho : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict D) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρ.1.continuousOn.mono hDt)).aemeasurable hDm
  have hpos : ∀ᵐ z ∂(volume.restrict D), ENNReal.ofReal (ρ z) ≠ 0 := by
    filter_upwards [ae_restrict_mem hDm] with z hz
    exact (ENNReal.ofReal_pos.mpr (hρ.2.1 z (hDt hz))).ne'
  have hac : volume.restrict D ≪
      (volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)) :=
    withDensity_absolutelyContinuous' hrho hpos
  have hs : AEMeasurable c.val.symm (volume.restrict D) :=
    (c.val.continuousOn_symm.mono hDt).aemeasurable hDm
  have hs' : AEMeasurable c.val.symm
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) :=
    hs.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map c.val.symm (volume.restrict D) ≪
      Measure.map c.val.symm
        ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) := by
    refine Measure.AbsolutelyContinuous.mk fun s hsm hzero => ?_
    rw [Measure.map_apply_of_aemeasurable hs' hsm] at hzero
    rw [Measure.map_apply_of_aemeasurable hs hsm]
    exact hac hzero
  have hsub : c.val ⁻¹' D ∩ c.val.source ⊆ T.U := by
    intro x hx
    have hxu : c.val.symm (c.val x) ∈ T.U := hx.1.2
    simpa only [c.val.left_inv hx.2] using hxu
  have hle : (T.μ.restrict c.val.source).restrict (c.val ⁻¹' D) ≤ T.μ.restrict T.U := by
    rw [Measure.restrict_restrict' c.val.open_source.measurableSet]
    exact Measure.restrict_mono hsub le_rfl
  apply hmap.trans
  rw [chartDensity_map_symm_restrict c hρ hDm hDt]
  exact hle.absolutelyContinuous

/-- The actual local correction coefficient is a.e. strongly measurable for
Lebesgue measure on the chart piece. -/
theorem aestronglyMeasurable_chartCorrectionCoeff
    (u : Lp ℂ 2 (T.μ.restrict T.U)) (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    AEStronglyMeasurable (fun z => T.correctionFrameCoeff u e (c.val.symm z))
      (volume.restrict (T.pieceDomain c e)) := by
  have hs : AEMeasurable c.val.symm (volume.restrict (T.pieceDomain c e)) :=
    (c.val.continuousOn_symm.mono (T.pieceDomain_subset_target c e)).aemeasurable
      (T.isOpen_pieceDomain c e).measurableSet
  have hcoeff : AEMeasurable (T.correctionFrameCoeff u e)
      (Measure.map c.val.symm (volume.restrict (T.pieceDomain c e))) :=
    (T.aestronglyMeasurable_correctionFrameCoeff u e).aemeasurable.mono_ac
      (T.inverseChart_piece_absolutelyContinuous c e hρ)
  exact (hcoeff.comp_aemeasurable hs).aestronglyMeasurable


/-- The actual correction coefficient belongs to the weighted Euclidean
`L²` space on the chart-frame piece. The measure transport uses the original
restricted manifold L² element and the true positive chart density. -/
theorem memLp_chartCorrectionCoeff
    (u : Lp ℂ 2 (T.μ.restrict T.U)) (c : ComplexChart n X) (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    MemLp (fun z => T.correctionFrameCoeff u e (c.val.symm z)) 2
      (weightedVolume (T.pieceDomain c e) (T.localH1Weight c e ρ)) := by
  let D := T.pieceDomain c e
  have hDm : MeasurableSet D := (T.isOpen_pieceDomain c e).measurableSet
  have hDt : D ⊆ c.val.target := T.pieceDomain_subset_target c e
  have hrho : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict D) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρ.1.continuousOn.mono hDt)).aemeasurable hDm
  have hs : AEMeasurable c.val.symm
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) :=
    ((c.val.continuousOn_symm.mono hDt).aemeasurable hDm).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hsub : c.val ⁻¹' D ∩ c.val.source ⊆ T.U := by
    intro x hx
    have hxu : c.val.symm (c.val x) ∈ T.U := hx.1.2
    simpa only [c.val.left_inv hx.2] using hxu
  have hle : (T.μ.restrict c.val.source).restrict (c.val ⁻¹' D) ≤ T.μ.restrict T.U := by
    rw [Measure.restrict_restrict' c.val.open_source.measurableSet]
    exact Measure.restrict_mono hsub le_rfl
  have hu : MemLp (u : X → ℂ) 2
      (Measure.map c.val.symm
        ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z)))) := by
    rw [chartDensity_map_symm_restrict c hρ hDm hDt]
    exact (Lp.memLp u).mono_measure hle
  have hv : MemLp (fun z => (u : X → ℂ) (c.val.symm z)) 2
      ((volume.restrict D).withDensity (fun z => ENNReal.ofReal (ρ z))) :=
    hu.comp_of_map hs
  have hint := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  rw [integrable_withDensity_iff_integrable_smul₀' hrho
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hint
  have henergy : Integrable (fun z => ‖(u : X → ℂ) (c.val.symm z)‖ ^ 2 * ρ z)
      (volume.restrict D) := by
    refine hint.congr ?_
    filter_upwards [ae_restrict_mem hDm] with z hz
    simp only [ENNReal.toReal_ofReal (hρ.2.1 z (hDt hz)).le, smul_eq_mul]
    ring
  have hw : AEMeasurable (T.localH1Weight c e ρ) (volume.restrict D) :=
    (T.continuousOn_localH1Weight c e hρ).aemeasurable hDm
  have hmeas := T.aestronglyMeasurable_chartCorrectionCoeff u c e hρ
  apply (memLp_weightedVolume_iff hw hmeas).mpr
  refine henergy.congr ?_
  filter_upwards [ae_restrict_mem hDm] with z hz
  exact (T.correctionFrameCoeff_local_energy u c e hρ hz).symm

end TwistedDatum
end SGPT.Trace.TwistedL2
