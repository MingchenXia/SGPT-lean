import SGPT.Foundations.Analysis.Pending.OTSliceVanishing
import SGPT.Foundations.Analysis.Pending.OTChenWeights

/-!
# Hyperplane nullity and the source critical kernel

The real-division kernel is zero on the normal slice. The reciprocal ENNReal
kernel below has value ∞ there, as in the usual source convention. Their
integrals agree on a normal chart with `|w|² < 1` because the hyperplane is
ambient Lebesgue null. Preservation of the trace requires a separate argument.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OTChen

namespace SGPT.Trace.TwistedL2.OTNormalKernel

variable {m : ℕ}

/-- The actual coordinate hyperplane has zero ambient Lebesgue measure in
any tangential dimension, including dimension zero. -/
theorem normal_hyperplane_volume_zero :
    (volume : Measure (ComplexModel (m + 1))) {z | z (Fin.last m) = 0} = 0 := by
  let H : Set (ComplexModel m × ℂ) := (univ : Set (ComplexModel m)) ×ˢ {0}
  have hHm : MeasurableSet H :=
    (MeasurableSet.univ : MeasurableSet (univ : Set (ComplexModel m))).prod (measurableSet_singleton 0)
  have hprod : ((volume : Measure (ComplexModel m)).prod (volume : Measure ℂ)) H = 0 := by
    rw [show H = (univ : Set (ComplexModel m)) ×ˢ ({0} : Set ℂ) from rfl,
      Measure.prod_prod, measure_singleton, mul_zero]
  have hmap : ((volume : Measure (ComplexModel (m + 1))).map (splitEquiv m)) H = 0 := by
    rw [map_splitEquiv_volume, Measure.smul_apply, hprod, smul_zero]
  have hpre := Measure.map_apply (μ := (volume : Measure (ComplexModel (m + 1))))
    (splitEquiv m).measurable hHm
  have hpre0 : (volume : Measure (ComplexModel (m + 1))) ((splitEquiv m) ⁻¹' H) = 0 := by
    rw [← hpre]
    exact hmap
  have hset : (splitEquiv m) ⁻¹' H = {z | z (Fin.last m) = 0} := by
    ext z
    change ((splitEquiv m) z ∈ H) ↔ z (Fin.last m) = 0
    rw [splitEquiv_apply]
    simp [H]
  simpa only [hset] using hpre0

/-- The normal coordinate is nonzero almost everywhere, also after
restriction to any measurable or nonmeasurable set. -/
theorem ae_normal_coordinate_ne_zero (K : Set (ComplexModel (m + 1))) :
    ∀ᵐ z ∂((volume : Measure (ComplexModel (m + 1))).restrict K), z (Fin.last m) ≠ 0 := by
  exact ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp normal_hyperplane_volume_zero)

/-- Totalized real reciprocal of the normal critical denominator. -/
def realDivisionKernel (z : ComplexModel (m + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (coordSq (Fin.last m) z * (-Real.log (coordSq (Fin.last m) z)) ^ 2))

/-- The same pointwise expression with the source convention `1/0 = ∞` in
`ℝ≥0∞`. The additional zero at `|w|² = 1` is excluded by the small chart. -/
def sourceReciprocalKernel (z : ComplexModel (m + 1)) : ℝ≥0∞ :=
  (ENNReal.ofReal (coordSq (Fin.last m) z * (-Real.log (coordSq (Fin.last m) z)) ^ 2))⁻¹

theorem kernels_differ_on_normal_slice {z : ComplexModel (m + 1)} (hz : z (Fin.last m) = 0) :
    realDivisionKernel z = 0 ∧ sourceReciprocalKernel z = ⊤ := by
  simp [realDivisionKernel, sourceReciprocalKernel, coordSq, hz]

/-- Off the hyperplane and inside the normal unit ball, the real-division
and source-reciprocal kernels coincide pointwise. -/
theorem kernels_eq_off_slice {z : ComplexModel (m + 1)}
    (hz : z (Fin.last m) ≠ 0) (hsmall : coordSq (Fin.last m) z < 1) :
    realDivisionKernel z = sourceReciprocalKernel z := by
  have hq : 0 < coordSq (Fin.last m) z := by
    dsimp [coordSq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hlog : Real.log (coordSq (Fin.last m) z) < 0 := Real.log_neg hq hsmall
  have hden : 0 < coordSq (Fin.last m) z * (-Real.log (coordSq (Fin.last m) z)) ^ 2 := by
    exact mul_pos hq (sq_pos_of_pos (neg_pos.mpr hlog))
  dsimp [realDivisionKernel, sourceReciprocalKernel]
  rw [one_div, ENNReal.ofReal_inv_of_pos hden]

/-- The producer's normal-radius assumptions give the strict small-chart
hypothesis needed for source-kernel comparison. -/
theorem normal_sq_lt_one_of_radius {K D : Set (ComplexModel (m + 1))}
    (hKD : K ⊆ D) {R : ℝ} (_hR : 0 < R) (hRsmall : 2 * R ^ 2 ≤ 1)
    (hDR : ∀ z ∈ D, ‖z (Fin.last m)‖ < R) :
    ∀ z ∈ K, coordSq (Fin.last m) z < 1 := by
  intro z hz
  have hq : coordSq (Fin.last m) z ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hDR z (hKD hz)).le 2
  nlinarith [sq_nonneg R]

/-- Almost-everywhere equality of the source and totalized kernels on the
actual small normal chart. -/
theorem ae_kernels_eq_on_small_chart {K : Set (ComplexModel (m + 1))}
    (hKm : MeasurableSet K) (hsmall : ∀ z ∈ K, coordSq (Fin.last m) z < 1) :
    realDivisionKernel =ᵐ[(volume : Measure (ComplexModel (m + 1))).restrict K]
      sourceReciprocalKernel := by
  filter_upwards [ae_normal_coordinate_ne_zero K, ae_restrict_mem hKm] with z hz hzK
  exact kernels_eq_off_slice hz (hsmall z hzK)

/-- The equality survives arbitrary section norms and arbitrary extended
multiplier weights, including `0 * ∞`, without changing the trace data. -/
theorem lintegral_realDivision_eq_source {K : Set (ComplexModel (m + 1))}
    (hKm : MeasurableSet K) (hsmall : ∀ z ∈ K, coordSq (Fin.last m) z < 1)
    (F : ComplexModel (m + 1) → ℂ) (W : ComplexModel (m + 1) → ℝ≥0∞) :
    (∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * (realDivisionKernel z * W z)) =
      ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * (sourceReciprocalKernel z * W z) := by
  apply lintegral_congr_ae
  filter_upwards [ae_kernels_eq_on_small_chart hKm hsmall] with z hz
  rw [hz]

end SGPT.Trace.TwistedL2.OTNormalKernel
