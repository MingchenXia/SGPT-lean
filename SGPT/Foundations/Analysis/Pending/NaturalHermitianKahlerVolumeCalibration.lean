import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormL2
import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint
import SGPT.Foundations.Analysis.Pending.SmoothMixedMeasureDensity

set_option autoImplicit false

/-! # Entire original normalized Hermitian/Kähler volume and Hilbert pairing calibration

All five complete mathematical proofs precede this SOURCE. The actual original
Hermitian measure is calibrated with the existing zero-potential Kähler measure.
Only the actual dense smooth images enter the Hilbert adjoint identity; no
closed differential, bounded extension, elliptic estimate or Green inverse
is assumed or asserted.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration

open FirstPass FirstPass.PositiveClasses NaturalHermitianVolumeMeasure NaturalHermitianFormL2
  NaturalHermitianHodgeStar NaturalHermitianFormalAdjoint NaturalHermitianCodifferential
  NaturalOriginalComplementaryWedgeDuality SmoothMixedMeasureDensity
  IntegrationCurrent GlobalNonPluripolar DiagonalMass TopDegreeDensity ConstantFormProducts
  NaturalHermitianSmoothFormMetric NaturalOriginalGradedExteriorProduct StronglyPositiveForms
  ProductTestForms

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- The original chart metric-unit measure is exactly the normalized actual mixed-density measure. -/
theorem chartDensityMeasure_kahler (w : KahlerBackground n M) (e : ComplexChart n M) :
    chartDensityMeasure w.form.val e =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) •
        ((volume.restrict e.val.target).withDensity (chartDensity (fun _ => w.form) e)) := by
  have hc : 0 ≤ (n.factorial : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hd : (fun z => ENNReal.ofReal (metricVolumeDensity w.form.val e z)) =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) • chartDensity (fun _ => w.form) e := by
    funext z
    rw [metricVolumeDensity_eq_formPow, formPow_coeff, formPower_eq_wedgeProd,
      topDensity_wedgeProd, ENNReal.ofReal_mul hc]
    rfl
  unfold chartDensityMeasure
  rw [hd, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

section Compact

variable [CompactSpace M]

/-- The existing genuine original Kähler measure has the literal inverse-chart density restriction. -/
theorem kahlerVolume_restrict_chart (w : KahlerBackground n M) (e : ComplexChart n M) :
    (kahlerVolume w).restrict e.val.source =
      Measure.map e.val.symm
        ((volume.restrict e.val.target).withDensity (chartDensity (fun _ => w.form) e)) := by
  have h0 : IsThetaPshPotential w.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  rw [← himage, kahlerVolume, diagonalPotentialMeasure]
  exact restrict_image_eq_map (fun _ => h0.1) e e.val.open_target.measurableSet (Subset.refl _)

/-- Entire genuine measures, not merely density or real a.e. values, have the exact normalized calibration. -/
theorem hermitianVolumeMeasure_eq_smul_kahlerVolume (w : KahlerBackground n M) :
    hermitianVolumeMeasure w.form.val w.isKahler.1 =
      ENNReal.ofReal ((n.factorial : ℝ)⁻¹) • kahlerVolume w := by
  have hcandidate : ∀ e : ComplexChart n M,
      (ENNReal.ofReal ((n.factorial : ℝ)⁻¹) • kahlerVolume w).restrict e.val.source =
        chartVolumeMeasure w.form.val e := by
    intro e
    rw [Measure.restrict_smul, kahlerVolume_restrict_chart, ← Measure.map_smul,
      ← chartDensityMeasure_kahler]
    rfl
  exact (existsUnique_hermitianVolumeMeasure w.form.val w.isKahler.1).unique
    (hermitianVolumeMeasure_restrict_chart w.form.val w.isKahler.1) hcandidate

/-- Actual native real Bochner integrals calibrate without any caller integrability assumption. -/
theorem integral_hermitianVolumeMeasure_eq (w : KahlerBackground n M) (f : M → ℝ) :
    (∫ x, f x ∂hermitianVolumeMeasure w.form.val w.isKahler.1) =
      (n.factorial : ℝ)⁻¹ * ∫ x, f x ∂kahlerVolume w := by
  rw [hermitianVolumeMeasure_eq_smul_kahlerVolume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)), smul_eq_mul]

/-- Every actual original form degree has the same whole normalized metric and Hodge integral pairing. -/
theorem integralPair_eq_hodgeIntegralPairing (w : KahlerBackground n M)
    (α β : SmoothRealForm n M q) :
    integralPair w.form.val w.isKahler.1 α β = hodgeIntegralPairing w q α β := by
  by_cases hq : q ≤ 2 * n
  · unfold hodgeIntegralPairing
    rw [dif_pos hq]
    unfold integralPair topIntegral
    rw [integral_hermitianVolumeMeasure_eq]
    simp_rw [hodgeProduct_topRatio]
    change (n.factorial : ℝ)⁻¹ * (∫ x, pointwisePair w.form.val α β x ∂kahlerVolume w) =
      ∫ x, pointwisePair w.form.val α β x * (n.factorial : ℝ)⁻¹ ∂kahlerVolume w
    rw [integral_mul_const, mul_comm]
  · have hp : pointwisePair w.form.val α β = 0 := by
      funext x
      let e := complexChartAt (n := n) x
      have hα : α.coeff e (e.val x) = 0 :=
        originalForm_above_dimension q (by omega) _
      change formMetricCoefficients w.form.val e (e.val x) q
        (α.coeff e (e.val x)) (β.coeff e (e.val x)) = 0
      rw [hα, map_zero]
      rfl
    simp only [integralPair, hp, Pi.zero_apply, integral_zero, hodgeIntegralPairing, dif_neg hq]

/-- The actual dense original smooth images satisfy the genuine Hilbert d/codifferential adjoint identity. -/
theorem hilbert_smooth_image_formal_adjoint (w : KahlerBackground n M) (p : ℕ)
    (α : SmoothRealForm n M p) (β : SmoothRealForm n M (p + 1)) :
    inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 α.exteriorDerivative)
      (toHilbertFormL2 w.form.val w.isKahler.1 β) =
      inner ℝ (toHilbertFormL2 w.form.val w.isKahler.1 α)
        (toHilbertFormL2 w.form.val w.isKahler.1
          (castSmoothForm (show (p + 1) - 1 = p by omega)
            (coderivativeForm w.form.val w.isKahler.1 (p + 1) β))) := by
  rw [hilbert_inner, hilbert_inner, integralPair_eq_hodgeIntegralPairing,
    integralPair_eq_hodgeIntegralPairing]
  exact coderivative_integral_formal_adjoint w p α β

end Compact

end SGPT.Foundations.Analysis.Pending.NaturalHermitianKahlerVolumeCalibration
