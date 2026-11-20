import SGPT.Foundations.Analysis.Pending.YauTheoremInterface

set_option autoImplicit false

/-!
# The actual Monge–Ampère producer for a smooth positive test volume

The target may be an arbitrary smooth positive top-degree form, including
`B ∧ G` for a positive complementary-degree test form. Its actual mass supplies
the normalization, and the proved Yau theorem supplies the corrected Kähler
form and the genuine chart-density equation.
-/

open MeasureTheory Set

namespace SGPT.Foundations.Analysis.Pending.XiaoYauTestVolume

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  IntegrationCurrent TopDegreeDensity ProductTestForms ManifoldTubePositivity

section Normalization

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]

/-- The actual intrinsic integral of a strictly positive smooth top form is positive. -/
theorem integral_topRatio_pos (A : KahlerBackground (m + 1) X)
    (Φ : SmoothRealForm (m + 1) X (2 * (m + 1)))
    (hΦ : ∀ x, 0 < topRatio A.form.val Φ x) :
    0 < ∫ x, topRatio A.form.val Φ x ∂(kahlerVolume A) := by
  have hμ : kahlerVolume A univ ≠ 0 := by
    intro hzero
    have hpos := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A
    simp only [measureReal_def, hzero, ENNReal.toReal_zero, lt_self_iff_false] at hpos
  exact NefCoreKahlerCurrent.integral_pos_of_forall_pos A hμ
    (continuous_topRatio A.isKahler.1 Φ) hΦ

/-- Scaling by the inverse of its actual mass produces a normalized positive top form. -/
theorem normalize_topForm (A : KahlerBackground (m + 1) X)
    (Φ : SmoothRealForm (m + 1) X (2 * (m + 1)))
    (hΦ : ∀ x, 0 < topRatio A.form.val Φ x) :
    let q := ∫ x, topRatio A.form.val Φ x ∂(kahlerVolume A)
    (∀ x, 0 < topRatio A.form.val (q⁻¹ • Φ) x) ∧
      ∫ x, topRatio A.form.val (q⁻¹ • Φ) x ∂(kahlerVolume A) = 1 := by
  dsimp only
  have hq := integral_topRatio_pos A Φ hΦ
  constructor
  · intro x
    rw [topRatio_smul]
    exact mul_pos (inv_pos.mpr hq) (hΦ x)
  · simp_rw [topRatio_smul]
    rw [integral_const_mul, inv_mul_cancel₀ hq.ne']

end Normalization

/-- Yau's proved theorem constructs the solution for an actual normalized positive top form. -/
theorem exists_kahler_mongeAmpere_eq_topForm {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : KahlerBackground (m + 1) X) (Φ : SmoothRealForm (m + 1) X (2 * (m + 1)))
    (hΦ : ∀ x, 0 < topRatio A.form.val Φ x)
    (hnorm : ∫ x, topRatio A.form.val Φ x ∂(kahlerVolume A) = 1) :
    ∃ (u : X → ℝ) (hu : ChartSmooth (n := m + 1) u),
      (A.form + ddcClosedForm u hu).val.IsKahler ∧
      ∀ (e : ComplexChart (m + 1) X) z, z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
          (kahlerVolume A).real univ * topDensity (Φ.coeff e z) := by
  let c := (kahlerVolume A).real univ
  have hc : 0 < c := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos A
  let R : X → ℝ := topRatio A.form.val Φ
  have hRs : ChartSmooth (n := m + 1) R :=
    TopBidimensionCurrents.chartSmooth_topRatio A.isKahler.1 Φ
  let F : X → ℝ := fun x => Real.log (c * R x)
  have hFs : ChartSmooth (n := m + 1) F := fun e =>
    (contDiffOn_const.mul (hRs e)).log fun z _ => (mul_pos hc (hΦ _)).ne'
  have hexp : ∀ x, Real.exp (F x) = c * R x :=
    fun x => Real.exp_log (mul_pos hc (hΦ x))
  have hnormF : ∫ x, Real.exp (F x) ∂(kahlerVolume A) = (kahlerVolume A).real univ := by
    simp_rw [hexp]
    rw [integral_const_mul, hnorm, mul_one]
  obtain ⟨u, hu, hK, hMA⟩ :=
    YauTheorem.exists_kahler_mongeAmpere_eq_exp (Nat.succ_pos m) A hFs hnormF
  refine ⟨u, hu, hK, fun e z hz => ?_⟩
  rw [hMA e z hz, hexp]
  have hRchart : R (e.val.symm z) =
      topDensity (Φ.coeff e z) / actualTopPowerDensity (A.form.val.coeff e z) := by
    dsimp only [R]
    rw [topRatio_eq_chartRatio A.isKahler.1 Φ (e.val.map_target hz), e.val.right_inv hz,
      chartRatio, formPow_coeff, topDensity_formPower]
  rw [hRchart]
  have hd := YauTheorem.actualTopPowerDensity_pos A hz
  change c * (topDensity (Φ.coeff e z) / actualTopPowerDensity (A.form.val.coeff e z)) *
    actualTopPowerDensity (A.form.val.coeff e z) = c * topDensity (Φ.coeff e z)
  field_simp [hd.ne']

end SGPT.Foundations.Analysis.Pending.XiaoYauTestVolume
