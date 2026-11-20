import SGPT.Foundations.Analysis.Pending.MongeAmpereRegularity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Openness of the `ε`-continuity path among smooth solutions

For a Kähler background `A` on a compact complex manifold `Y`, `F` chart-smooth and `ε > 0`, let
`S_ε` be the set of `t` for which `(A + ddᶜφ)^N = e^{tF + εφ} A^N` has a chart-smooth solution `φ` with
`A + ddᶜφ` Kähler.  **`S_ε` is open** (`exists_smooth_ma_eq_near`, blueprint `bou:yau-openness`):
* the inverse function theorem in `C^{2,r}` (`YauOpenness`), positivity near the smooth solution
  (`MongeAmperePositivity.exists_ma_eq_near_posDef`) and the regularity bootstrap
  (`MongeAmpereRegularity.chartSmooth_of_ma_eq`) give a chart-smooth `ψ` with `ma A ψ = tF + εψ`
  and `H_A + complexHessian ψ > 0` in every chart;
* `isKahler_of_posDef`: positive definiteness of the coefficient matrix in every chart makes
  `A + ddᶜψ` Kähler (`isStrictlyPositive_of_posDef`);
* `density_eq_of_ma_eq`: `ma A ψ = G` gives the density form `(A + ddᶜψ)^N = e^G A^N` in every chart
  (converse of `YauOpenness.ma_eq_of_density`).

TN.4 B5, N1.
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.YauSmoothOpenness

open FirstPass FirstPass.MongeAmpere KahlerLaplacianChart MongeAmpereHolder ManifoldTubePositivity
  PositiveClasses StronglyPositiveForms SubmanifoldMassConcentration

variable {n : ℕ}

/-- A `(1,1)`-form whose normalized matrix is positive definite is strictly positive. -/
theorem isStrictlyPositive_of_posDef {A : RealForm n 2} (hA : IsOneOne A)
    (hP : (normalizedHermitianMatrix A).PosDef) : IsStrictlyPositive A := by
  classical
  intro u hu
  set x : Fin n → ℂ := fun j => star (u j) with hx
  have hy : (∑ j, (star (x j)) • coordinateVector j : ComplexModel n) = u := by
    ext i
    rw [coord_sum_star_smul_coordinateVector x i]
    simp [hx]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hu
    ext i
    have := congrFun h0 i
    simp only [hx, Pi.zero_apply, star_eq_zero] at this
    simpa using this
  have h := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_normalizedHermitianMatrix hA, hy] at h
  have h' := Complex.zero_lt_real.mp h
  exact pos_of_mul_pos_right h' Real.pi_pos.le

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **Kähler from positivity in charts**: if `H_A + complexHessian φ` is positive definite in every
chart, then `A + ddᶜφ` is a Kähler form. -/
theorem isKahler_of_posDef (A : KahlerBackground N Y) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    (hpos : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (normalizedHermitianMatrix (A.form.val.coeff e z) +
        complexHessian (fun x => φ (e.val.symm x)) z).PosDef) :
    (A.form + ddcClosedForm φ hφ).val.IsKahler := by
  refine ⟨fun e z hz => ⟨(A.form + ddcClosedForm φ hφ).property.2 e z hz, ?_⟩,
    (A.form + ddcClosedForm φ hφ).property.1⟩
  refine isStrictlyPositive_of_posDef ((A.form + ddcClosedForm φ hφ).property.2 e z hz) ?_
  rw [YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ hz]
  exact hpos e z hz

/-- **The density form from `ma`**: if `A + ddᶜφ` is Kähler and `ma A φ = G`, then
`(A + ddᶜφ)^N = e^G A^N` in every chart. -/
theorem density_eq_of_ma_eq (A : KahlerBackground N Y) {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    {G : Y → ℝ} (hK : (A.form + ddcClosedForm φ hφ).val.IsKahler)
    (hma : ∀ y, ma A.form.val φ y = G y) (e : ComplexChart N Y) (z : ComplexModel N)
    (hz : z ∈ e.val.target) :
    actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
      Real.exp (G (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z) := by
  have h11 : IsOneOne ((A.form + ddcClosedForm φ hφ).val.coeff e z) := (hK.1 e z hz).1
  have hA11 : IsOneOne (A.form.val.coeff e z) := (A.isKahler.1 e z hz).1
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det h11,
    ConcentrationMassComparison.actualTopPowerDensity_eq_det hA11,
    YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ hz]
  have hP : (normalizedHermitianMatrix (A.form.val.coeff e z) +
      complexHessian (fun x => φ (e.val.symm x)) z).PosDef := by
    rw [← YauOpenness.normalizedHermitianMatrix_add_ddc A.form hφ hz]
    exact posDef_coeff hK.1 hz
  have hd1 : 0 < (normalizedHermitianMatrix (A.form.val.coeff e z) +
      complexHessian (fun x => φ (e.val.symm x)) z).det.re := (Complex.pos_iff.mp hP.det_pos).1
  have hd0 : 0 < (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re :=
    (Complex.pos_iff.mp (posDef_coeff A.isKahler.1 hz).det_pos).1
  have hφC2 : ∀ f : ComplexChart N Y,
      ContDiffOn ℝ 2 (fun w => φ (f.val.symm w)) f.val.target := fun f =>
    (hφ f).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hye : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hdet : (normalizedHermitianMatrix (A.form.val.coeff e (e.val (e.val.symm z))) +
      complexHessian (fun w => φ (e.val.symm w)) (e.val (e.val.symm z))).det.re ≠ 0 := by
    rw [e.val.right_inv hz]; exact hd1.ne'
  have hm := ma_eq A.isKahler.1 hφC2 hye hdet
  rw [e.val.right_inv hz, hma] at hm
  simp only [maChart] at hm
  have hlog : (normalizedHermitianMatrix (A.form.val.coeff e z) +
      complexHessian (fun x => φ (e.val.symm x)) z).det.re =
      Real.exp (G (e.val.symm z)) * (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re := by
    rw [hm, Real.exp_sub, Real.exp_log hd1, Real.exp_log hd0]
    field_simp
  rw [hlog]
  ring

/-- **Openness of `S_ε`** (blueprint `bou:yau-openness`): if `φ₀` is a chart-smooth solution of
`(A + ddᶜφ₀)^N = e^{t₀F + εφ₀} A^N` with `A + ddᶜφ₀` Kähler (`ε > 0`, `Y` compact), then for all `t`
near `t₀` there is a chart-smooth `φ` with `A + ddᶜφ` Kähler and `(A + ddᶜφ)^N = e^{tF + εφ} A^N`. -/
theorem exists_smooth_ma_eq_near [CompactSpace Y] (A : KahlerBackground N Y) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) {ε : ℝ} (hε : 0 < ε) {t₀ : ℝ} {φ₀ : Y → ℝ}
    (hφ₀ : ChartSmooth (n := N) φ₀) (hK : (A.form + ddcClosedForm φ₀ hφ₀).val.IsKahler)
    (hdens : ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ₀ hφ₀).val.coeff e z) =
        Real.exp (t₀ * F (e.val.symm z) + ε * φ₀ (e.val.symm z)) *
          actualTopPowerDensity (A.form.val.coeff e z)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - t₀| < δ → ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z)) *
            actualTopPowerDensity (A.form.val.coeff e z) := by
  obtain ⟨HA⟩ := HolderAtlas.nonempty (n := N) (M := Y)
  have hr0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ≥0) < 1 := by
    rw [← NNReal.coe_lt_coe]; norm_num
  obtain ⟨δ, hδ, hsol⟩ := MongeAmperePositivity.exists_ma_eq_near_posDef A HA hr0 hr1 hF hε hφ₀ hK
    hdens one_pos
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨ψ, -, heq, hpos⟩ := hsol t ht
  have hψ : ChartSmooth (n := N) ⇑ψ :=
    MongeAmpereRegularity.chartSmooth_of_ma_eq A hr0 hr1 hF ψ hpos heq
  have hKψ := isKahler_of_posDef A hψ hpos
  exact ⟨ψ, hψ, hKψ, fun e z hz => density_eq_of_ma_eq A hψ (G := fun y => t * F y + ε * ψ y)
    hKψ heq e z hz⟩

end SGPT.Foundations.Analysis.Pending.YauSmoothOpenness
