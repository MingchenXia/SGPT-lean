import SGPT.Foundations.Analysis.Pending.ActualSmoothLocalQuadraticCorrection

/-!
# Uniform local quadratics for arbitrary smooth real two-forms

The coefficient of the quadratic depends only on the given two-form on a
compact coordinate set. No closedness or local exact potential is required.
This is the coordinate domination used in FPT's nonclosed Hermitian theory.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianQuadratic

open Set Metric Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open KahlerDomination LocalBedfordTaylorCollar SmoothPotentialDomination
open scoped Topology ContDiff

variable {n : ℕ}

/-- A continuous family of real two-forms on a compact set is dominated on
every complex line by one positive quadratic, including in dimension zero. -/
theorem exists_compact_quadratic_domination
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (ha : ContinuousOn a K)
    (z₀ : ComplexModel n) :
    ∃ A : ℝ, 0 < A ∧ ∀ z ∈ K, ∀ v : ComplexModel n,
      a z ![v, Complex.I • v] ≤
        smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] := by
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn ha
  let C : ℝ := max C₀ 0
  let A : ℝ := Real.pi * (C + 1)
  have hC : 0 ≤ C := le_max_right _ _
  have hA : 0 < A := mul_pos Real.pi_pos (by linarith)
  have hq := contDiff_ballPot A z₀ 0
  have hdiag (z v : ComplexModel n) :
      smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] = (C + 1) * ‖v‖ ^ 2 := by
    rw [smoothDDC_complexDiagonal_eq_leviForm
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      leviForm_ballPot]
    dsimp only [A]
    field_simp
  refine ⟨A, hA, fun z hz v => ?_⟩
  rw [hdiag]
  calc
    a z ![v, Complex.I • v] ≤ ‖a z‖ * ‖v‖ ^ 2 :=
      (le_abs_self _).trans (abs_lineValue_le _ _)
    _ ≤ C * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right
      ((hC₀ z hz).trans (le_max_left _ _)) (sq_nonneg _)
    _ ≤ (C + 1) * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]

/-- The local quadratic is chosen before any potential: it depends only
on the smooth coordinate coefficients of the given form. -/
theorem exists_local_quadratic_domination
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ha : ContinuousOn a U) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ U) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ closedBall z₀ r ⊆ U ∧
      ∀ z ∈ closedBall z₀ r, ∀ v : ComplexModel n,
        a z ![v, Complex.I • v] ≤
          smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hsmall : closedBall z₀ (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨A, hA, hdom⟩ := exists_compact_quadratic_domination a
    (isCompact_closedBall z₀ (r / 2)) (ha.mono hsmall) z₀
  exact ⟨A, r / 2, hA, by linarith, hsmall, hdom⟩

/-- Every actual smooth manifold two-form admits a fixed positive local
quadratic majorant. No Hermitian, closedness or exactness hypothesis is used. -/
theorem exists_chart_quadratic_domination
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (omega : SmoothRealForm n M 2)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ closedBall z₀ r ⊆ e.val.target ∧
      ∀ z ∈ closedBall z₀ r, ∀ v : ComplexModel n,
        omega.coeff e z ![v, Complex.I • v] ≤
          smoothDDC (ballPot A z₀ 0) z ![v, Complex.I • v] :=
  exists_local_quadratic_domination e.val.open_target (omega.coeff e)
    (omega.smooth e).continuousOn hz₀

end SGPT.PSH.HermitianQuadratic
