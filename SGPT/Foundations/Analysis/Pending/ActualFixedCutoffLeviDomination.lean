import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationFixedCover
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi

set_option autoImplicit false

/-! # Intrinsic uniform control of the actual squared-cutoff Levi error -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualFixedCutoffLeviDomination
open FirstPass FirstPass.PositiveClasses QuantitativeRegularizationFixedCover
  ConcentrationPotentialLevi ManifoldTubePositivity PositivityPerturbation

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem cutoff_error_identity {c : ComplexModel n → ℝ} {z : ComplexModel n}
    (hc : ContDiffAt ℝ 2 c z) (v : ComplexModel n) :
    Complex.normSq (delC c z v) - c z * leviForm c z v =
      leviForm (fun w => c w * c w) z v / 2 - 2 * c z * leviForm c z v := by
  rw [leviForm_mul hc hc, normSq_delC]
  ring

/-- ONE genuine geometric margin, before every potential and Bergman level. -/
theorem exists_uniform_cutoff_error_bound [CompactSpace X]
    (F : FixedChartCover n X) (omega : KahlerBackground n X) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : F.t) (e : ComplexChart n X)
      (z : ComplexModel n), z ∈ e.val.target → ∀ v : ComplexModel n,
        Complex.normSq (delC (fun w => F.cover.χ j (e.val.symm w)) z v) -
          F.cover.χ j (e.val.symm z) *
            leviForm (fun w => F.cover.χ j (e.val.symm w)) z v ≤
        C * omega.form.val.coeff e z ![v, Complex.I • v] := by
  classical
  have hsq : ∀ j, ChartSmooth (n := n) (fun y => F.cover.χ j y * F.cover.χ j y) :=
    fun j e => (F.cover.χ_smooth j e).mul (F.cover.χ_smooth j e)
  let alpha : F.t × Bool → ClosedRealOneOneForm n X := fun p =>
    if p.2 then ddcClosedForm (F.cover.χ p.1) (F.cover.χ_smooth p.1)
    else -ddcClosedForm (fun y => F.cover.χ p.1 y * F.cover.χ p.1 y) (hsq p.1)
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega alpha
  refine ⟨3 * Real.pi * A, by positivity, fun j e z hz v => ?_⟩
  let c : ComplexModel n → ℝ := fun w => F.cover.χ j (e.val.symm w)
  let W : ℝ := omega.form.val.coeff e z ![v, Complex.I • v]
  have hW : 0 ≤ W := omega.isSemipositive e z hz v
  have hc : ContDiffAt ℝ 2 c z :=
    ((F.cover.χ_smooth j e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have h1 := hsemi (j, true) e z hz v
  have h2 := hsemi (j, false) e z hz v
  dsimp only [alpha] at h1 h2
  simp only [ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1
  simp only [Bool.false_eq_true, if_false, ClosedRealOneOneForm.coeff_add,
    ClosedRealOneOneForm.coeff_neg, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h2
  change 0 ≤ quad ((ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j)).val.coeff e z) v + A * W at h1
  change 0 ≤ -quad ((ddcClosedForm (fun y => F.cover.χ j y * F.cover.χ j y)
    (hsq j)).val.coeff e z) v + A * W at h2
  rw [quad_ddcClosedForm_coeff (F.cover.χ_smooth j) e hz v] at h1
  rw [quad_ddcClosedForm_coeff (hsq j) e hz v] at h2
  change 0 ≤ leviForm c z v / Real.pi + A * W at h1
  change 0 ≤ - (leviForm (fun w => c w * c w) z v / Real.pi) + A * W at h2
  have hlo : -(Real.pi * A * W) ≤ leviForm c z v := by
    have h := mul_nonneg h1 Real.pi_pos.le
    nlinarith [div_mul_cancel₀ (leviForm c z v) Real.pi_ne_zero]
  have hup : leviForm (fun w => c w * c w) z v ≤ Real.pi * A * W := by
    have h := mul_nonneg h2 Real.pi_pos.le
    nlinarith [div_mul_cancel₀ (leviForm (fun w => c w * c w) z v) Real.pi_ne_zero]
  have hc0 : 0 ≤ c z := F.cover.χ_nonneg j _
  have hc1 : c z ≤ 1 := F.χ_le_one j _
  have hmargin : 0 ≤ Real.pi * A * W := by positivity
  have hneg : -2 * c z * leviForm c z v ≤ 2 * (Real.pi * A * W) := by
    have h := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 * c z by positivity)
    have h' := mul_le_mul_of_nonneg_right hc1 hmargin
    nlinarith
  have hid := cutoff_error_identity hc v
  change Complex.normSq (delC c z v) - c z * leviForm c z v ≤ 3 * Real.pi * A * W
  nlinarith

/-- The actual support condition kills both derivatives off the patch, including its boundary. -/
theorem cutoff_error_vanishes_off_patch (F : FixedChartCover n X) (j : F.t)
    (e : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hy : e.val.symm z ∉ F.cover.V j) :
    fderiv ℝ (fun w => F.cover.χ j (e.val.symm w)) z = 0 ∧
      ∀ v : ComplexModel n,
        leviForm (fun w => F.cover.χ j (e.val.symm w)) z v = 0 ∧
        Complex.normSq (delC (fun w => F.cover.χ j (e.val.symm w)) z v) -
          F.cover.χ j (e.val.symm z) *
            leviForm (fun w => F.cover.χ j (e.val.symm w)) z v = 0 := by
  have hyT : e.val.symm z ∉ tsupport (F.cover.χ j) :=
    fun h => hy (F.cover.tsupport_χ_subset j h)
  have hzero : ∀ᶠ y in 𝓝 (e.val.symm z), F.cover.χ j y = 0 := by
    filter_upwards [(isClosed_tsupport (F.cover.χ j)).isOpen_compl.mem_nhds hyT] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have heq : (fun w => F.cover.χ j (e.val.symm w)) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) :=
    (e.val.symm.continuousAt hz).eventually hzero
  have hfd : fderiv ℝ (fun w => F.cover.χ j (e.val.symm w)) z = 0 := by
    rw [heq.fderiv_eq (𝕜 := ℝ)]
    exact fderiv_const_apply (𝕜 := ℝ) (x := z) 0
  have h2 : iteratedFDeriv ℝ 2 (fun w => F.cover.χ j (e.val.symm w)) z = 0 := by
    simpa using (heq.iteratedFDeriv ℝ 2).eq_of_nhds
  refine ⟨hfd, fun v => ?_⟩
  have hL : leviForm (fun w => F.cover.χ j (e.val.symm w)) z v = 0 := by
    simp [leviForm, realHessian, h2]
  refine ⟨hL, ?_⟩
  simp [delC, hfd, hL]

end SGPT.Foundations.Analysis.Pending.ActualFixedCutoffLeviDomination
