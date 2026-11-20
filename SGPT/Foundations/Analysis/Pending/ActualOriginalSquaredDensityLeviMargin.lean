import SGPT.Foundations.Analysis.Pending.ActualFixedCutoffLeviDomination
import SGPT.Foundations.Analysis.Pending.ActualSquaredBergmanDensityUniformRatios
import SGPT.Foundations.Analysis.Pending.ActualFiniteHilbertSquaredCutoffLevi

set_option autoImplicit false

/-! # Curvature of the SAME actual squared Bergman density -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal Classical
namespace SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityLeviMargin
open FirstPass FirstPass.PositiveClasses FirstPass.HolomorphicMaps
  QuantitativeRegularizationFixedCover QuantitativeRegularizationChartBranch
  BergmanKernelSmooth BergmanSupWeight GlobalTubeFunction
  ActualGlobalSquaredBergmanDensity ActualFixedAtlasHolomorphicKernelGauges
  ActualSquaredBergmanDensityUniformRatios ActualFixedCutoffLeviDomination
  ActualFiniteHilbertSquaredCutoffLevi ConcentrationPotentialLevi

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

private theorem norm_sq_gauged {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (k : ℕ) (g : ℂ) (a : H) :
    ‖Complex.exp (((k : ℝ) / 2 : ℝ) * g) • a‖ ^ 2 =
      Real.exp ((k : ℝ) * g.re) * ‖a‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_exp, pow_two, ← Real.exp_add]
  have he : ((((k : ℝ) / 2 : ℝ) : ℂ) * g).re +
      ((((k : ℝ) / 2 : ℝ) : ℂ) * g).re = (k : ℝ) * g.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [he]

private theorem smooth_squared_dual_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : ComplexModel n → StrongDual ℂ H} {z : ComplexModel n}
    (hA : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ A y) :
    ContDiffAt ℝ 2 (fun y => ‖A y‖ ^ 2) z := by
  obtain ⟨U, hUsub, hU, hzU⟩ := _root_.mem_nhds_iff.mp hA
  have hAU : DifferentiableOn ℂ A U := fun y hy => (hUsub hy).differentiableWithinAt
  let T := (InnerProductSpace.toDual ℂ H).symm
  let T' := @IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (StrongDual ℂ H) H _ NormedSpace.complexToReal _ _ T.toIsometryEquiv T.map_zero
  have ht := (contDiff_norm_sq ℂ).comp_contDiffOn
    (T'.contDiff.comp_contDiffOn (FirstPass.contDiffOn_real_of_differentiableOn_complex hAU hU))
  have hs : ContDiffOn ℝ ∞ (fun y => ‖A y‖ ^ 2) U := by
    refine ht.congr fun y _ => ?_
    change ‖A y‖ ^ 2 = ‖T' (A y)‖ ^ 2
    rw [T'.norm_map]
  exact ((hs z hzU).contDiffAt (hU.mem_nhds hzU)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

private theorem levi_eq_of_eventuallyEq {f g : ComplexModel n → ℝ}
    {z : ComplexModel n} (h : f =ᶠ[𝓝 z] g) (v : ComplexModel n) :
    leviForm f z v = leviForm g z v := by
  have h2 := (h.iteratedFDeriv ℝ 2).eq_of_nhds
  simp only [leviForm, realHessian, h2]

/-- The actual SAME prescribed density has a uniform O(1/k) Levi margin off its zeros. -/
theorem exists_uniform_original_density_levi_margin [CompactSpace X]
    (F : FixedChartCover n X) (omega : KahlerBackground n X) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ClosedRealOneOneForm n X)
      (ρ : F.t → ComplexModel n → ℝ),
      (∀ j, IsSmoothLocalPotential θ.val (F.chart j)
        (ball (F.center j) (F.potentialRadius j)) (ρ j)) →
      ∀ x : X, ∃ i : F.t, x ∈ F.cover.U i ∧ ∃ r : ℝ, 0 < r ∧
        ball ((F.chart i).val x) r ⊆ (F.chart i).val.target ∧
        (∀ z ∈ ball ((F.chart i).val x) r, (F.chart i).val.symm z ∈ F.cover.U i) ∧
        ∀ (u : X → EReal), IsThetaPshPotential θ.val u → ∀ k : ℕ, 0 < k →
          ∀ z ∈ ball ((F.chart i).val x) r,
            0 < density F ρ u k ((F.chart i).val.symm z) → ∀ v : ComplexModel n,
              -(C / (k : ℝ) * omega.form.val.coeff (F.chart i) z ![v, Complex.I • v]) ≤
                leviForm (fun w => (k : ℝ)⁻¹ *
                  Real.log (density F ρ u k ((F.chart i).val.symm w)) + ρ i w) z v := by
  classical
  obtain ⟨D, hD, hcut⟩ := exists_uniform_cutoff_error_bound F omega
  let E : ℝ := Real.exp F.CB * D * ((F.t.card : ℝ) + 1)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨2 * E, by positivity, fun θ ρ hρ x => ?_⟩
  obtain ⟨i, hxi, r, g, hr, htarget, hcore, hg, hall⟩ :=
    all_level_holomorphic_kernel_gauges F θ ρ hρ x
  refine ⟨i, hxi, r, hr, htarget, hcore, fun u hu k hk => ?_⟩
  obtain ⟨hBw, hA0, hdensity⟩ := hall u hu k hk
  let J := {j : F.t // x ∈ closure (F.cover.V j)}
  let H : J → Type := fun j => bergmanSubspace
    (ball (F.center j.val) (F.bergmanRadius j.val))
    (fun z => multiplierWeight k (correctedWeight (F.chart j.val) (ρ j.val) u z))
  let : ∀ j : J, CompleteSpace (H j) := fun j =>
    completeSpace_coe_iff_isComplete.mpr (isClosed_bergmanSubspace (hBw j.val)).isComplete
  let A : (j : J) → ComplexModel n → StrongDual ℂ (H j) := fun j z =>
    Complex.exp (((k : ℝ) / 2 : ℝ) * g j z) •
      evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z))
  let c : J → ComplexModel n → ℝ := fun j z => F.cover.χ j.val ((F.chart i).val.symm z)
  let G : ComplexModel n → ℝ := fun z => ∑ j : J, c j z ^ 2 * ‖A j z‖ ^ 2
  have hGeq : ∀ z ∈ ball ((F.chart i).val x) r,
      G z = Real.exp ((k : ℝ) * ρ i z) * density F ρ u k ((F.chart i).val.symm z) := by
    intro z hz
    have h := hdensity z hz
    change density F ρ u k ((F.chart i).val.symm z) = Real.exp (-(k : ℝ) * ρ i z) * G z at h
    rw [h, ← mul_assoc, ← Real.exp_add]
    simp
  have hnorm : ∀ j : J, ∀ z ∈ ball ((F.chart i).val x) r,
      ‖A j z‖ ^ 2 = Real.exp ((k : ℝ) * ρ i z) *
        localDensity F ρ u k j.val ((F.chart i).val.symm z) := by
    intro j z hz
    dsimp only [A]
    have hn := norm_sq_gauged k (g j z)
      (evalCLM (hBw j.val) ((F.chart j.val).val ((F.chart i).val.symm z)))
    rw [hn, ((hg j).2 z hz).1]
    dsimp only [localDensity]
    rw [bergmanSup_eq_ofReal_norm_evalCLM_sq (hBw j.val)
      (show (F.chart j.val).val ((F.chart i).val.symm z) ∈
        ball (F.center j.val) (F.bergmanRadius j.val) from ((hg j).2 z hz).2.2),
      ENNReal.toReal_ofReal (sq_nonneg _)]
    have hex : Real.exp ((k : ℝ) * ρ i z) *
        Real.exp (-(k : ℝ) * ρ j.val ((F.chart j.val).val ((F.chart i).val.symm z))) =
        Real.exp ((k : ℝ) * (ρ i z - ρ j.val ((F.chart j.val).val ((F.chart i).val.symm z)))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hex]
    ring
  intro z hz hS v
  have hzT := htarget hz
  have hGpos : 0 < G z := by rw [hGeq z hz]; exact mul_pos (Real.exp_pos _) hS
  let W : ℝ := omega.form.val.coeff (F.chart i) z ![v, Complex.I • v]
  have hW : 0 ≤ W := omega.isSemipositive (F.chart i) z hzT v
  have hA : ∀ j : J, ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (A j) w := by
    intro j
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (hA0 j).differentiableAt (isOpen_ball.mem_nhds hw)
  have hc : ∀ j : J, ContDiffAt ℝ 2 (c j) z := fun j =>
    ((F.cover.χ_smooth j.val (F.chart i)).contDiffAt
      ((F.chart i).val.open_target.mem_nhds hzT)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hterm : ∀ j : J,
      ‖A j z‖ ^ 2 * (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v) ≤
      Real.exp F.CB * G z * D * W := by
    intro j
    by_cases hy : (F.chart i).val.symm z ∈ F.cover.V j.val
    · have hn : ‖A j z‖ ^ 2 ≤ Real.exp F.CB * G z := by
        rw [hnorm j z hz, hGeq z hz]
        have h := (localDensity_le_exp_CB_mul_density F θ ρ hρ hu hk j.val hy).2
        have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos ((k : ℝ) * ρ i z)).le
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
      have he := hcut j.val (F.chart i) z hzT v
      change Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v ≤ D * W at he
      calc
        _ ≤ ‖A j z‖ ^ 2 * (D * W) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
        _ ≤ (Real.exp F.CB * G z) * (D * W) :=
          mul_le_mul_of_nonneg_right hn (mul_nonneg hD.le hW)
        _ = _ := by ring
    · have he := (cutoff_error_vanishes_off_patch F j.val (F.chart i) hzT hy).2 v |>.2
      change Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v = 0 at he
      rw [he, mul_zero]
      positivity
  have hcard : (Fintype.card J : ℝ) ≤ (F.t.card : ℝ) + 1 := by
    have h := Fintype.card_subtype_le (fun j : F.t => x ∈ closure (F.cover.V j))
    have h' : Fintype.card J ≤ F.t.card := by simpa only [J, Fintype.card_coe] using h
    have hR : (Fintype.card J : ℝ) ≤ (F.t.card : ℝ) := by exact_mod_cast h'
    linarith
  have hnum : (∑ j : J, ‖A j z‖ ^ 2 *
      (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) ≤ E * G z * W := by
    calc
      _ ≤ ∑ j : J, Real.exp F.CB * G z * D * W := Finset.sum_le_sum fun j _ => hterm j
      _ = (Fintype.card J : ℝ) * (Real.exp F.CB * G z * D * W) := by simp
      _ ≤ ((F.t.card : ℝ) + 1) * (Real.exp F.CB * G z * D * W) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by dsimp [E]; ring
  have hL := neg_le_leviForm_log_sum_heterogeneous_dual_of_nonneg H
    (s := 0) le_rfl (by simpa only [add_zero] using hGpos) hc hA v
  change -(2 * _ / (G z + 0)) ≤ leviForm (fun w => Real.log (G w + 0)) z v at hL
  simp only [add_zero] at hL
  have hquot : 2 * (∑ j : J, ‖A j z‖ ^ 2 *
      (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) / G z ≤ 2 * E * W := by
    apply (div_le_iff₀ hGpos).mpr
    nlinarith
  have hlow : -(2 * E * W) ≤ leviForm (fun w => Real.log (G w)) z v := by linarith
  have hG : ContDiffAt ℝ 2 G z :=
    ContDiffAt.sum fun j _ => (hc j).pow 2 |>.mul (smooth_squared_dual_norm (hA j))
  have hlog : ContDiffAt ℝ 2 (fun w => Real.log (G w)) z := hG.log hGpos.ne'
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have heq : (fun w => (k : ℝ)⁻¹ *
      Real.log (density F ρ u k ((F.chart i).val.symm w)) + ρ i w) =ᶠ[𝓝 z]
      ((k : ℝ)⁻¹ • fun w => Real.log (G w)) := by
    have hnear : ∀ᶠ w in 𝓝 z, 0 < G w := hG.continuousAt.eventually (lt_mem_nhds hGpos)
    filter_upwards [isOpen_ball.mem_nhds hz, hnear] with w hw hwG
    have h := hdensity w hw
    change density F ρ u k ((F.chart i).val.symm w) = Real.exp (-(k : ℝ) * ρ i w) * G w at h
    rw [h, Real.log_mul (Real.exp_ne_zero _) hwG.ne', Real.log_exp]
    change (k : ℝ)⁻¹ * (-(k : ℝ) * ρ i w + Real.log (G w)) + ρ i w =
      (k : ℝ)⁻¹ * Real.log (G w)
    field_simp [hkR.ne']
    ring
  rw [levi_eq_of_eventuallyEq heq v, leviForm_smul hlog]
  change -(2 * E / (k : ℝ) * W) ≤ (k : ℝ)⁻¹ * leviForm (fun w => Real.log (G w)) z v
  calc
    _ = (k : ℝ)⁻¹ * (-(2 * E * W)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (inv_pos.mpr hkR).le

end SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityLeviMargin
