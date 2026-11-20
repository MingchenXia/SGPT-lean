import SGPT.Okounkov.TranscendentalWNConv6LineMeasure
import SGPT.Okounkov.TranscendentalWNConv6Product
import SGPT.Okounkov.TranscendentalWNKeyLSCLocal
import SGPT.Toric.ProjectiveLineNativeManifold
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.FubiniStudyLineLevi
import SGPT.Foundations.Analysis.Pending.SubmanifoldRestrictionPositivity
import SGPT.Foundations.Analysis.FirstPass.ClosedFormPullback

/-!
# The complex Hessian of the cutoff obstacles: `dd^c g_k ≤ C e^k ω`

Blueprint `claude-tok-wn-fl3`, node `tok-wn-fl3:obstacle-hessian`; source WN21 §7, proof of
Lemma 7.5: "Since `g_k(τ) = χ(ln|e^{k/2}τ|²) - k - ln(1 + |τ|²)` it follows that
`sup_𝒵 Δ_{ω̃}(g_k ∘ π) ≤ C e^k`" (`references/wn21-restricted-volume`).

* `leviForm_dim_one`, `smoothDensity_dim_one`, `smoothDDC_line_dim_one`: in complex dimension
  one, `dd^c u (v, iv) = |v|² · ρ_u` with `ρ_u = smoothDensity u` the Monge--Ampère density.
* `exists_isSemipositive_smul_sub_ddc_cutoffObstacleLine`: there is `C` with
  `C e^k ω_FS - dd^c g_k ≥ 0` on `ℙ¹` for all `k` (in the affine chart the density of
  `χ(log |τ|² + k)` is `≤ M e^k` and vanishes for `|τ| > 1`, `ω_FS` has density `≥ c > 0` on
  `|τ| ≤ 1`; near `∞` (`|w|² < e^k`) `g_k = -log(1 + |w|²)`, and the remaining points of the other
  chart are transported by the chart change).
* `exists_ddc_cutoffObstacleLine_comp_le`: for a holomorphic `q : Y → ℙ¹` from a compact Kähler
  manifold `(Y, A)` there is `C` with `dd^c(g_k ∘ q) ≤ C e^k A` on complex lines, for all `k`
  (pullback of the semipositive form and domination of `q^*ω_FS` by `A`).  With
  `q = pr₂ ∘ μ ∘ π` and `A = ω̃` this is the hypothesis `dd^c(g_k ∘ π) ≤ S_k ω̃`, `S_k = C e^k`,
  of `exists_lineBound_resolvedEnvelope`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Toric

/-! ### Complex dimension one -/

/-- In complex dimension one the Levi form is `|v|²` times its value on the unit vector. -/
theorem leviForm_dim_one (u : ComplexModel 1 → ℝ) (z v : ComplexModel 1) :
    leviForm u z v = ‖v‖ ^ 2 * leviForm u z (coordinateVector 0) := by
  set e : ComplexModel 1 := coordinateVector 0 with he
  set a : ℝ := (v 0).re with ha
  set b : ℝ := (v 0).im with hb
  have hv : v = a • e + b • (Complex.I • e) := by
    ext i
    fin_cases i
    simp only [he, coordinateVector, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      if_true, smul_eq_mul, mul_one, Fin.zero_eta]
    apply Complex.ext <;> simp [ha, hb]
  have hIv : Complex.I • v = a • (Complex.I • e) + (-b) • e := by
    ext i
    fin_cases i
    simp only [he, coordinateVector, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
      if_true, smul_eq_mul, mul_one, Fin.zero_eta]
    apply Complex.ext <;> simp [ha, hb]
  have hn : ‖v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [norm_sq_eq_zero_coord, Complex.sq_norm, Complex.normSq_apply, ha, hb]
    ring
  simp only [leviForm, realHessian_eq_fderiv]
  rw [hn, hIv, hv]
  simp only [map_add, map_smul, FunLike.coe_add, FunLike.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- In complex dimension one, the Monge--Ampère density is the Levi form on the unit vector,
divided by `π`. -/
theorem smoothDensity_dim_one (u : ComplexModel 1 → ℝ) (z : ComplexModel 1) :
    smoothDensity u z = leviForm u z (coordinateVector 0) / Real.pi := by
  rw [smoothDensity, Matrix.det_fin_one]
  simp only [complexHessian, leviForm, Nat.factorial_one, Nat.cast_one, pow_one]
  simp [Complex.add_re, Complex.mul_re]
  ring

/-- **`dd^c u (v, iv) = |v|² ρ_u` in complex dimension one.** -/
theorem smoothDDC_line_dim_one {u : ComplexModel 1 → ℝ} {z : ComplexModel 1}
    (hu : ContDiffAt ℝ 2 u z) (v : ComplexModel 1) :
    smoothDDC u z ![v, Complex.I • v] = ‖v‖ ^ 2 * smoothDensity u z := by
  rw [FubiniStudyLineLevi.quad_smoothDDC_eq_leviForm hu v, leviForm_dim_one,
    smoothDensity_dim_one]
  ring

/-! ### Densities on the affine line -/

/-- `ρ_{χ(log |τ|² + k)} ≤ M e^k`. -/
theorem exists_cutoffLineDensity_le {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (k : ℕ) (z : ComplexModel 1), cutoffLineDensity χ k z ≤ M * Real.exp k := by
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 0)).exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num)) hχ.continuous_deriv2.continuousOn
  set M₀ := deriv (deriv χ) x₀ with hM₀
  have hM₀0 : 0 ≤ M₀ := hχ.deriv2_nonneg x₀
  refine ⟨(1 + Real.exp 1 * M₀) / Real.pi, by positivity, fun k z => ?_⟩
  have hek : 0 < Real.exp k := Real.exp_pos _
  rcases lt_or_ge (Real.exp k * ‖z 0‖ ^ 2) (Real.exp (-1)) with hs | hs
  · rw [cutoffLineDensity_eq_of_small hχ k hs, div_mul_eq_mul_div]
    gcongr
    nlinarith [Real.exp_pos 1, mul_nonneg (Real.exp_pos 1).le hM₀0]
  · have hz : z 0 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hs
      simp at hs
      linarith [Real.exp_pos (-1)]
    have hn : 0 < ‖z 0‖ ^ 2 := by positivity
    rw [cutoffLineDensity_eq_of_ne hχ k hz]
    set s := Real.log (‖z 0‖ ^ 2) + k with hsdef
    have hs1 : -1 ≤ s := by
      have := Real.log_le_log (Real.exp_pos _) hs
      rw [Real.log_exp, Real.log_mul hek.ne' hn.ne', Real.log_exp] at this
      linarith
    have hinv : 1 / ‖z 0‖ ^ 2 ≤ Real.exp 1 * Real.exp k := by
      rw [div_le_iff₀ hn, ← Real.exp_add]
      have h1 : Real.exp (-1) ≤ Real.exp k * ‖z 0‖ ^ 2 := hs
      calc (1 : ℝ) = Real.exp (1 + k) * Real.exp (-1 - k) := by
            rw [← Real.exp_add]; ring_nf; exact Real.exp_zero.symm
        _ ≤ Real.exp (1 + k) * ‖z 0‖ ^ 2 := by
            gcongr
            rw [show (-1 - (k : ℝ)) = -1 + -(k : ℝ) by ring, Real.exp_add]
            calc Real.exp (-1) * Real.exp (-(k : ℝ)) ≤
                (Real.exp k * ‖z 0‖ ^ 2) * Real.exp (-(k : ℝ)) :=
                  mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
              _ = ‖z 0‖ ^ 2 := by
                  rw [mul_comm (Real.exp k), mul_assoc, ← Real.exp_add]; simp
    have hd2 : deriv (deriv χ) s ≤ M₀ := by
      rcases le_or_gt s 0 with hs0 | hs0
      · exact hx₀ ⟨hs1, hs0⟩
      · rw [hχ.deriv2_of_pos hs0]; exact hM₀0
    have hd0 : 0 ≤ deriv (deriv χ) s := hχ.deriv2_nonneg s
    rw [div_le_iff₀ (by positivity)]
    calc deriv (deriv χ) s ≤ M₀ := hd2
      _ ≤ M₀ * (‖z 0‖ ^ 2 * (Real.exp 1 * Real.exp k)) := by
          have : 1 ≤ ‖z 0‖ ^ 2 * (Real.exp 1 * Real.exp k) := by
            rw [one_div, inv_le_iff_one_le_mul₀ hn] at hinv; linarith
          nlinarith
      _ ≤ (1 + Real.exp 1 * M₀) / Real.pi * Real.exp k * (Real.pi * ‖z 0‖ ^ 2) := by
          have hπ : 0 < Real.pi := Real.pi_pos
          have hR : (1 + Real.exp 1 * M₀) / Real.pi * Real.exp k * (Real.pi * ‖z 0‖ ^ 2) =
              (1 + Real.exp 1 * M₀) * (Real.exp k * ‖z 0‖ ^ 2) := by
            field_simp
          rw [hR]
          nlinarith [mul_pos hn hek]

/-- `ρ_{χ(log |τ|² + k)} = 0` where `eᵏ |τ|² > 1`. -/
theorem cutoffLineDensity_eq_zero {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ) {z : ComplexModel 1}
    (hz : 1 < Real.exp k * ‖z 0‖ ^ 2) : cutoffLineDensity χ k z = 0 := by
  have hz0 : z 0 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz; simp at hz; linarith
  have hn : 0 < ‖z 0‖ ^ 2 := by positivity
  rw [cutoffLineDensity_eq_of_ne hχ k hz0, hχ.deriv2_of_pos, zero_div]
  have := Real.log_lt_log one_pos hz
  rw [Real.log_one, Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp] at this
  linarith

/-- The Fubini--Study density is bounded below on the closed unit disc. -/
theorem exists_smoothDensity_projectiveFSPotential_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ComplexModel 1, ‖z 0‖ ≤ 1 →
      c ≤ smoothDensity projectiveFSPotential z := by
  have hK : IsCompact (closedBall (0 : ComplexModel 1) 1) := isCompact_closedBall _ _
  have hcont : ContinuousOn (smoothDensity projectiveFSPotential) (closedBall 0 1) :=
    fun z _ => (LSC.continuousAt_smoothDensity
      contDiff_projectiveFSPotential.contDiffAt).continuousWithinAt
  obtain ⟨z₀, -, hz₀⟩ := hK.exists_isMinOn ⟨0, mem_closedBall_self zero_le_one⟩ hcont
  have hpos : ∀ z, 0 < smoothDensity projectiveFSPotential z := by
    intro z
    have h0 := projectiveFSForm_strictlyPositive false z coordinateVector_zero_ne
    have h : 0 < smoothDDC projectiveFSPotential z
        ![coordinateVector 0, Complex.I • coordinateVector 0] := h0
    rw [smoothDDC_line_dim_one (contDiff_projectiveFSPotential.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))] at h
    have hn : ‖(coordinateVector 0 : ComplexModel 1)‖ ^ 2 = 1 := by
      simp [coordinateVector]
    rwa [hn, one_mul] at h
  refine ⟨_, hpos z₀, fun z hz => hz₀ ?_⟩
  rw [mem_closedBall, dist_zero_right, ← sq_le_one_iff₀ (norm_nonneg _), norm_sq_eq_zero_coord]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mpr hz

/-! ### `dd^c g_k ≤ C e^k ω_FS` on `ℙ¹` -/

theorem projectiveModelChart_false_symm (z : ComplexModel 1) :
    (projectiveModelChart false).symm z = affineLinePoint (z 0) := by
  rw [projectiveModelChart_symm_eq_mk, affineLinePoint_eq_mk]
  congr 1

theorem projectiveModelChart_true_symm_of_ne {z : ComplexModel 1} (hz : z 0 ≠ 0) :
    (projectiveModelChart true).symm z = affineLinePoint (z 0)⁻¹ := by
  rw [projectiveModelChart_symm_eq_mk, affineLinePoint_eq_mk]
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 (z 0) hz, ?_⟩
  ext i
  fin_cases i <;> simp [projectiveAffineLift, projectiveModelEquiv_symm_apply, hz]

theorem affineLinePoint_mem_source_false (τ : ℂ) :
    affineLinePoint τ ∈ (projectiveModelChart false).source := by
  have h := projectiveModelChart_false_symm (projectiveModelEquiv τ)
  rw [projectiveModelEquiv_apply_zero] at h
  rw [← h]
  exact (projectiveModelChart false).map_target (by
    rw [projectiveModelChart_target_eq]; exact mem_univ _)

/-- **`C e^k ω_FS - dd^c g_k ≥ 0` on `ℙ¹`** for a constant `C` independent of `k`. -/
theorem exists_isSemipositive_smul_sub_ddc_cutoffObstacleLine {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ((C * Real.exp k) • projectiveNativeFSBackground.form -
      ddcClosedForm (cutoffObstacleLine χ k) (chartSmooth_cutoffObstacleLine hχ k)).val.IsSemipositive := by
  obtain ⟨M, hM, hMk⟩ := exists_cutoffLineDensity_le hχ
  obtain ⟨c, hc, hcz⟩ := exists_smoothDensity_projectiveFSPotential_ge
  refine ⟨M / c, div_pos hM hc, fun k => ?_⟩
  set A := (M / c * Real.exp k) • projectiveNativeFSBackground.form -
    ddcClosedForm (cutoffObstacleLine χ k) (chartSmooth_cutoffObstacleLine hχ k) with hA
  have hek : 0 < Real.exp k := Real.exp_pos _
  have hFS2 : ∀ w : ComplexModel 1, ContDiffAt ℝ 2 projectiveFSPotential w := fun w =>
    contDiff_projectiveFSPotential.contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hFSnn : ∀ w u, 0 ≤ smoothDDC projectiveFSPotential w ![u, Complex.I • u] := fun w u => by
    rw [smoothDDC_line_dim_one (hFS2 w)]
    exact mul_nonneg (sq_nonneg _) (smoothDensity_projectiveFSPotential_nonneg w)
  have hcoeffA : ∀ (e : ComplexChart 1 ProjectiveLine) (w : ComplexModel 1) (u : ComplexModel 1),
      A.val.coeff e w ![u, Complex.I • u] =
        M / c * Real.exp k * smoothDDC projectiveFSPotential w ![u, Complex.I • u] -
          smoothDDC (fun y => cutoffObstacleLine χ k (e.val.symm y)) w ![u, Complex.I • u] := by
    intro e w u
    rw [hA, BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul, ddcClosedForm_coeff]
    rfl
  -- the affine chart
  have hfalse : ∀ w u, 0 ≤ A.val.coeff (projectiveNativeChart false) w ![u, Complex.I • u] := by
    intro w u
    rw [hcoeffA]
    have hfun : (fun y => cutoffObstacleLine χ k ((projectiveNativeChart false).val.symm y)) =
        fun y => (cutoffLineProfile χ k y - k) - projectiveFSPotential y := by
      funext y
      exact cutoffObstacleLine_chart_false χ k y
    rw [hfun, smoothDDC_sub isOpen_univ ((contDiff_cutoffLineProfile hχ k).sub
      contDiff_const).contDiffOn contDiff_projectiveFSPotential.contDiffOn (mem_univ w),
      smoothDDC_sub isOpen_univ (contDiff_cutoffLineProfile hχ k).contDiffOn contDiffOn_const
      (mem_univ w), GlobalPotentialTransforms.smoothDDC_const, sub_zero]
    simp only [ContinuousAlternatingMap.sub_apply]
    have hP2 : ContDiffAt ℝ 2 (cutoffLineProfile χ k) w :=
      (contDiff_cutoffLineProfile hχ k).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    rw [smoothDDC_line_dim_one hP2, smoothDDC_line_dim_one (hFS2 w)]
    have hρ : cutoffLineDensity χ k w ≤ M / c * Real.exp k * smoothDensity projectiveFSPotential w := by
      rcases le_or_gt ‖w 0‖ 1 with hw | hw
      · calc cutoffLineDensity χ k w ≤ M * Real.exp k := hMk k w
          _ = M / c * Real.exp k * c := by field_simp
          _ ≤ M / c * Real.exp k * smoothDensity projectiveFSPotential w :=
              mul_le_mul_of_nonneg_left (hcz w hw) (by positivity)
      · have h1 : 1 < Real.exp k * ‖w 0‖ ^ 2 := by
          have : 1 < ‖w 0‖ ^ 2 := by nlinarith
          nlinarith [Real.one_le_exp (Nat.cast_nonneg (α := ℝ) k)]
        rw [cutoffLineDensity_eq_zero hχ k h1]
        exact mul_nonneg (by positivity) (smoothDensity_projectiveFSPotential_nonneg w)
    have hFSd := smoothDensity_projectiveFSPotential_nonneg w
    unfold cutoffLineDensity at hρ
    nlinarith [sq_nonneg ‖u‖, mul_le_mul_of_nonneg_left hρ (sq_nonneg ‖u‖),
      mul_nonneg (sq_nonneg ‖u‖) hFSd]
  intro e z hz u
  obtain ⟨i, hi⟩ := (mem_projectiveNativeAtlas_iff e.val).mp e.property
  have he : e = projectiveNativeChart i := Subtype.ext hi
  subst he
  cases i
  · exact hfalse z u
  · rcases lt_or_ge (‖z 0‖ ^ 2) (Real.exp k) with hzk | hzk
    · -- near `∞`, `g_k = -log(1 + |w|²)`
      rw [hcoeffA]
      have hn := contDiff_normSq_zero
      have hev : (fun y => cutoffObstacleLine χ k ((projectiveNativeChart true).val.symm y)) =ᶠ[𝓝 z]
          fun y => -projectiveFSPotential y := by
        filter_upwards [hn.continuous.continuousAt.eventually (gt_mem_nhds hzk)] with y hy
        rw [projectiveNativeChart_val, cutoffObstacleLine_chart_true_of_small hχ k hy,
          projectiveFSPotential_eq, ← Complex.sq_norm]
      rw [smoothDDC_congr hev, smoothDDC_neg isOpen_univ contDiff_projectiveFSPotential.contDiffOn
        (mem_univ z)]
      simp only [ContinuousAlternatingMap.neg_apply, sub_neg_eq_add]
      have := hFSnn z u
      positivity
    · -- transport to the affine chart
      have hz0 : z 0 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hzk
        simp at hzk
        linarith [Real.one_le_exp (Nat.cast_nonneg (α := ℝ) k)]
      have hsrc : z ∈ (chartTransition (projectiveNativeChart true)
          (projectiveNativeChart false)).source := by
        refine ⟨hz, ?_⟩
        show (projectiveModelChart true).symm z ∈ (projectiveModelChart false).source
        rw [projectiveModelChart_true_symm_of_ne hz0]
        exact affineLinePoint_mem_source_false _
      rw [KahlerDomination.lineValue_compatible A.val _ _ hsrc u]
      exact hfalse _ _

/-! ### Pullback to a compact Kähler manifold -/

section Pullback

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y]

/-- **`dd^c(g_k ∘ q) ≤ C e^k A`** for a holomorphic `q : Y → ℙ¹` from a compact Kähler manifold
`(Y, A)`, with `C` independent of `k` (WN21 §7, proof of Lemma 7.5, with `q = pr₂ ∘ μ ∘ π`). -/
theorem exists_ddc_cutoffObstacleLine_comp_le (A : KahlerBackground N Y) {q : Y → ProjectiveLine}
    (hq : ContMDiff 𝓘(ℂ, ComplexModel N) 𝓘(ℂ, ComplexModel 1) ∞ q)
    {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N,
        (ddcClosedForm (fun y => cutoffObstacleLine χ k (q y))
          (ProductTestForms.chartSmooth_comp hq (chartSmooth_cutoffObstacleLine hχ k))).val.coeff
            e z ![v, Complex.I • v] ≤
          C * Real.exp k * A.form.val.coeff e z ![v, Complex.I • v] := by
  obtain ⟨C₀, hC₀, hsemi⟩ := exists_isSemipositive_smul_sub_ddc_cutoffObstacleLine hχ
  obtain ⟨B, hB, hBsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul A
    (-(ClosedRealOneOneForm.pullback hq projectiveNativeFSBackground.form))
  refine ⟨C₀ * B, mul_pos hC₀ hB, fun k e z hz v => ?_⟩
  set d := complexChartAt (n := 1) (q (e.val.symm z)) with hd
  have hzd : z ∈ coordinateDomain q e d :=
    ⟨hz, show q (e.val.symm z) ∈ d.val.source from mem_complexChartAt_source _⟩
  set ωF := projectiveNativeFSBackground.form with hωF
  set G := ddcClosedForm (cutoffObstacleLine χ k) (chartSmooth_cutoffObstacleLine hχ k) with hG
  -- the pulled-back semipositivity
  have h1 := ClosedRealOneOneForm.pullback_isSemipositive hq (hsemi k) e z hz v
  rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hq _ e d hzd] at h1
  have hω' : (ClosedRealOneOneForm.pullback hq ωF).val.coeff e z ![v, Complex.I • v] =
      ((ωF.val.coeff d (coordinateMap q e d z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap q e d) z)) ![v, Complex.I • v] := by
    rw [ClosedRealOneOneForm.pullback_val, SmoothRealForm.pullback_coeff hq _ e d hzd]
  have hG' : (ddcClosedForm (fun y => cutoffObstacleLine χ k (q y))
      (ProductTestForms.chartSmooth_comp hq (chartSmooth_cutoffObstacleLine hχ k))).val.coeff
        e z ![v, Complex.I • v] =
      ((G.val.coeff d (coordinateMap q e d z)).compContinuousLinearMap
        (fderiv ℝ (coordinateMap q e d) z)) ![v, Complex.I • v] := by
    rw [← SubmanifoldRestrictionPositivity.pullback_ddcClosedForm_coeff hq
      (chartSmooth_cutoffObstacleLine hχ k) e hz, SmoothRealForm.pullback_coeff hq _ e d hzd]
  have h2 := (hBsemi e z hz v)
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    ClosedRealOneOneForm.coeff_smul] at h2
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h2
  rw [hω'] at h2
  rw [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_smul] at h1
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 h2
  rw [hG']
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hek : 0 < Real.exp k := Real.exp_pos _
  nlinarith [mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos hC₀ hek))]

end Pullback

end SGPT.Okounkov.TranscendentalWN
