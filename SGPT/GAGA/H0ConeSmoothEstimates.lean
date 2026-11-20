import SGPT.GAGA.H0ConeSmoothExtension

/-!
# Estimates for the smooth homogeneous extension


For gluing data `Gd` of a closed cone `C ⊆ ℂ^m` and a function `F` homogeneous of degree
`k ≥ 2` and locally holomorphic on `C ∖ {0}` (`SGPT.GAGA.H0.GluingData`), the glued extension
`G = Gd.glued`, extended by `0` at the vertex (`GluingData.ext0`), satisfies:

* `GluingData.contDiff_ext0`: `G` is `C¹` on `ℂ^m` (smooth off `0`, `|G| ≤ A|Z|^k`,
  `|DG| ≤ A'|Z|^{k-1}`);
* `GluingData.ext0_eq`: `G = F` on `C`;
* `GluingData.dbarNormSq_ext0_le`: `|∂̄G(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²` (mean value inequality
  for `∂̄G`, which vanishes on `C ∖ {0}`, on the shell `1/2 < |Z| < 3/2`, and homogeneity of
  degree `k - 1` of `∂̄G` and `1` of `dist(·, C)`).

`exists_smoothExtension` packages these.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric
open scoped Topology ContDiff Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.PSH.GlobalL2

variable {m : ℕ}

/-- A cone is invariant under nonzero scalars as a set. -/
theorem smul_cone_eq {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {c : ℂ} (hc : c ≠ 0) :
    c • C = C := by
  ext Z
  constructor
  · rintro ⟨Y, hY, rfl⟩
    exact hC c Y hY
  · intro hZ
    refine ⟨c⁻¹ • Z, hC _ Z hZ, ?_⟩
    show c • (c⁻¹ • Z) = Z
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- `dist(c Z, C) = |c| dist(Z, C)` for a cone `C` and `c ≠ 0`. -/
theorem infDist_smul_cone {C : Set (ComplexModel m)}
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {c : ℂ} (hc : c ≠ 0)
    (Z : ComplexModel m) : infDist (c • Z) C = ‖c‖ * infDist Z C := by
  conv_lhs => rw [← smul_cone_eq hC hc]
  exact infDist_smul₀ hc C Z

namespace GluingData

variable {C : Set (ComplexModel m)} {k : ℕ} {F : ComplexModel m → ℂ} (Gd : GluingData C k F)

theorem differentiableAt_glued {Z : ComplexModel m} (hZ : Z ≠ 0) :
    DifferentiableAt ℝ Gd.glued Z :=
  (Gd.contDiffAt_glued hZ).differentiableAt (by simp)

/-- The derivative of `G` is homogeneous of degree `k - 1`. -/
theorem fderiv_glued_smul (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) {Z : ComplexModel m} (hZ : Z ≠ 0)
    (v : ComplexModel m) :
    fderiv ℝ Gd.glued ((t : ℂ) • Z) v = ((t ^ (k - 1) : ℝ) : ℂ) * fderiv ℝ Gd.glued Z v := by
  set S : ComplexModel m →L[ℝ] ComplexModel m := t • ContinuousLinearMap.id ℝ (ComplexModel m)
    with hS
  have hSZ : ∀ Y, S Y = (t : ℂ) • Y := fun Y => by
    rw [hS, smul_apply, ContinuousLinearMap.id_apply, Complex.coe_smul]
  have htZ : (t : ℂ) • Z ≠ 0 := smul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') hZ
  have h1 : HasFDerivAt (fun Y => Gd.glued (S Y))
      ((fderiv ℝ Gd.glued (S Z)).comp S) Z := by
    have hd : HasFDerivAt Gd.glued (fderiv ℝ Gd.glued (S Z)) (S Z) := by
      rw [hSZ]; exact (Gd.differentiableAt_glued htZ).hasFDerivAt
    exact hd.comp Z S.hasFDerivAt
  have h2 : HasFDerivAt (fun Y => Gd.glued (S Y))
      (((t : ℂ) ^ k) • fderiv ℝ Gd.glued Z) Z := by
    have heq : (fun Y => Gd.glued (S Y)) = fun Y => (t : ℂ) ^ k * Gd.glued Y := by
      funext Y; rw [hSZ, Gd.glued_smul ht]
    rw [heq]
    exact (Gd.differentiableAt_glued hZ).hasFDerivAt.const_mul _
  have huniq := h1.unique h2
  have hv := congrArg (fun L : ComplexModel m →L[ℝ] ℂ => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul] at hv
  rw [hSZ, hSZ] at hv
  have hlin : ∀ X : ComplexModel m, fderiv ℝ Gd.glued X ((t : ℂ) • v) =
      (t : ℂ) * fderiv ℝ Gd.glued X v := fun X => by
    rw [Complex.coe_smul, ContinuousLinearMap.map_smul, Complex.real_smul]
  rw [hlin] at hv
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ k = (t : ℂ) * (t : ℂ) ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, mul_assoc] at hv
  rw [mul_left_cancel₀ htne hv]
  push_cast
  ring

/-- `∂̄G` is homogeneous of degree `k - 1`. -/
theorem dbarDir_glued_smul (hk : 1 ≤ k) {t : ℝ} (ht : 0 < t) {Z : ComplexModel m} (hZ : Z ≠ 0)
    (v : ComplexModel m) :
    dbarDir v Gd.glued ((t : ℂ) • Z) = ((t ^ (k - 1) : ℝ) : ℂ) * dbarDir v Gd.glued Z := by
  simp only [dbarDir, Gd.fderiv_glued_smul hk ht hZ]
  ring

/-- `|G(Z)| ≤ A |Z|^k`. -/
theorem exists_norm_glued_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ Z : ComplexModel m, Z ≠ 0 →
    ‖Gd.glued Z‖ ≤ A * ‖Z‖ ^ k := by
  have hcont : ContinuousOn Gd.glued (sphere (0 : ComplexModel m) 1) := fun Z hZ =>
    (Gd.contDiffAt_glued (ne_of_mem_sphere hZ one_ne_zero)).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : ComplexModel m) 1).exists_bound_of_continuousOn hcont
  refine ⟨max A 0, le_max_right _ _, fun Z hZ => ?_⟩
  have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hu : unitMap Z ∈ sphere (0 : ComplexModel m) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact norm_unitMap hZ
  conv_lhs => rw [eq_norm_smul_unitMap hZ, Gd.glued_smul hn]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, mul_comm]
  gcongr
  exact (hA _ hu).trans (le_max_left _ _)

theorem continuousAt_fderiv_glued {Z : ComplexModel m} (hZ : Z ≠ 0) :
    ContinuousAt (fderiv ℝ Gd.glued) Z :=
  ((Gd.contDiffAt_glued hZ).fderiv_right (m := 0) (by simp)).continuousAt

/-- `|DG(Z)| ≤ A' |Z|^{k-1}`. -/
theorem exists_norm_fderiv_glued_le (hk : 1 ≤ k) : ∃ A : ℝ, 0 ≤ A ∧ ∀ Z : ComplexModel m,
    Z ≠ 0 → ‖fderiv ℝ Gd.glued Z‖ ≤ A * ‖Z‖ ^ (k - 1) := by
  have hcont : ContinuousOn (fderiv ℝ Gd.glued) (sphere (0 : ComplexModel m) 1) := fun Z hZ =>
    (Gd.continuousAt_fderiv_glued (ne_of_mem_sphere hZ one_ne_zero)).continuousWithinAt
  obtain ⟨A, hA⟩ := (isCompact_sphere (0 : ComplexModel m) 1).exists_bound_of_continuousOn hcont
  refine ⟨max A 0, le_max_right _ _, fun Z hZ => ?_⟩
  have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hu : unitMap Z ∈ sphere (0 : ComplexModel m) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact norm_unitMap hZ
  have hu0 : unitMap Z ≠ 0 := ne_of_mem_sphere hu one_ne_zero
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  conv_lhs => rw [eq_norm_smul_unitMap hZ, Gd.fderiv_glued_smul hk hn hu0]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖Z‖ ^ (k - 1) * ‖fderiv ℝ Gd.glued (unitMap Z) v‖
      ≤ ‖Z‖ ^ (k - 1) * (‖fderiv ℝ Gd.glued (unitMap Z)‖ * ‖v‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Z‖ ^ (k - 1) * (max A 0 * ‖v‖) := by
        gcongr; exact (hA _ hu).trans (le_max_left _ _)
    _ = max A 0 * ‖Z‖ ^ (k - 1) * ‖v‖ := by ring

/-- The glued extension, set to `0` at the vertex. -/
def ext0 (Z : ComplexModel m) : ℂ := if Z = 0 then 0 else Gd.glued Z

theorem ext0_eventuallyEq {Z : ComplexModel m} (hZ : Z ≠ 0) : Gd.ext0 =ᶠ[𝓝 Z] Gd.glued := by
  filter_upwards [isOpen_ne.mem_nhds hZ] with Y hY
  simp [ext0, hY]

theorem hasFDerivAt_ext0_zero (hk : 2 ≤ k) :
    HasFDerivAt Gd.ext0 (0 : ComplexModel m →L[ℝ] ℂ) 0 := by
  obtain ⟨A, hA0, hA⟩ := Gd.exists_norm_glued_le
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
  have hball : ∀ᶠ h in 𝓝 (0 : ComplexModel m), ‖h‖ < min 1 (c / (A + 1)) := by
    have := isOpen_ball.mem_nhds (mem_ball_self (x := (0 : ComplexModel m))
      (lt_min one_pos (div_pos hc (by linarith : (0 : ℝ) < A + 1))))
    filter_upwards [this] with h hh
    exact mem_ball_zero_iff.mp hh
  filter_upwards [hball] with h hh
  simp only [zero_add, zero_apply, sub_zero]
  have hext00 : Gd.ext0 0 = 0 := by simp [ext0]
  rw [hext00, sub_zero]
  by_cases h0 : h = 0
  · simp [ext0, h0]
  · simp only [ext0, h0, if_false]
    have h1 : ‖h‖ < 1 := lt_of_lt_of_le hh (min_le_left _ _)
    have h2 : ‖h‖ < c / (A + 1) := lt_of_lt_of_le hh (min_le_right _ _)
    have hnn := norm_nonneg h
    calc ‖Gd.glued h‖ ≤ A * ‖h‖ ^ k := hA h h0
      _ ≤ A * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hnn h1.le hk) hA0
      _ = (A * ‖h‖) * ‖h‖ := by ring
      _ ≤ c * ‖h‖ := by
          gcongr
          have : A * ‖h‖ ≤ (A + 1) * ‖h‖ := by nlinarith
          calc A * ‖h‖ ≤ (A + 1) * ‖h‖ := this
            _ ≤ (A + 1) * (c / (A + 1)) := by gcongr
            _ = c := by field_simp

theorem fderiv_ext0_zero (hk : 2 ≤ k) : fderiv ℝ Gd.ext0 (0 : ComplexModel m) = 0 :=
  (Gd.hasFDerivAt_ext0_zero hk).fderiv

theorem fderiv_ext0_eq {Z : ComplexModel m} (hZ : Z ≠ 0) :
    fderiv ℝ Gd.ext0 Z = fderiv ℝ Gd.glued Z :=
  (Gd.ext0_eventuallyEq hZ).fderiv_eq

/-- **The extension is `C¹` on `ℂ^m`** (`k ≥ 2`). -/
theorem contDiff_ext0 (hk : 2 ≤ k) : ContDiff ℝ 1 Gd.ext0 := by
  rw [contDiff_one_iff_fderiv]
  constructor
  · intro Z
    by_cases hZ : Z = 0
    · subst hZ; exact (Gd.hasFDerivAt_ext0_zero hk).differentiableAt
    · exact (Gd.differentiableAt_glued hZ).congr_of_eventuallyEq (Gd.ext0_eventuallyEq hZ)
  · rw [continuous_iff_continuousAt]
    intro Z
    by_cases hZ : Z = 0
    · subst hZ
      obtain ⟨A, hA0, hA⟩ := Gd.exists_norm_fderiv_glued_le (by omega)
      rw [ContinuousAt, Gd.fderiv_ext0_zero hk, tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun Y => norm_nonneg _) (fun Y => ?_) (g := fun Y => A * ‖Y‖ ^ (k - 1))
        ?_
      · by_cases hY : Y = 0
        · rw [hY, Gd.fderiv_ext0_zero hk, norm_zero]; positivity
        · rw [Gd.fderiv_ext0_eq hY]; exact hA Y hY
      · have : Tendsto (fun Y : ComplexModel m => A * ‖Y‖ ^ (k - 1)) (𝓝 0)
            (𝓝 (A * ‖(0 : ComplexModel m)‖ ^ (k - 1))) :=
          (continuous_const.mul (continuous_norm.pow _)).tendsto 0
        rwa [norm_zero, zero_pow (by omega), mul_zero] at this
    · have heq : fderiv ℝ Gd.ext0 =ᶠ[𝓝 Z] fderiv ℝ Gd.glued := by
        filter_upwards [isOpen_ne.mem_nhds hZ] with Y hY
        exact Gd.fderiv_ext0_eq hY
      exact (Gd.continuousAt_fderiv_glued hZ).congr heq.symm

theorem ext0_eq (hk : 1 ≤ k) (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
    (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    {Z : ComplexModel m} (hZ : Z ∈ C) : Gd.ext0 Z = F Z := by
  by_cases h0 : Z = 0
  · subst h0
    have h := hF 0 0 hZ
    rw [zero_smul, zero_pow (by omega), zero_mul] at h
    simp [ext0, h]
  · simp only [ext0, h0, if_false]
    exact Gd.glued_eq hC hZ h0

/-! ### The `∂̄`-estimate -/

/-- The components `∂̄_j G` are smooth off `0`. -/
theorem contDiffAt_dbarDir_glued (v : ComplexModel m) {Z : ComplexModel m} (hZ : Z ≠ 0) :
    ContDiffAt ℝ 1 (dbarDir v Gd.glued) Z := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ Gd.glued) Z :=
    (Gd.contDiffAt_glued hZ).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiffAt ℝ 1 (fun Y => fderiv ℝ Gd.glued Y v) Z :=
    hD.clm_apply contDiffAt_const
  have h2 : ContDiffAt ℝ 1 (fun Y => fderiv ℝ Gd.glued Y (Complex.I • v)) Z :=
    hD.clm_apply contDiffAt_const
  exact ((h1.add (contDiffAt_const.mul h2)).div_const (2 : ℂ))

theorem continuousAt_fderiv_dbarDir_glued (v : ComplexModel m) {Z : ComplexModel m}
    (hZ : Z ≠ 0) : ContinuousAt (fderiv ℝ (dbarDir v Gd.glued)) Z := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ Gd.glued) Z :=
    (Gd.contDiffAt_glued hZ).fderiv_right (m := 2) (WithTop.coe_le_coe.mpr le_top)
  have h1 : ContDiffAt ℝ 2 (fun Y => fderiv ℝ Gd.glued Y v) Z :=
    hD.clm_apply contDiffAt_const
  have h2 : ContDiffAt ℝ 2 (fun Y => fderiv ℝ Gd.glued Y (Complex.I • v)) Z :=
    hD.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℝ 2 (dbarDir v Gd.glued) Z :=
    ((h1.add (contDiffAt_const.mul h2)).div_const (2 : ℂ))
  exact (h3.fderiv_right (m := 0) (by norm_num)).continuousAt

variable (hCc : IsClosed C) (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C)
include hCc hC

/-- On the unit sphere, `|∂̄_v G(W)| ≤ M dist(W, C)`. -/
theorem exists_dbarDir_le_on_sphere (hCne : C.Nonempty) (v : ComplexModel m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ W : ComplexModel m, ‖W‖ = 1 →
      ‖dbarDir v Gd.glued W‖ ≤ M * infDist W C := by
  set K : Set (ComplexModel m) := closedBall 0 (3 / 2) \ ball 0 (1 / 2) with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 _).diff isOpen_ball
  have hK0 : ∀ Y ∈ K, Y ≠ 0 := by
    intro Y hY h0
    apply hY.2
    rw [h0]; exact mem_ball_self (by norm_num)
  obtain ⟨B₁, hB₁⟩ := hKc.exists_bound_of_continuousOn (f := fderiv ℝ (dbarDir v Gd.glued))
    fun Y hY => (Gd.continuousAt_fderiv_dbarDir_glued v (hK0 Y hY)).continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := (isCompact_sphere (0 : ComplexModel m) 1).exists_bound_of_continuousOn
    (f := dbarDir v Gd.glued) fun Y hY =>
      (Gd.contDiffAt_dbarDir_glued v (ne_of_mem_sphere hY one_ne_zero)).continuousAt.continuousWithinAt
  refine ⟨max (max B₁ 0) (2 * max B₀ 0), le_max_of_le_left (le_max_right _ _), fun W hW => ?_⟩
  by_cases hfar : 1 / 2 ≤ infDist W C
  · have h1 : ‖dbarDir v Gd.glued W‖ ≤ max B₀ 0 :=
      (hB₀ W (by rw [mem_sphere_zero_iff_norm]; exact hW)).trans (le_max_left _ _)
    calc ‖dbarDir v Gd.glued W‖ ≤ max B₀ 0 := h1
      _ = (2 * max B₀ 0) * (1 / 2) := by ring
      _ ≤ (2 * max B₀ 0) * infDist W C := by gcongr
      _ ≤ max (max B₁ 0) (2 * max B₀ 0) * infDist W C := by
          gcongr; exact le_max_right _ _
  · push Not at hfar
    obtain ⟨W', hW'C, hW'd⟩ := hCc.exists_infDist_eq_dist hCne W
    have hball : ball W (1 / 2) ⊆ K := by
      intro Y hY
      have hY' : ‖Y - W‖ < 1 / 2 := mem_ball_iff_norm.mp hY
      have h1 : ‖Y‖ ≤ ‖W‖ + ‖Y - W‖ := by
        calc ‖Y‖ = ‖W + (Y - W)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖W‖ ≤ ‖Y‖ + ‖Y - W‖ := by
        calc ‖W‖ = ‖Y - (Y - W)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      refine ⟨mem_closedBall_zero_iff.mpr (by linarith), fun hYb => ?_⟩
      have := mem_ball_zero_iff.mp hYb
      linarith
    have hW'b : W' ∈ ball W (1 / 2) := by
      rw [mem_ball, dist_comm, ← hW'd]; exact hfar
    have hW'0 : W' ≠ 0 := hK0 W' (hball hW'b)
    have hzero : dbarDir v Gd.glued W' = 0 := Gd.dbarDir_glued_eq_zero hC hW'C hW'0 v
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := dbarDir v Gd.glued)
      (s := ball W (1 / 2)) (C := max B₁ 0)
      (fun Y hY => (Gd.contDiffAt_dbarDir_glued v (hK0 Y (hball hY))).differentiableAt
        (by simp))
      (fun Y hY => (hB₁ Y (hball hY)).trans (le_max_left _ _)) (convex_ball W (1 / 2))
      hW'b (mem_ball_self (by norm_num))
    rw [hzero, sub_zero, ← dist_eq_norm, ← hW'd] at hmvt
    exact hmvt.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) infDist_nonneg)

/-- `|∂̄_v G(Z)| ≤ M |Z|^{k-2} dist(Z, C)` for `Z ≠ 0` (`k ≥ 2`). -/
theorem exists_dbarDir_le (hk : 2 ≤ k) (v : ComplexModel m) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Z : ComplexModel m, Z ≠ 0 →
      ‖dbarDir v Gd.glued Z‖ ≤ M * ‖Z‖ ^ (k - 2) * infDist Z C := by
  by_cases hCne : C.Nonempty
  · obtain ⟨M, hM0, hM⟩ := Gd.exists_dbarDir_le_on_sphere hCc hC hCne v
    refine ⟨M, hM0, fun Z hZ => ?_⟩
    have hn : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
    have hu0 : unitMap Z ≠ 0 := by
      intro h; have := norm_unitMap hZ; rw [h, norm_zero] at this; exact zero_ne_one this
    have hdist : infDist (unitMap Z) C = ‖Z‖⁻¹ * infDist Z C := by
      rw [unitMap, infDist_smul_cone hC (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hn).ne'),
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    conv_lhs => rw [eq_norm_smul_unitMap hZ, Gd.dbarDir_glued_smul (by omega) hn hu0]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖Z‖ ^ (k - 1) * ‖dbarDir v Gd.glued (unitMap Z)‖
        ≤ ‖Z‖ ^ (k - 1) * (M * infDist (unitMap Z) C) := by
          gcongr; exact hM _ (norm_unitMap hZ)
      _ = M * (‖Z‖ ^ (k - 1) * ‖Z‖⁻¹) * infDist Z C := by rw [hdist]; ring
      _ = M * ‖Z‖ ^ (k - 2) * infDist Z C := by
          congr 2
          have : k - 1 = (k - 2) + 1 := by omega
          rw [this, pow_succ, mul_assoc, mul_inv_cancel₀ hn.ne', mul_one]
  · -- empty cone: no centres, `G = 0`
    rw [Set.not_nonempty_iff_eq_empty] at hCne
    have hT : Gd.T = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have := Gd.T_sub p hp
      rw [hCne] at this
      exact this
    have hG : Gd.glued = fun _ => 0 := by
      funext Z; simp [glued, hT]
    refine ⟨0, le_rfl, fun Z hZ => ?_⟩
    rw [hG, dbarDir_const, norm_zero]
    simp

/-- **The `∂̄`-estimate**: `|∂̄G(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²` on `ℂ^m` (`k ≥ 2`). -/
theorem exists_dbarNormSq_ext0_le (hk : 2 ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Z : ComplexModel m,
      dbarNormSq Gd.ext0 Z ≤ M * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2 := by
  choose M hM0 hM using fun j : Fin m => Gd.exists_dbarDir_le hCc hC hk (coordVec j)
  refine ⟨∑ j, M j ^ 2, Finset.sum_nonneg fun j _ => sq_nonneg _, fun Z => ?_⟩
  by_cases hZ : Z = 0
  · subst hZ
    have h0 : ∀ j, dbarDir (coordVec j) Gd.ext0 0 = 0 := by
      intro j
      simp [dbarDir, Gd.fderiv_ext0_zero hk]
    have : dbarNormSq Gd.ext0 0 = 0 := by simp [dbarNormSq, h0]
    rw [this]
    positivity
  · have hdbar : ∀ j, dbarDir (coordVec j) Gd.ext0 Z = dbarDir (coordVec j) Gd.glued Z :=
      fun j => dbarDir_congr (Gd.ext0_eventuallyEq hZ)
    simp only [dbarNormSq, hdbar, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := hM j Z hZ
    have hnn : 0 ≤ M j * ‖Z‖ ^ (k - 2) * infDist Z C :=
      mul_nonneg (mul_nonneg (hM0 j) (pow_nonneg (norm_nonneg _) _)) infDist_nonneg
    calc ‖dbarDir (coordVec j) Gd.glued Z‖ ^ 2 ≤ (M j * ‖Z‖ ^ (k - 2) * infDist Z C) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = M j ^ 2 * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2 := by
          have : 2 * k - 4 = (k - 2) * 2 := by omega
          rw [this, pow_mul]; ring

end GluingData

/-- **Smooth homogeneous extension** (`claude-h0-gaga:smooth-extension`).  Let `C ⊆ ℂ^m` be a
closed cone and `F` homogeneous of degree `k ≥ 2` on `C` and locally holomorphic on `C ∖ {0}`.
Then there is `a : ℂ^m → ℂ` of class `C¹` with `a = F` on `C` and
`|∂̄a(Z)|² ≤ M |Z|^{2k-4} dist(Z, C)²`. -/
theorem exists_smoothExtension {C : Set (ComplexModel m)} (hCc : IsClosed C)
    (hC : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → c • Z ∈ C) {k : ℕ} (hk : 2 ≤ k)
    {F : ComplexModel m → ℂ} (hF : ∀ (c : ℂ) (Z : ComplexModel m), Z ∈ C → F (c • Z) = c ^ k * F Z)
    (hloc : IsLocallyHolomorphicOn C F) :
    ∃ a : ComplexModel m → ℂ, ContDiff ℝ 1 a ∧ (∀ Z ∈ C, a Z = F Z) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ Z : ComplexModel m,
        dbarNormSq a Z ≤ M * ‖Z‖ ^ (2 * k - 4) * infDist Z C ^ 2 := by
  obtain ⟨Gd⟩ := GluingData.nonempty hCc hC hF hloc
  exact ⟨Gd.ext0, Gd.contDiff_ext0 hk, fun Z hZ => Gd.ext0_eq (by omega) hC hF hZ,
    Gd.exists_dbarNormSq_ext0_le hCc hC hk⟩

end SGPT.GAGA.H0
