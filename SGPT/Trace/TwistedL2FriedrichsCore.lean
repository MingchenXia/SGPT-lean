import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import SGPT.Foundations.Analysis.Pending.MollifierL2
import SGPT.Foundations.Analysis.Pending.HormanderDensity

/-!
# Friedrichs' lemma: the scalar commutator estimate

Blueprint `claude-twisted-l2-a.tex` (lane TL2-A; node `claude-twisted-l2:friedrichs` of
`claude-twisted-l2.tex`).  On a finite-dimensional real normed space `E` with an additive Haar
measure `μ`, let `ρ_r` be the normalized standard bump of radius `r` (`stdBump r`), `a` a `C¹`
complex function with compact support and `v ∈ E`.  The **Friedrichs commutator**

`C_r u (z) = a(z) ∂_v (ρ_r ⋆ u)(z) + ∫ u(y) ∂_v[y ↦ a(y) ρ_r(z - y)](y) dy`

is the difference between `a ∂_v` applied to the mollification `ρ_r ⋆ u` and the mollification
of the (distributional) `a ∂_v u`: the displayed integral is the negative of the latter,
written through the transpose. The main result
`tendsto_eLpNorm_friedrichsComm` is Friedrichs' lemma (Hörmander, *An introduction to complex
analysis in several variables*, Lemma 4.1.3 and its proof):

`‖C_r u‖_{L²} → 0` as `r → 0` for every `u ∈ L²(μ)`.

The proof is the classical one:
* `C_r` is an integral operator with kernel `(a(z) - a(y)) ∂_vρ_r(z - y) + ∂_v a(y) ρ_r(z - y)`
  (`friedrichsComm_eq_integral`), bounded by `L |x| |∂_vρ_r(x)| + M ρ_r(x)` at `x = z - y`;
* the `L¹` norm of `|x| |∂_vρ_r(x)|` does not depend on `r` (`integral_norm_mul_abs_fderiv_stdBump`,
  a scaling argument), so `C_r` is bounded on `L²` uniformly in `r` (Young's inequality
  `eLpNorm_le_of_kernel`);
* for smooth compactly supported `u`, integration by parts gives
  `C_r u = a (ρ_r ⋆ ∂_v u) - ρ_r ⋆ (a ∂_v u) → 0` (`tendsto_eLpNorm_friedrichsComm_of_contDiff`);
* density of smooth compactly supported functions in `L²`.

The zeroth order commutator `zeroComm` (`b (ρ_r ⋆ u) - ρ_r ⋆ (b u)`) is also treated.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology ENNReal Pointwise
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander.Density

namespace SGPT.Trace.TwistedL2.Friedrichs

/-! ### Cauchy--Schwarz and Young's inequality for `L¹` kernels -/

/-- Cauchy--Schwarz with a weight: `(∫ w a)² ≤ (∫ w) (∫ w a²)`. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {w a : α → ℝ≥0∞}
    (hw : Measurable w) (ha : Measurable a) :
    (∫⁻ t, w t * a t ∂ν) ^ 2 ≤ (∫⁻ t, w t ∂ν) * ∫⁻ t, w t * a t ^ 2 ∂ν := by
  set ν' := ν.withDensity w
  have h1 : ∫⁻ t, w t * a t ∂ν = ∫⁻ t, a t ∂ν' :=
    (lintegral_withDensity_eq_lintegral_mul ν hw ha).symm
  have h2 : ∫⁻ t, w t * a t ^ 2 ∂ν = ∫⁻ t, a t ^ 2 ∂ν' :=
    (lintegral_withDensity_eq_lintegral_mul ν hw (ha.pow_const 2)).symm
  have h3 : ν' univ = ∫⁻ t, w t ∂ν := by
    simp [ν', withDensity_apply _ MeasurableSet.univ]
  rw [h1, h2, ← h3]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq ν' Real.HolderConjugate.two_two ha.aemeasurable
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, ENNReal.rpow_two, one_pow,
    one_mul] at hCS
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ t, a t ∂ν') ^ 2
      ≤ ((∫⁻ t, a t ^ 2 ∂ν') ^ (1 / 2 : ℝ) * ν' univ ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ν' univ * ∫⁻ t, a t ^ 2 ∂ν' := by rw [mul_pow, hsq, hsq, mul_comm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Young's inequality** `‖k ⋆ a‖₂ ≤ ‖k‖₁ ‖a‖₂`, for `ℝ≥0∞`-valued functions. -/
theorem lintegral_kernel_sq_le {k a : E → ℝ≥0∞} (hk : Measurable k) (ha : Measurable a) :
    ∫⁻ z, (∫⁻ y, k (z - y) * a y ∂μ) ^ 2 ∂μ ≤ (∫⁻ x, k x ∂μ) ^ 2 * ∫⁻ y, a y ^ 2 ∂μ := by
  set c := ∫⁻ x, k x ∂μ
  have hkz : ∀ z, ∫⁻ y, k (z - y) ∂μ = c := fun z ↦ lintegral_sub_left_eq_self k z
  have hm : Measurable fun p : E × E ↦ k (p.1 - p.2) * a p.2 ^ 2 :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((ha.comp measurable_snd).pow_const 2)
  calc ∫⁻ z, (∫⁻ y, k (z - y) * a y ∂μ) ^ 2 ∂μ
      ≤ ∫⁻ z, c * ∫⁻ y, k (z - y) * a y ^ 2 ∂μ ∂μ := by
        refine lintegral_mono fun z ↦ ?_
        have := lintegral_mul_sq_le (ν := μ) (w := fun y ↦ k (z - y))
          (hk.comp (measurable_const.sub measurable_id)) ha
        rwa [hkz z] at this
    _ = c * ∫⁻ z, ∫⁻ y, k (z - y) * a y ^ 2 ∂μ ∂μ :=
        lintegral_const_mul _ hm.lintegral_prod_right'
    _ = c * ∫⁻ y, ∫⁻ z, k (z - y) * a y ^ 2 ∂μ ∂μ := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = c * ∫⁻ y, c * a y ^ 2 ∂μ := by
        congr 1
        refine lintegral_congr fun y ↦ ?_
        rw [lintegral_mul_const _ (show Measurable fun z : E ↦ k (z - y) from
          hk.comp (measurable_id.sub measurable_const)), lintegral_sub_right_eq_self k y]
    _ = c ^ 2 * ∫⁻ y, a y ^ 2 ∂μ := by
        rw [lintegral_const_mul _ (ha.pow_const 2), ← mul_assoc, sq]

/-- **Young's inequality for an `L¹` kernel bound.**  If `‖T z‖ ≤ ∫ k(z - y) ‖u(y)‖ dy`, then
`‖T‖₂ ≤ ‖k‖₁ ‖u‖₂`. -/
theorem eLpNorm_le_of_kernel {k : E → ℝ≥0∞} (hk : Measurable k) {T u : E → ℂ}
    (hu : AEStronglyMeasurable u μ) (hT : ∀ z, ‖T z‖ₑ ≤ ∫⁻ y, k (z - y) * ‖u y‖ₑ ∂μ) :
    eLpNorm T 2 μ ≤ (∫⁻ x, k x ∂μ) * eLpNorm u 2 μ := by
  set a : E → ℝ≥0∞ := fun y ↦ ‖hu.mk u y‖ₑ
  have ha : Measurable a := hu.stronglyMeasurable_mk.measurable.enorm
  have hT' : ∀ z, ‖T z‖ₑ ≤ ∫⁻ y, k (z - y) * a y ∂μ := fun z ↦ (hT z).trans_eq
    (lintegral_congr_ae (hu.ae_eq_mk.mono fun y hy ↦ by simp only [a, hy]))
  rw [eLpNorm_congr_ae hu.ae_eq_mk,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hsq : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x ↦ by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc (∫⁻ z, ‖T z‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ x, k x ∂μ) ^ 2 * ∫⁻ y, a y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        gcongr
        exact (lintegral_mono fun z ↦ by gcongr; exact hT' z).trans (lintegral_kernel_sq_le hk ha)
    _ = (∫⁻ x, k x ∂μ) * (∫⁻ y, ‖hu.mk u y‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsq]

/-! ### The standard bumps and their scaling -/

/-- The standard bump of radius `r`: `rIn = r/2`, `rOut = r`. -/
def stdBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : E) :=
  ⟨r / 2, r, by positivity, by linarith⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem stdBump_rOut (r : ℝ) (hr : 0 < r) :
    (stdBump r hr : ContDiffBump (0 : E)).rOut = r :=
  rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem stdBump_apply (r : ℝ) (hr : 0 < r) (x : E) :
    (stdBump r hr : ContDiffBump (0 : E)) x =
      (stdBump 1 one_pos : ContDiffBump (0 : E)) (r⁻¹ • x) := by
  simp only [ContDiffBump.apply, stdBump, sub_zero, smul_smul]
  have e1 : r / (r / 2) = 1 / (1 / 2) := by field_simp
  have e2 : (r / 2)⁻¹ = (1 / 2)⁻¹ * r⁻¹ := by ring
  rw [e1, e2]

theorem integral_stdBump (r : ℝ) (hr : 0 < r) :
    ∫ x, (stdBump r hr : ContDiffBump (0 : E)) x ∂μ =
      r ^ Module.finrank ℝ E * ∫ x, (stdBump 1 one_pos : ContDiffBump (0 : E)) x ∂μ := by
  simp_rw [stdBump_apply r hr]
  rw [Measure.integral_comp_inv_smul_of_nonneg μ _ hr.le, smul_eq_mul]

/-- `ρ_r(x) = r^{-d} ρ_1(x/r)`. -/
theorem stdBump_normed (r : ℝ) (hr : 0 < r) (x : E) :
    (stdBump r hr).normed μ x =
      (r ^ Module.finrank ℝ E)⁻¹ * (stdBump 1 one_pos).normed μ (r⁻¹ • x) := by
  have h1 : 0 < ∫ x, (stdBump 1 one_pos : ContDiffBump (0 : E)) x ∂μ :=
    (stdBump 1 one_pos).integral_pos
  have h2 : 0 < r ^ Module.finrank ℝ E := pow_pos hr _
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, integral_stdBump r hr, stdBump_apply r hr]
  field_simp

/-- `∂_vρ_r(x) = r^{-d-1} (∂_vρ_1)(x/r)`. -/
theorem fderiv_stdBump_normed_apply (r : ℝ) (hr : 0 < r) (x v : E) :
    fderiv ℝ ((stdBump r hr).normed μ) x v =
      (r ^ Module.finrank ℝ E)⁻¹ * r⁻¹ *
        fderiv ℝ ((stdBump 1 one_pos).normed μ) (r⁻¹ • x) v := by
  set Φ := (stdBump (E := E) 1 one_pos).normed μ
  have hfun : (stdBump r hr).normed μ = fun x ↦ (r ^ Module.finrank ℝ E)⁻¹ * Φ (r⁻¹ • x) :=
    funext (stdBump_normed r hr)
  have hΦ : DifferentiableAt ℝ Φ (r⁻¹ • x) :=
    ((stdBump (E := E) 1 one_pos).contDiff_normed (n := 1)).differentiable one_ne_zero _
  have hin : HasFDerivAt (fun x : E ↦ r⁻¹ • x) (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have h : HasFDerivAt (fun x : E ↦ (r ^ Module.finrank ℝ E)⁻¹ * Φ (r⁻¹ • x))
      ((r ^ Module.finrank ℝ E)⁻¹ • (fderiv ℝ Φ (r⁻¹ • x)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ E)) x :=
    (hΦ.hasFDerivAt.comp x hin).const_mul (r ^ Module.finrank ℝ E)⁻¹
  rw [hfun, h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

/-- The first moment of `|∂_vρ_r|` does not depend on `r`. -/
theorem integral_norm_mul_abs_fderiv_stdBump (r : ℝ) (hr : 0 < r) (v : E) :
    ∫ x, ‖x‖ * |fderiv ℝ ((stdBump r hr).normed μ) x v| ∂μ =
      ∫ x, ‖x‖ * |fderiv ℝ ((stdBump 1 one_pos).normed μ) x v| ∂μ := by
  set Φ := (stdBump (E := E) 1 one_pos).normed μ
  have h2 : 0 < r ^ Module.finrank ℝ E := pow_pos hr _
  have hpt : ∀ x : E, ‖x‖ * |fderiv ℝ ((stdBump r hr).normed μ) x v| =
      (r ^ Module.finrank ℝ E)⁻¹ * (‖r⁻¹ • x‖ * |fderiv ℝ Φ (r⁻¹ • x) v|) := by
    intro x
    rw [fderiv_stdBump_normed_apply r hr, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_inv, abs_inv, abs_of_pos h2, abs_of_pos hr]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg μ
    (fun x ↦ ‖x‖ * |fderiv ℝ Φ x v|) hr.le, smul_eq_mul]
  field_simp

/-! ### Translated bumps -/

section Bump

variable (ρ : ContDiffBump (0 : E))

theorem normed_sub_eq_zero {z y : E} (h : ρ.rOut ≤ dist y z) : ρ.normed μ (z - y) = 0 := by
  have : z - y ∉ support (ρ.normed μ) := by
    rw [ρ.support_normed_eq, mem_ball_zero_iff, ← dist_eq_norm, dist_comm]
    exact not_lt.2 h
  exact notMem_support.1 this

theorem fderiv_normed_sub_eq_zero {z y : E} (h : ρ.rOut < dist y z) :
    fderiv ℝ (ρ.normed μ) (z - y) = 0 := by
  refine fderiv_of_notMem_tsupport ℝ ?_
  rw [ρ.tsupport_normed_eq, mem_closedBall_zero_iff, ← dist_eq_norm, dist_comm]
  exact not_le.2 h

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem contDiff_normed_sub {k : ℕ∞} (z : E) :
    ContDiff ℝ k fun y ↦ (ρ.normed μ (z - y) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (ρ.contDiff_normed.comp (contDiff_const.sub contDiff_id))

theorem hasCompactSupport_normed_sub (z : E) :
    HasCompactSupport fun y ↦ (ρ.normed μ (z - y) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall z ρ.rOut) fun y hy ↦ by
    have h : ρ.rOut < dist y z := not_le.1 (by simpa [mem_closedBall] using hy)
    simp [normed_sub_eq_zero (μ := μ) ρ h.le]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem continuous_fderiv_normed_apply (v : E) :
    Continuous fun x ↦ fderiv ℝ (ρ.normed μ) x v :=
  ((ρ.contDiff_normed (n := 1)).continuous_fderiv one_ne_zero).clm_apply continuous_const

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem hasFDerivAt_normed_sub (z y : E) :
    HasFDerivAt (fun y ↦ (ρ.normed μ (z - y) : ℂ))
      (-(Complex.ofRealCLM.comp (fderiv ℝ (ρ.normed μ) (z - y)))) y := by
  have h1 : HasFDerivAt (fun y : E ↦ z - y) (-ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).const_sub z
  have h2 := ((ρ.contDiff_normed (μ := μ) (n := 1)).differentiable one_ne_zero (z - y)).hasFDerivAt
  have h3 : HasFDerivAt (fun y ↦ (ρ.normed μ (z - y) : ℂ)) (Complex.ofRealCLM.comp
      ((fderiv ℝ (ρ.normed μ) (z - y)).comp (-ContinuousLinearMap.id ℝ E))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (h2.comp y h1)
  exact h3.congr_fderiv (by ext w; simp)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem fderiv_normed_sub_apply (z y v : E) :
    fderiv ℝ (fun y ↦ (ρ.normed μ (z - y) : ℂ)) y v = -(fderiv ℝ (ρ.normed μ) (z - y) v : ℂ) := by
  rw [(hasFDerivAt_normed_sub ρ z y).fderiv]
  simp

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem fderiv_mul_normed_sub_apply {a : E → ℂ} (ha : Differentiable ℝ a) (z y v : E) :
    fderiv ℝ (fun y ↦ a y * (ρ.normed μ (z - y) : ℂ)) y v =
      fderiv ℝ a y v * (ρ.normed μ (z - y) : ℂ) -
        a y * (fderiv ℝ (ρ.normed μ) (z - y) v : ℂ) := by
  have h : HasFDerivAt (fun y ↦ a y * (ρ.normed μ (z - y) : ℂ)) _ y :=
    (ha y).hasFDerivAt.mul (hasFDerivAt_normed_sub ρ z y)
  rw [h.fderiv]
  simp
  ring

end Bump

/-! ### Integrability against locally integrable functions -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem continuous_fderiv_apply {G : E → ℂ} (hG : ContDiff ℝ 1 G) (v : E) :
    Continuous fun y ↦ fderiv ℝ G y v :=
  (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
theorem integrable_mul_of_hasCompactSupport {g u : E → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hu : LocallyIntegrable u μ) :
    Integrable (fun y ↦ g y * u y) μ :=
  hu.integrable_smul_left_of_hasCompactSupport hg hgc

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
theorem integrable_mul_fderiv_of_hasCompactSupport {G u : E → ℂ} (hG : ContDiff ℝ 1 G)
    (hGc : HasCompactSupport G) (hu : LocallyIntegrable u μ) (v : E) :
    Integrable (fun y ↦ u y * fderiv ℝ G y v) μ :=
  hu.integrable_smul_right_of_hasCompactSupport (continuous_fderiv_apply hG v)
    (hGc.fderiv_apply ℝ v)

theorem integrable_mul_fderiv_mul_normed_sub (ρ : ContDiffBump (0 : E)) {a u : E → ℂ}
    (ha : ContDiff ℝ 1 a) (hu : LocallyIntegrable u μ) (z v : E) :
    Integrable (fun y ↦ u y * fderiv ℝ (fun y ↦ a y * (ρ.normed μ (z - y) : ℂ)) y v) μ :=
  integrable_mul_fderiv_of_hasCompactSupport (ha.mul (contDiff_normed_sub ρ z))
    (hasCompactSupport_normed_sub ρ z).mul_left hu v

/-- Integration by parts `∫ u ∂_v g = -∫ ∂_v u g` for `C¹` functions, `u` compactly supported. -/
theorem integral_mul_fderiv_eq_neg {u g : E → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (hg : ContDiff ℝ 1 g) (v : E) :
    ∫ y, u y * fderiv ℝ g y v ∂μ = -∫ y, fderiv ℝ u y v * g y ∂μ := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ ↦ hu.differentiable one_ne_zero x) (fun x _ ↦ hg.differentiable one_ne_zero x)
  · exact ((continuous_fderiv_apply hu v).mul hg.continuous).integrable_of_hasCompactSupport
      (huc.fderiv_apply ℝ v).mul_right
  · exact (hu.continuous.mul (continuous_fderiv_apply hg v)).integrable_of_hasCompactSupport
      huc.mul_right
  · exact (hu.continuous.mul hg.continuous).integrable_of_hasCompactSupport huc.mul_right

/-! ### The Friedrichs commutator -/

/-- The **Friedrichs commutator** of the first order operator `a ∂_v` with the mollifier `ρ`:
`a(z) ∂_v(ρ ⋆ u)(z) + ∫ u(y) ∂_v[a(·) ρ(z - ·)](y) dy`. The second term is minus the mollification
of the distribution `a ∂_v u` (its transpose applied to the test function `ρ(z - ·)`). -/
def friedrichsComm (μ : Measure E) (ρ : ContDiffBump (0 : E)) (a : E → ℂ) (v : E) (u : E → ℂ)
    (z : E) : ℂ :=
  a z * fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] u) z v +
    ∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed μ (z - y) : ℂ)) y v ∂μ

/-- The kernel `(a(z) - a(y)) ∂_vρ(z - y) + ∂_v a(y) ρ(z - y)` of the Friedrichs commutator. -/
def friedrichsKernel (μ : Measure E) (ρ : ContDiffBump (0 : E)) (a : E → ℂ) (v z y : E) : ℂ :=
  (a z - a y) * (fderiv ℝ (ρ.normed μ) (z - y) v : ℂ) +
    fderiv ℝ a y v * (ρ.normed μ (z - y) : ℂ)

section Comm

variable (ρ : ContDiffBump (0 : E)) {a : E → ℂ} (v : E)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem continuous_friedrichsKernel (ha : ContDiff ℝ 1 a) :
    Continuous fun p : E × E ↦ friedrichsKernel μ ρ a v p.1 p.2 := by
  have hda : Continuous fun y ↦ fderiv ℝ a y v := continuous_fderiv_apply ha v
  have hdρ := continuous_fderiv_normed_apply (μ := μ) ρ v
  have hsub : Continuous fun p : E × E ↦ p.1 - p.2 := continuous_fst.sub continuous_snd
  exact (((ha.continuous.comp continuous_fst).sub (ha.continuous.comp continuous_snd)).mul
    (Complex.continuous_ofReal.comp (hdρ.comp hsub))).add ((hda.comp continuous_snd).mul
      (Complex.continuous_ofReal.comp (ρ.continuous_normed.comp hsub)))

theorem hasCompactSupport_friedrichsKernel (z : E) :
    HasCompactSupport fun y ↦ friedrichsKernel μ ρ a v z y :=
  HasCompactSupport.intro (isCompact_closedBall z ρ.rOut) fun y hy ↦ by
    have h : ρ.rOut < dist y z := not_le.1 (by simpa [mem_closedBall] using hy)
    simp [friedrichsKernel, normed_sub_eq_zero (μ := μ) ρ h.le,
      fderiv_normed_sub_eq_zero (μ := μ) ρ h]

theorem integrable_friedrichsKernel_mul (ha : ContDiff ℝ 1 a) {u : E → ℂ}
    (hu : LocallyIntegrable u μ) (z : E) :
    Integrable (fun y ↦ friedrichsKernel μ ρ a v z y * u y) μ :=
  integrable_mul_of_hasCompactSupport
    ((continuous_friedrichsKernel ρ v ha).comp (Continuous.prodMk_right z))
    (hasCompactSupport_friedrichsKernel ρ v z) hu

/-- The Friedrichs commutator is an integral operator. -/
theorem friedrichsComm_eq_integral (ha : ContDiff ℝ 1 a) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (z : E) :
    friedrichsComm μ ρ a v u z = ∫ y, friedrichsKernel μ ρ a v z y * u y ∂μ := by
  have hda := ha.differentiable one_ne_zero
  have hint1 : Integrable (fun y ↦ (fderiv ℝ (ρ.normed μ) (z - y) v : ℂ) * u y) μ := by
    refine integrable_mul_of_hasCompactSupport (Complex.continuous_ofReal.comp
      ((continuous_fderiv_normed_apply ρ v).comp (continuous_const.sub continuous_id)))
      (HasCompactSupport.intro (isCompact_closedBall z ρ.rOut) fun y hy ↦ ?_) hu
    have h : ρ.rOut < dist y z := not_le.1 (by simpa [mem_closedBall] using hy)
    simp [fderiv_normed_sub_eq_zero (μ := μ) ρ h]
  rw [friedrichsComm, fderiv_bump_convolution_apply ρ hu, ← integral_const_mul,
    ← integral_add (hint1.const_mul _) (integrable_mul_fderiv_mul_normed_sub ρ ha hu z v)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [fderiv_mul_normed_sub_apply ρ hda, friedrichsKernel]
  ring

theorem aestronglyMeasurable_friedrichsComm (ha : ContDiff ℝ 1 a) {u : E → ℂ}
    (hu : LocallyIntegrable u μ) : AEStronglyMeasurable (friedrichsComm μ ρ a v u) μ := by
  have : friedrichsComm μ ρ a v u = fun z ↦ ∫ y, friedrichsKernel μ ρ a v z y * u y ∂μ :=
    funext (friedrichsComm_eq_integral ρ v ha hu)
  rw [this]
  exact AEStronglyMeasurable.integral_prod_right'
    (f := fun p : E × E ↦ friedrichsKernel μ ρ a v p.1 p.2 * u p.2)
    ((continuous_friedrichsKernel ρ v ha).aestronglyMeasurable.mul
      hu.aestronglyMeasurable.comp_snd)

theorem friedrichsComm_sub (ha : ContDiff ℝ 1 a) {u₁ u₂ : E → ℂ} (hu₁ : LocallyIntegrable u₁ μ)
    (hu₂ : LocallyIntegrable u₂ μ) (z : E) :
    friedrichsComm μ ρ a v (u₁ - u₂) z =
      friedrichsComm μ ρ a v u₁ z - friedrichsComm μ ρ a v u₂ z := by
  rw [friedrichsComm_eq_integral ρ v ha (hu₁.sub hu₂), friedrichsComm_eq_integral ρ v ha hu₁,
    friedrichsComm_eq_integral ρ v ha hu₂, ← integral_sub
      (integrable_friedrichsKernel_mul ρ v ha hu₁ z) (integrable_friedrichsKernel_mul ρ v ha hu₂ z)]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp [mul_sub]

/-- The pointwise bound `L |x| |∂_vρ(x)| + M ρ(x)` of the kernel at `x = z - y`. -/
def friedrichsBound (μ : Measure E) (ρ : ContDiffBump (0 : E)) (v : E) (L M : ℝ) (x : E) : ℝ :=
  L * (‖x‖ * |fderiv ℝ (ρ.normed μ) x v|) + M * ρ.normed μ x

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem norm_friedrichsKernel_le {L M : ℝ} (hL : ∀ z y, ‖a z - a y‖ ≤ L * ‖z - y‖)
    (hM : ∀ y, ‖fderiv ℝ a y v‖ ≤ M) (z y : E) :
    ‖friedrichsKernel μ ρ a v z y‖ ≤ friedrichsBound μ ρ v L M (z - y) := by
  unfold friedrichsKernel friedrichsBound
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hL z y) (abs_nonneg _)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ρ.nonneg_normed _)]
    exact mul_le_mul_of_nonneg_right (hM y) (ρ.nonneg_normed _)

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem continuous_friedrichsBound (L M : ℝ) : Continuous (friedrichsBound μ ρ v L M) :=
  (continuous_const.mul (continuous_norm.mul (continuous_fderiv_normed_apply ρ v).abs)).add
    (continuous_const.mul ρ.continuous_normed)

theorem hasCompactSupport_moment :
    HasCompactSupport fun x ↦ ‖x‖ * |fderiv ℝ (ρ.normed μ) x v| :=
  HasCompactSupport.mul_left (f := fun x : E ↦ ‖x‖)
    ((ρ.hasCompactSupport_normed.fderiv_apply ℝ v).comp_left (g := fun t : ℝ ↦ |t|) abs_zero)

theorem integrable_moment : Integrable (fun x ↦ ‖x‖ * |fderiv ℝ (ρ.normed μ) x v|) μ :=
  (continuous_norm.mul (continuous_fderiv_normed_apply ρ v).abs).integrable_of_hasCompactSupport
    (hasCompactSupport_moment ρ v)

theorem enorm_friedrichsComm_le (ha : ContDiff ℝ 1 a) {L M : ℝ}
    (hL : ∀ z y, ‖a z - a y‖ ≤ L * ‖z - y‖) (hM : ∀ y, ‖fderiv ℝ a y v‖ ≤ M) {u : E → ℂ}
    (hu : LocallyIntegrable u μ) (z : E) :
    ‖friedrichsComm μ ρ a v u z‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (friedrichsBound μ ρ v L M (z - y)) * ‖u y‖ₑ ∂μ := by
  rw [friedrichsComm_eq_integral ρ v ha hu]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ ?_)
  rw [enorm_mul, ← ofReal_norm]
  gcongr
  exact norm_friedrichsKernel_le ρ v hL hM z y

/-- The Friedrichs commutator is bounded on `L²`. -/
theorem eLpNorm_friedrichsComm_le (ha : ContDiff ℝ 1 a) {L M : ℝ}
    (hL : ∀ z y, ‖a z - a y‖ ≤ L * ‖z - y‖) (hM : ∀ y, ‖fderiv ℝ a y v‖ ≤ M) (hL0 : 0 ≤ L)
    (hM0 : 0 ≤ M) {u : E → ℂ} (hu : MemLp u 2 μ) :
    eLpNorm (friedrichsComm μ ρ a v u) 2 μ ≤
      ENNReal.ofReal (L * ∫ x, ‖x‖ * |fderiv ℝ (ρ.normed μ) x v| ∂μ + M) * eLpNorm u 2 μ := by
  have hk : Measurable fun x ↦ ENNReal.ofReal (friedrichsBound μ ρ v L M x) :=
    ENNReal.measurable_ofReal.comp (continuous_friedrichsBound ρ v L M).measurable
  refine (eLpNorm_le_of_kernel hk hu.1
    (enorm_friedrichsComm_le ρ v ha hL hM (hu.locallyIntegrable one_le_two))).trans_eq ?_
  congr 1
  have hint : Integrable (friedrichsBound μ ρ v L M) μ :=
    ((integrable_moment ρ v).const_mul L).add (ρ.integrable_normed.const_mul M)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ ?_)]
  · congr 1
    rw [show friedrichsBound μ ρ v L M = fun x ↦
        L * (‖x‖ * |fderiv ℝ (ρ.normed μ) x v|) + M * ρ.normed μ x from rfl,
      integral_add ((integrable_moment ρ v).const_mul L) (ρ.integrable_normed.const_mul M),
      integral_const_mul, integral_const_mul, ρ.integral_normed, mul_one]
  · exact add_nonneg (mul_nonneg hL0 (by positivity)) (mul_nonneg hM0 (ρ.nonneg_normed x))

end Comm

/-! ### Smooth compactly supported functions -/

section Smooth

variable (ρ : ContDiffBump (0 : E)) {a : E → ℂ} (v : E)

/-- For a `C¹` compactly supported `u`, integration by parts identifies the Friedrichs commutator
with `a (ρ ⋆ ∂_v u) - ρ ⋆ (a ∂_v u)`. -/
theorem friedrichsComm_eq_of_contDiff (ha : ContDiff ℝ 1 a) {u : E → ℂ} (hu : ContDiff ℝ 1 u)
    (huc : HasCompactSupport u) (z : E) :
    friedrichsComm μ ρ a v u z =
      a z * (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ u y v) z -
        (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y * fderiv ℝ u y v) z := by
  have hul : LocallyIntegrable u μ := hu.continuous.locallyIntegrable
  have hρz : ContDiff ℝ 1 fun y ↦ (ρ.normed μ (z - y) : ℂ) := contDiff_normed_sub ρ z
  have h1 : fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] u) z v =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ u y v) z := by
    rw [fderiv_bump_convolution_apply ρ hul, bump_convolution_apply_eq_integral]
    calc ∫ y, (fderiv ℝ (ρ.normed μ) (z - y) v : ℂ) * u y ∂μ
        = -∫ y, u y * fderiv ℝ (fun y ↦ (ρ.normed μ (z - y) : ℂ)) y v ∂μ := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          simp only [fderiv_normed_sub_apply]
          ring
      _ = ∫ y, (ρ.normed μ (z - y) : ℂ) * fderiv ℝ u y v ∂μ := by
          rw [integral_mul_fderiv_eq_neg hu huc hρz v, neg_neg]
          refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
          ring
  have h2 : ∫ y, u y * fderiv ℝ (fun y ↦ a y * (ρ.normed μ (z - y) : ℂ)) y v ∂μ =
      -(ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y * fderiv ℝ u y v) z := by
    rw [integral_mul_fderiv_eq_neg hu huc (ha.mul hρz) v, bump_convolution_apply_eq_integral]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    ring
  rw [friedrichsComm, h1, h2, sub_eq_add_neg]

/-- Friedrichs' lemma for `C¹` compactly supported functions. -/
theorem tendsto_eLpNorm_friedrichsComm_of_contDiff (ha : ContDiff ℝ 1 a) {Ca : ℝ}
    (hCa : ∀ z, ‖a z‖ ≤ Ca) {u : E → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    {φ : ℕ → ContDiffBump (0 : E)} (hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (friedrichsComm μ (φ k) a v u) 2 μ) atTop (𝓝 0) := by
  set g : E → ℂ := fun y ↦ fderiv ℝ u y v
  have hg : Continuous g := continuous_fderiv_apply hu v
  have hgc : HasCompactSupport g := huc.fderiv_apply ℝ v
  have hag : Continuous fun y ↦ a y * g y := ha.continuous.mul hg
  have hagc : HasCompactSupport fun y ↦ a y * g y := hgc.mul_left
  have hgl : LocallyIntegrable g μ := hg.locallyIntegrable
  have hagl : LocallyIntegrable (fun y ↦ a y * g y) μ := hag.locallyIntegrable
  have hfun : ∀ k, friedrichsComm μ (φ k) a v u = fun z ↦
      a z * ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) z - a z * g z -
        (((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y * g y) z - a z * g z) := by
    intro k
    funext z
    rw [friedrichsComm_eq_of_contDiff (φ k) v ha hu huc z]
    ring
  simp_rw [hfun]
  refine tendsto_eLpNorm_sub
    (f := fun k z ↦ a z * ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) z - a z * g z)
    (g := fun k z ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ a y * g y) z - a z * g z)
    (fun k ↦ ((ha.continuous.mul (contDiff_bump_convolution (φ k) hgl).continuous).sub
      hag).aestronglyMeasurable)
    (fun k ↦ ((contDiff_bump_convolution (φ k) hagl).continuous.sub hag).aestronglyMeasurable)
    ?_ (tendsto_eLpNorm_bump_convolution_sub (hag.memLp_of_hasCompactSupport hagc) hφ)
  have h0 := tendsto_eLpNorm_bump_convolution_sub (μ := μ) (hg.memLp_of_hasCompactSupport hgc) hφ
  have h1 : Tendsto (fun k ↦ ENNReal.ofReal Ca *
      eLpNorm (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] g) x - g x) 2 μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ zero_le)
    fun k ↦ eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x ↦ ?_) 2
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right (hCa x) (norm_nonneg _)

end Smooth

/-! ### Friedrichs' lemma -/

/-- **Friedrichs' lemma** (Hörmander, *An introduction to complex analysis in several variables*,
Lemma 4.1.3).  For a `C¹` function `a` with compact support, a direction `v` and `u ∈ L²`, the
commutator of `a ∂_v` with the standard mollifiers `ρ_{r_k}`, `r_k → 0`, tends to `0` in `L²`. -/
theorem tendsto_eLpNorm_friedrichsComm {a : E → ℂ} (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (v : E) {u : E → ℂ} (hu : MemLp u 2 μ) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (friedrichsComm μ (stdBump (r k) (hr k)) a v u) 2 μ)
      atTop (𝓝 0) := by
  obtain ⟨Ca, hCa⟩ := ha.continuous.bounded_above_of_compact_support hac
  obtain ⟨Da, hDa⟩ := (ha.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hac.fderiv ℝ)
  set L := max Da 0
  set M := L * ‖v‖
  have hL0 : 0 ≤ L := le_max_right _ _
  have hM0 : 0 ≤ M := mul_nonneg hL0 (norm_nonneg _)
  have hL : ∀ z y, ‖a z - a y‖ ≤ L * ‖z - y‖ := fun z y ↦
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ ha.differentiable one_ne_zero x)
      (fun x _ ↦ (hDa x).trans (le_max_left _ _)) (mem_univ y) (mem_univ z)
  have hM : ∀ y, ‖fderiv ℝ a y v‖ ≤ M := fun y ↦
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ((hDa y).trans (le_max_left _ _))
      (norm_nonneg _))
  set I := ∫ x, ‖x‖ * |fderiv ℝ ((stdBump 1 one_pos : ContDiffBump (0 : E)).normed μ) x v| ∂μ
  have hI : 0 ≤ I := integral_nonneg fun x ↦ by positivity
  set C := L * I + M
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hL0 hI) hM0
  have hbound : ∀ k (w : E → ℂ), MemLp w 2 μ →
      eLpNorm (friedrichsComm μ (stdBump (r k) (hr k)) a v w) 2 μ ≤
        ENNReal.ofReal C * eLpNorm w 2 μ := by
    intro k w hw
    have := eLpNorm_friedrichsComm_le (stdBump (r k) (hr k)) v ha hL hM hL0 hM0 hw
    rwa [integral_norm_mul_abs_fderiv_stdBump] at this
  have hφ : Tendsto (fun k ↦ (stdBump (r k) (hr k) : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) := by
    simpa using hr0
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨e, -, he0, heε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have he : 0 < e := ENNReal.ofReal_pos.1 he0
  set δ := e / (2 * (C + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨g, hgc, hgs, hug⟩ := hu.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two hδ
  have hg1 : ContDiff ℝ 1 g := hgs.of_le (by norm_cast)
  have hg2 : MemLp g 2 μ := hgs.continuous.memLp_of_hasCompactSupport hgc
  have hlim := tendsto_eLpNorm_friedrichsComm_of_contDiff (μ := μ) v ha hCa hg1 hgc hφ
  have he2 : (0 : ℝ≥0∞) < ENNReal.ofReal (e / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim _ he2] with k hk
  set ρ : ContDiffBump (0 : E) := stdBump (r k) (hr k)
  have hul := hu.locallyIntegrable one_le_two
  have hgl := hg2.locallyIntegrable one_le_two
  have hsplit : friedrichsComm μ ρ a v u =
      fun z ↦ friedrichsComm μ ρ a v (u - g) z + friedrichsComm μ ρ a v g z := by
    funext z
    rw [friedrichsComm_sub ρ v ha hul hgl]
    ring
  have hCδ : C * δ ≤ e / 2 := by
    have : C * δ = e / 2 * (C / (C + 1)) := by
      simp only [δ]; field_simp
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  rw [hsplit]
  calc eLpNorm (fun z ↦ friedrichsComm μ ρ a v (u - g) z + friedrichsComm μ ρ a v g z) 2 μ
      ≤ eLpNorm (friedrichsComm μ ρ a v (u - g)) 2 μ + eLpNorm (friedrichsComm μ ρ a v g) 2 μ :=
        eLpNorm_add_le (aestronglyMeasurable_friedrichsComm ρ v ha (hul.sub hgl))
          (aestronglyMeasurable_friedrichsComm ρ v ha hgl) one_le_two
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal δ + ENNReal.ofReal (e / 2) :=
        add_le_add ((hbound k _ (hu.sub hg2)).trans (by gcongr)) hk
    _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := by
        gcongr
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal hCδ
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ε := heε.le

/-! ### The zeroth order commutator -/

/-- The commutator `b (ρ ⋆ u) - ρ ⋆ (b u)` of a multiplication operator with the mollifier, the
second term written through the transpose. -/
def zeroComm (μ : Measure E) (ρ : ContDiffBump (0 : E)) (b u : E → ℂ) (z : E) : ℂ :=
  b z * (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] u) z - ∫ y, u y * (b y * (ρ.normed μ (z - y) : ℂ)) ∂μ

theorem zeroComm_eq (ρ : ContDiffBump (0 : E)) (b u : E → ℂ) (z : E) :
    zeroComm μ ρ b u z = b z * (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] u) z -
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ b y * u y) z := by
  rw [zeroComm, bump_convolution_apply_eq_integral ρ (fun y ↦ b y * u y)]
  congr 2
  funext y
  ring

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
theorem memLp_mul_of_bounded {b u : E → ℂ} (hb : Continuous b) {Cb : ℝ} (hCb : ∀ z, ‖b z‖ ≤ Cb)
    (hu : MemLp u 2 μ) : MemLp (fun y ↦ b y * u y) 2 μ :=
  hu.of_le_mul (c := Cb) (hb.aestronglyMeasurable.mul hu.1)
    (Eventually.of_forall fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hCb x) (norm_nonneg _))

theorem aestronglyMeasurable_zeroComm (ρ : ContDiffBump (0 : E)) {b u : E → ℂ}
    (hb : Continuous b) {Cb : ℝ} (hCb : ∀ z, ‖b z‖ ≤ Cb) (hu : MemLp u 2 μ) :
    AEStronglyMeasurable (zeroComm μ ρ b u) μ := by
  have hfun : zeroComm μ ρ b u = fun z ↦ b z * (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] u) z -
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ b y * u y) z := funext (zeroComm_eq ρ b u)
  rw [hfun]
  exact ((hb.mul (contDiff_bump_convolution ρ (hu.locallyIntegrable one_le_two)).continuous).sub
    (contDiff_bump_convolution ρ ((memLp_mul_of_bounded hb hCb hu).locallyIntegrable
      one_le_two)).continuous).aestronglyMeasurable

/-- The zeroth order commutator tends to `0` in `L²` (`b` continuous and bounded). -/
theorem tendsto_eLpNorm_zeroComm {b : E → ℂ} (hb : Continuous b) {Cb : ℝ} (hCb : ∀ z, ‖b z‖ ≤ Cb)
    {u : E → ℂ} (hu : MemLp u 2 μ) {φ : ℕ → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0)) :
    Tendsto (fun k ↦ eLpNorm (zeroComm μ (φ k) b u) 2 μ) atTop (𝓝 0) := by
  have hbu := memLp_mul_of_bounded hb hCb hu
  have hul := hu.locallyIntegrable one_le_two
  have hbul := hbu.locallyIntegrable one_le_two
  have hfun : ∀ k, zeroComm μ (φ k) b u = fun z ↦
      (b z * ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] u) z - b z * u z) -
        (((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ b y * u y) z - b z * u z) := by
    intro k
    funext z
    rw [zeroComm_eq]
    ring
  simp_rw [hfun]
  refine tendsto_eLpNorm_sub
    (f := fun k z ↦ b z * ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] u) z - b z * u z)
    (g := fun k z ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] fun y ↦ b y * u y) z - b z * u z)
    (fun k ↦ ((hb.mul (contDiff_bump_convolution (φ k) hul).continuous).aestronglyMeasurable.sub
      hbu.1))
    (fun k ↦ (contDiff_bump_convolution (φ k) hbul).continuous.aestronglyMeasurable.sub hbu.1)
    ?_ (tendsto_eLpNorm_bump_convolution_sub hbu hφ)
  have h0 := tendsto_eLpNorm_bump_convolution_sub (μ := μ) hu hφ
  have h1 : Tendsto (fun k ↦ ENNReal.ofReal Cb *
      eLpNorm (fun x ↦ ((φ k).normed μ ⋆[lsmul ℝ ℝ, μ] u) x - u x) 2 μ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ zero_le)
    fun k ↦ eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x ↦ ?_) 2
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right (hCb x) (norm_nonneg _)

end SGPT.Trace.TwistedL2.Friedrichs
