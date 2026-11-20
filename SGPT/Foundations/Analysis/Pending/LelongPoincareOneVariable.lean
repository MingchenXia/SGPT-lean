import SGPT.Foundations.Analysis.CircleMeanSecondOrder
import SGPT.Foundations.Analysis.LogLevi
import SGPT.Foundations.Analysis.LeviForm
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Topology

set_option autoImplicit false

/-!
# The Lelong--Poincaré formula in one complex variable

For a meromorphic function `f` on an open set `U ⊆ ℂ`, nowhere locally zero, and a smooth
compactly supported test function `χ` with support in `U`,

  `∫_ℂ log ‖f z‖ · Δχ(z) dλ(z) = 2π ∑_{u} ord_u(f) · χ(u)`

(`integral_log_norm_mul_laplacian`), where `ord_u(f)` is the order of `f` at `u`, the divisor of
`f` (`MeromorphicOn.divisor`), and `Δ = ∂²/∂x² + ∂²/∂y²`.  In the normalisation
`ddᶜ = (i/2π)∂∂̄`, for which `ddᶜ φ = (1/4π) Δφ dλ` on functions, this is the
**Lelong--Poincaré equation** `ddᶜ log |f|² = [zeros of f] - [poles of f]` on `U`
(`Demailly, Complex analytic and differential geometry`, III.2.15, in dimension one): the
distributional Laplacian of `log |f|` is `2π` times the divisor of `f`, counted with
multiplicities.

## Route

* `integral_mul_laplacian_eq` — integration by parts `∫ F Δχ = ∫ ΔF χ` for `F` smooth on a
  neighbourhood of the support of `χ` (a cutoff and the Schwartz-space identity
  `SchwartzMap.integral_mul_laplacian_right_eq_left`);
* `integral_log_norm_mul_laplacian_eq_zero` — the harmonic part: `log ‖g‖` is harmonic where
  `g` is analytic and nonzero (`AnalyticAt.harmonicAt_log_norm`), so its integral against
  `Δχ` vanishes;
* `integral_log_norm_sub_mul_laplacian` — the model: `∫ log ‖z - u‖ Δχ(z) = 2π χ(u)`.  The
  pole is regularized by `L_ε = ½ log (‖z‖² + ε²)`, whose Laplacian is the approximate identity
  `2ε² / (‖z‖² + ε²)²` of total mass `2π` (polar coordinates); dominated convergence passes to
  the limit on both sides;
* `integral_log_norm_mul_laplacian` — the general case: near the support of `χ`, `log ‖f‖` is,
  off a discrete set, `∑ ord_u(f) log ‖z - u‖ + log ‖g‖` with `g` analytic without zeros
  (`MeromorphicOn.extract_zeros_poles_log`).

This is step (LP1) of the formalization of the blueprint lemma `ana:divisor-lelong-poincare`.
Sorry-free.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff Laplacian Manifold

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable

/-! ### Integration by parts for the Laplacian -/

/-- A smooth cutoff equal to `1` near a compact set, supported in an open neighbourhood. -/
theorem exists_cutoff {K W : Set ℂ} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ W ∧
      ∀ᶠ z in 𝓝ˢ K, ψ z = 1 := by
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨ρ, hρ1, hρV, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞))
    (𝓘(ℝ, ℂ)) hK.isClosed (by rwa [hVo.interior_eq])
  have hρsupp : Function.support (ρ : ℂ → ℝ) ⊆ V := fun x hx => by
    by_contra hxV
    exact hx (hρV x hxV)
  exact ⟨ρ, ρ.contMDiff.contDiff,
    HasCompactSupport.of_support_subset_isCompact hVc (hρsupp.trans subset_closure),
    (closure_mono hρsupp).trans hVW, hρ1⟩

/-- `ψ F` is globally smooth when `ψ` is smooth with support in an open set on which `F` is
smooth. -/
theorem contDiff_mul_of_tsupport {ψ F : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hψ : ContDiff ℝ ∞ ψ) (hψW : tsupport ψ ⊆ W) (hF : ContDiffOn ℝ ∞ F W) :
    ContDiff ℝ ∞ (fun z => ψ z * F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ W
  · exact (hψ.contDiffAt.mul (hF.contDiffAt (hW.mem_nhds hz)))
  · have hzs : z ∉ tsupport ψ := fun h => hz (hψW h)
    have hev : (fun z => ψ z * F z) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hzs] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    exact (contDiffAt_const).congr_of_eventuallyEq hev

theorem laplacian_eq_zero_of_notMem_tsupport {χ : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport χ) :
    Δ χ z = 0 := by
  have hev : χ =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
  simp

/-- **Integration by parts for the Laplacian against a function smooth near the support.**  For
`χ` smooth with compact support and `F` smooth on an open neighbourhood of `tsupport χ`,
`∫ F Δχ = ∫ ΔF χ`. -/
theorem integral_mul_laplacian_eq {χ F : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχW : tsupport χ ⊆ W)
    (hF : ContDiffOn ℝ ∞ F W) :
    ∫ z, F z * Δ χ z = ∫ z, Δ F z * χ z := by
  obtain ⟨ψ, hψ, hψc, hψW, hψ1⟩ := exists_cutoff hχc hW hχW
  set G : ℂ → ℝ := fun z => ψ z * F z with hG
  have hGs : ContDiff ℝ ∞ G := contDiff_mul_of_tsupport hW hψ hψW hF
  have hGc : HasCompactSupport G := hψc.mul_right
  have hibp := SchwartzMap.integral_mul_laplacian_right_eq_left (μ := (volume : Measure ℂ))
    (hGc.toSchwartzMap hGs) (hχc.toSchwartzMap hχ)
  simp only [SchwartzMap.laplacian_apply, HasCompactSupport.toSchwartzMap_toFun] at hibp
  have hGF : ∀ᶠ z in 𝓝ˢ (tsupport χ), G z = F z := by
    filter_upwards [hψ1] with z hz
    simp [hG, hz]
  have h1 : (fun z => G z * Δ χ z) = fun z => F z * Δ χ z := by
    funext z
    by_cases hz : z ∈ tsupport χ
    · rw [hGF.self_of_nhdsSet z hz]
    · rw [laplacian_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  have h2 : (fun z => Δ G z * χ z) = fun z => Δ F z * χ z := by
    funext z
    by_cases hz : z ∈ tsupport χ
    · have hev : G =ᶠ[𝓝 z] F := hGF.filter_mono (nhds_le_nhdsSet hz)
      rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
  rw [← h1, ← h2]
  exact hibp

/-! ### The harmonic part -/

/-- `log ‖g‖` is smooth where `g` is analytic and has no zero. -/
theorem contDiffOn_log_norm {g : ℂ → ℂ} {W : Set ℂ}
    (hg : AnalyticOnNhd ℂ g W) (hg0 : ∀ z ∈ W, g z ≠ 0) :
    ContDiffOn ℝ ∞ (fun z => Real.log ‖g z‖) W := by
  intro z hz
  have hgz : ContDiffAt ℝ ∞ g z :=
    ((hg z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have hn : ContDiffAt ℝ ∞ (fun w => ‖g w‖) z := hgz.norm ℝ (hg0 z hz)
  exact (hn.log (norm_ne_zero_iff.mpr (hg0 z hz))).contDiffWithinAt

/-- **The harmonic part.**  If `g` is analytic without zeros on an open neighbourhood of the
support of `χ`, then `∫ log ‖g‖ Δχ = 0`. -/
theorem integral_log_norm_mul_laplacian_eq_zero {g : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hg : AnalyticOnNhd ℂ g W) (hg0 : ∀ z ∈ W, g z ≠ 0) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχW : tsupport χ ⊆ W) :
    ∫ z, Real.log ‖g z‖ * Δ χ z = 0 := by
  rw [integral_mul_laplacian_eq hW hχ hχc hχW (contDiffOn_log_norm hg hg0)]
  have h0 : (fun z => Δ (fun w => Real.log ‖g w‖) z * χ z) = fun _ => 0 := by
    funext z
    by_cases hz : z ∈ W
    · have hh := (hg z hz).harmonicAt_log_norm (hg0 z hz)
      rw [hh.2.self_of_nhds, Pi.zero_apply, zero_mul]
    · have hzs : z ∉ tsupport χ := fun h => hz (hχW h)
      rw [image_eq_zero_of_notMem_tsupport hzs, mul_zero]
  rw [h0, integral_zero]

/-! ### The model: a single logarithmic pole -/

/-- The kernel `2 / (‖z‖² + 1)²`; `Δ (½ log (‖z‖² + ε²))` is its rescaling. -/
def kernel (z : ℂ) : ℝ := 2 / (‖z‖ ^ 2 + 1) ^ 2

/-- The regularized logarithm `½ log (‖z‖² + ε²)`. -/
def regLog (ε : ℝ) (z : ℂ) : ℝ := (1 / 2 : ℝ) * Real.log (‖z‖ ^ 2 + ε ^ 2)

theorem regLog_eq_smul (ε : ℝ) :
    regLog ε = (1 / 2 : ℝ) • SGPT.Foundations.Analysis.regularizedLogNormSq (E := ℂ) (ε ^ 2) := by
  funext z
  simp [regLog, SGPT.Foundations.Analysis.regularizedLogNormSq]

theorem contDiff_regLog {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (regLog ε) := by
  rw [regLog_eq_smul]
  exact (SGPT.Foundations.Analysis.contDiff_regularizedLogNormSq (H := ℂ) (n := ∞)
    (by positivity)).const_smul (1 / 2 : ℝ)

/-- `Δ (½ log (‖z‖² + ε²)) = 2ε² / (‖z‖² + ε²)²`. -/
theorem laplacian_regLog {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Δ (regLog ε) z = 2 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hc : (0 : ℝ) < ε ^ 2 := by positivity
  have hsmooth : ContDiffAt ℝ 2
      (SGPT.Foundations.Analysis.regularizedLogNormSq (E := ℂ) (ε ^ 2)) z :=
    (SGPT.Foundations.Analysis.contDiff_regularizedLogNormSq (H := ℂ) hc).contDiffAt
  have h := SGPT.Foundations.Analysis.laplacian_complexLine
    (u := SGPT.Foundations.Analysis.regularizedLogNormSq (E := ℂ) (ε ^ 2))
    (SGPT.Foundations.Analysis.contDiff_regularizedLogNormSq hc) 0 1 z
  simp only [zero_add, smul_eq_mul, mul_one] at h
  have h' : Δ (SGPT.Foundations.Analysis.regularizedLogNormSq (E := ℂ) (ε ^ 2)) z =
      4 * SGPT.Foundations.Analysis.leviForm
        (SGPT.Foundations.Analysis.regularizedLogNormSq (E := ℂ) (ε ^ 2)) z 1 := h
  rw [regLog_eq_smul, InnerProductSpace.laplacian_smul _ hsmooth, h',
    SGPT.Foundations.Analysis.leviForm_regularizedLogNormSq hc]
  simp
  ring

/-- `Δ (½ log (‖·‖² + ε²))` is the rescaled kernel `ε⁻² K(ε⁻¹ z)`. -/
theorem laplacian_regLog_eq_kernel {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Δ (regLog ε) z = (ε ^ 2)⁻¹ * kernel (ε⁻¹ • z) := by
  rw [laplacian_regLog hε, kernel, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  field_simp

/-- `∫_0^∞ r · 2 / (r² + 1)² dr = 1`. -/
theorem integral_Ioi_kernel_profile :
    ∫ r in Ioi (0 : ℝ), r * (2 / (r ^ 2 + 1) ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => -(r ^ 2 + 1)⁻¹)
      (x * (2 / (x ^ 2 + 1) ^ 2)) x := by
    intro x _
    have hx : x ^ 2 + 1 ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).add_const 1).inv hx).neg
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    · simp
      ring
    · simp
  have hlim : Tendsto (fun r : ℝ => -(r ^ 2 + 1)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => r ^ 2 + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp this).neg
  have hint : IntegrableOn (fun r : ℝ => r * (2 / (r ^ 2 + 1) ^ 2)) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
      have : (0 : ℝ) < x := hx
      positivity) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  norm_num

theorem integrableOn_Ioi_kernel_profile :
    IntegrableOn (fun r : ℝ => r * (2 / (r ^ 2 + 1) ^ 2)) (Ioi 0) := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun r : ℝ => -(r ^ 2 + 1)⁻¹)
      (x * (2 / (x ^ 2 + 1) ^ 2)) x := by
    intro x _
    have hx : x ^ 2 + 1 ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).add_const 1).inv hx).neg
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    · simp
      ring
    · simp
  have hlim : Tendsto (fun r : ℝ => -(r ^ 2 + 1)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun r : ℝ => r ^ 2 + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp this).neg
  exact integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
    have : (0 : ℝ) < x := hx
    positivity) hlim

theorem integrable_kernel : Integrable kernel := by
  have h := (integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => 2 / (r ^ 2 + 1) ^ 2)).mpr (by
      simpa [Complex.finrank_real_complex] using integrableOn_Ioi_kernel_profile)
  exact h

/-- **The kernel has total mass `2π`.** -/
theorem integral_kernel : ∫ z, kernel z = 2 * Real.pi := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => 2 / (r ^ 2 + 1) ^ 2)
  simp only [Complex.finrank_real_complex] at h
  have hball : (volume : Measure ℂ).real (ball (0 : ℂ) 1) = Real.pi := by
    simp [measureReal_def, Complex.volume_ball]
  rw [show (fun z : ℂ => kernel z) = fun z => 2 / (‖z‖ ^ 2 + 1) ^ 2 from rfl, h, hball]
  have hprof : (fun y : ℝ => y ^ (2 - 1) • (2 / (y ^ 2 + 1) ^ 2)) =
      fun y => y * (2 / (y ^ 2 + 1) ^ 2) := by
    funext y
    norm_num
  rw [hprof, integral_Ioi_kernel_profile, nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring


theorem kernel_nonneg (z : ℂ) : 0 ≤ kernel z := by
  unfold kernel
  positivity

/-- Change of variables `z = ε w`: `∫ Δ L_ε · χ = ∫ K(w) χ(ε w)`. -/
theorem integral_laplacian_regLog_mul {ε : ℝ} (hε : 0 < ε) (χ : ℂ → ℝ) :
    ∫ z, Δ (regLog ε) z * χ z = ∫ w, kernel w * χ (ε • w) := by
  have h := Measure.integral_comp_smul (volume : Measure ℂ)
    (fun w => kernel w * χ (ε • w)) ε⁻¹
  simp only [Complex.finrank_real_complex, smul_smul, mul_inv_cancel₀ hε.ne', one_smul] at h
  have hfun : (fun z => Δ (regLog ε) z * χ z) =
      fun z => (ε ^ 2)⁻¹ * (kernel (ε⁻¹ • z) * χ z) := by
    funext z
    rw [laplacian_regLog_eq_kernel hε, mul_assoc]
  rw [hfun, integral_const_mul, h, smul_eq_mul, inv_pow, inv_inv,
    abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2), ← mul_assoc, inv_mul_cancel₀ (by positivity),
    one_mul]

/-- **The kernel is an approximate identity of mass `2π`.** -/
theorem tendsto_integral_kernel_mul {χ : ℂ → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Tendsto (fun ε : ℝ => ∫ w, kernel w * χ (ε • w)) (𝓝 0) (𝓝 (2 * Real.pi * χ 0)) := by
  obtain ⟨C, hC⟩ := hχ.bounded_above_of_compact_support hχc
  have hlim : ∫ w, kernel w * χ ((0 : ℝ) • w) = 2 * Real.pi * χ 0 := by
    simp only [zero_smul]
    rw [integral_mul_const, integral_kernel]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun w => kernel w * C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε => integrable_kernel.aestronglyMeasurable.mul
      (hχ.comp (continuous_const_smul ε)).aestronglyMeasurable
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun w => by
      rw [norm_mul, Real.norm_of_nonneg (kernel_nonneg w)]
      exact mul_le_mul_of_nonneg_left (hC _) (kernel_nonneg w)
  · exact integrable_kernel.mul_const C
  · exact Eventually.of_forall fun w =>
      (continuous_const.mul (hχ.comp (continuous_id.smul continuous_const))).tendsto 0

/-- `log ‖z‖` is locally integrable on `ℂ` (polar coordinates: `r log r` is continuous). -/
theorem locallyIntegrable_log_norm : LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, -, hR⟩ := hK.isBounded.exists_pos_norm_lt
  refine IntegrableOn.mono_set ?_ (fun z hz => mem_ball_zero_iff.mpr (hR z hz))
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := Real.log)]
  simp only [Complex.finrank_real_complex]
  have hfun : (fun y : ℝ => y ^ (2 - 1) • Real.log y) = fun y => y * Real.log y := by
    funext y
    norm_num
  rw [hfun]
  exact (Real.continuous_mul_log.integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- `log ‖z‖ · φ(z)` is integrable for `φ` continuous with compact support. -/
theorem integrable_log_norm_mul {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z => Real.log ‖z‖ * φ z) := by
  have h := locallyIntegrable_log_norm.integrable_smul_left_of_hasCompactSupport hφ hφc
  simpa only [smul_eq_mul, mul_comm] using h

/-- `log ‖z - u‖ · φ(z)` is integrable for `φ` continuous with compact support. -/
theorem integrable_log_norm_sub_mul {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (u : ℂ) : Integrable (fun z => Real.log ‖z - u‖ * φ z) := by
  have hφ' : Continuous (fun w => φ (w + u)) := hφ.comp (continuous_id.add continuous_const)
  have hφc' : HasCompactSupport (fun w => φ (w + u)) := hφc.comp_homeomorph (Homeomorph.addRight u)
  have h := (integrable_log_norm_mul hφ' hφc').comp_sub_right u
  simpa only [sub_add_cancel] using h

theorem continuous_regLog {ε : ℝ} (hε : 0 < ε) : Continuous (regLog ε) :=
  (contDiff_regLog hε).continuous

/-- `L_ε → log ‖·‖` against a continuous compactly supported function, as `ε → 0⁺`
(dominated convergence; for `0 < ε ≤ 1`, `log ‖z‖ ≤ L_ε(z) ≤ L_1(z)`). -/
theorem tendsto_integral_regLog_mul {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun ε => ∫ z, regLog ε z * φ z) (𝓝[>] 0) (𝓝 (∫ z, Real.log ‖z‖ * φ z)) := by
  have hbound : Integrable (fun z => |Real.log ‖z‖ * φ z| + |regLog 1 z * φ z|) :=
    (integrable_log_norm_mul hφ hφc).abs.add
      (((continuous_regLog one_pos).mul hφ).integrable_of_hasCompactSupport hφc.mul_left).abs
  have hne : ∀ᵐ z : ℂ, z ≠ 0 := by
    have : (volume : Measure ℂ) {0} = 0 := measure_singleton 0
    exact compl_mem_ae_iff.mpr this
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbound ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ((continuous_regLog hε).mul hφ).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hne] with z hz
    have hz2 : 0 < ‖z‖ ^ 2 := by positivity
    have hlo : Real.log ‖z‖ ≤ regLog ε z := by
      have : Real.log ‖z‖ = (1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) := by
        rw [Real.log_pow]
        push_cast
        ring
      rw [this, regLog]
      gcongr
      nlinarith [sq_nonneg ε]
    have hhi : regLog ε z ≤ regLog 1 z := by
      have h0 : 0 < ε := hε.1
      have h1 : ε ≤ 1 := hε.2
      have hle : ‖z‖ ^ 2 + ε ^ 2 ≤ ‖z‖ ^ 2 + 1 ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hle) (by norm_num)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log ‖z‖), abs_nonneg (regLog 1 z)],
      by linarith [le_abs_self (regLog 1 z), abs_nonneg (Real.log ‖z‖)]⟩
  · filter_upwards [hne] with z hz
    refine Tendsto.mul_const _ (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have hz2 : ‖z‖ ^ 2 + (0 : ℝ) ^ 2 ≠ 0 := by positivity
    have hc : ContinuousAt (fun ε : ℝ => regLog ε z) 0 := by
      unfold regLog
      exact continuousAt_const.mul
        ((continuousAt_const.add (continuous_pow 2).continuousAt).log hz2)
    have h0 : regLog 0 z = Real.log ‖z‖ := by
      rw [regLog, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.log_pow]
      push_cast
      ring
    simpa only [h0] using hc.tendsto

theorem continuous_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) : Continuous (Δ χ) :=
  SGPT.Foundations.Analysis.continuous_laplacian_complex (hχ.of_le ENat.LEInfty.out)

theorem support_laplacian_subset (χ : ℂ → ℝ) : Function.support (Δ χ) ⊆ tsupport χ :=
  fun _ hz => by
    by_contra h
    exact hz (laplacian_eq_zero_of_notMem_tsupport h)

theorem hasCompactSupport_laplacian {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (Δ χ) :=
  hχc.mono' (support_laplacian_subset χ)

/-- **The model at the origin:** `∫ log ‖z‖ Δχ(z) = 2π χ(0)`. -/
theorem integral_log_norm_mul_laplacian_zero {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∫ z, Real.log ‖z‖ * Δ χ z = 2 * Real.pi * χ 0 := by
  have h1 := tendsto_integral_regLog_mul (continuous_laplacian hχ)
    (hasCompactSupport_laplacian hχc)
  have h2 : Tendsto (fun ε => ∫ z, regLog ε z * Δ χ z) (𝓝[>] 0) (𝓝 (2 * Real.pi * χ 0)) := by
    refine ((tendsto_integral_kernel_mul hχ.continuous hχc).mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [integral_mul_laplacian_eq isOpen_univ hχ hχc (subset_univ _)
      (contDiff_regLog hε).contDiffOn, integral_laplacian_regLog_mul hε]
  exact tendsto_nhds_unique h1 h2

/-- The Laplacian commutes with translations. -/
theorem laplacian_comp_add_right (χ : ℂ → ℝ) (u : ℂ) :
    Δ (fun w => χ (w + u)) = fun w => Δ χ (w + u) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  funext w
  simp only [iteratedFDeriv_comp_add_right]

/-- **The model:** `∫ log ‖z - u‖ Δχ(z) = 2π χ(u)`. -/
theorem integral_log_norm_sub_mul_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (u : ℂ) :
    ∫ z, Real.log ‖z - u‖ * Δ χ z = 2 * Real.pi * χ u := by
  have hχ' : ContDiff ℝ ∞ (fun w => χ (w + u)) := hχ.comp (contDiff_id.add contDiff_const)
  have hχc' : HasCompactSupport (fun w => χ (w + u)) :=
    hχc.comp_homeomorph (Homeomorph.addRight u)
  have h := integral_log_norm_mul_laplacian_zero hχ' hχc'
  rw [laplacian_comp_add_right] at h
  simp only [zero_add] at h
  rw [← h, ← integral_add_right_eq_self (fun z => Real.log ‖z - u‖ * Δ χ z) u]
  simp only [add_sub_cancel_right]

/-! ### The general case -/

/-- **The Lelong--Poincaré formula in one variable.**  Let `f` be meromorphic on an open set
`U ⊆ ℂ` and nowhere locally zero (its order is finite at every point of `U`), and let `χ` be
smooth with compact support in `U`.  Then
`∫ log ‖f z‖ Δχ(z) dλ(z) = 2π ∑_u ord_u(f) χ(u)`: the distributional Laplacian of `log ‖f‖` on
`U` is `2π` times the divisor of `f`. -/
theorem integral_log_norm_mul_laplacian {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : MeromorphicOn f U) (hf0 : ∀ u : U, meromorphicOrderAt f u ≠ ⊤)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, Real.log ‖f z‖ * Δ χ z =
      2 * Real.pi * ∑ᶠ u, (MeromorphicOn.divisor f U u : ℝ) * χ u := by
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hχc hU hχU
  have hWU' : W ⊆ U := subset_closure.trans hWU
  have hfW : MeromorphicOn f W := hf.mono_set hWU'
  have hf0W : ∀ u : W, meromorphicOrderAt f u ≠ ⊤ := fun u => hf0 ⟨u, hWU' u.2⟩
  have hfin : (MeromorphicOn.divisor f W).support.Finite :=
    (hf.mono_set hWU).divisor_support_finite_of_subset hWc subset_closure
  obtain ⟨g, hg, hg0, hfg⟩ := hfW.extract_zeros_poles hf0W hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfg
  have hg0' : ∀ z ∈ W, g z ≠ 0 := fun z hz => hg0 ⟨z, hz⟩
  set d := MeromorphicOn.divisor f W with hd
  set S := hfin.toFinset with hS
  have hdW : ∀ u, (d u : ℝ) * χ u = (MeromorphicOn.divisor f U u : ℝ) * χ u := by
    intro u
    by_cases hu : u ∈ W
    · rw [hd, ← MeromorphicOn.divisor_restrict hf hWU',
        Function.locallyFinsuppWithin.restrict_apply, if_pos hu]
    · have : χ u = 0 := image_eq_zero_of_notMem_tsupport (fun h => hu (hKW h))
      rw [this, mul_zero, mul_zero]
  have hsum : (∑ᶠ u, fun x : ℂ => (d u : ℝ) * Real.log ‖x - u‖) =
      fun x => ∑ u ∈ S, (d u : ℝ) * Real.log ‖x - u‖ := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · funext x
      rw [Finset.sum_apply]
    · intro u hu
      rw [hS, Set.Finite.coe_toFinset]
      by_contra h
      apply hu
      funext x
      simp [Function.notMem_support.mp h]
  have hΔ := continuous_laplacian hχ
  have hae : (fun z => Real.log ‖f z‖ * Δ χ z) =ᵐ[volume]
      fun z => ∑ u ∈ S, (d u : ℝ) * (Real.log ‖z - u‖ * Δ χ z) + Real.log ‖g z‖ * Δ χ z := by
    have h1 : ∀ᵐ z ∂(volume.restrict W), Real.log ‖f z‖ =
        ((∑ᶠ u, fun x : ℂ => (d u : ℝ) * Real.log ‖x - u‖) + fun x => Real.log ‖g x‖) z :=
      ae_restrict_le_codiscreteWithin hWo.measurableSet hlog
    rw [ae_restrict_iff' hWo.measurableSet] at h1
    filter_upwards [h1] with z hz
    by_cases hzW : z ∈ W
    · simp only [hz hzW, Pi.add_apply, hsum, add_mul, Finset.sum_mul, mul_assoc]
    · have : Δ χ z = 0 := laplacian_eq_zero_of_notMem_tsupport (fun h => hzW (hKW h))
      simp [this]
  rw [integral_congr_ae hae]
  have hint : ∀ u ∈ S, Integrable (fun z => (d u : ℝ) * (Real.log ‖z - u‖ * Δ χ z)) :=
    fun u _ => (integrable_log_norm_sub_mul hΔ (hasCompactSupport_laplacian hχc) u).const_mul _
  have hgint : Integrable (fun z => Real.log ‖g z‖ * Δ χ z) := by
    have hsupp : Function.support (fun z => Real.log ‖g z‖ * Δ χ z) ⊆ tsupport χ := by
      intro z hz
      by_contra h
      exact hz (by simp [laplacian_eq_zero_of_notMem_tsupport h])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
    exact ContinuousOn.integrableOn_compact hχc
      (((contDiffOn_log_norm hg hg0').continuousOn.mono hKW).mul hΔ.continuousOn)
  rw [integral_add (integrable_finsetSum S hint) hgint, integral_finsetSum S hint,
    integral_log_norm_mul_laplacian_eq_zero hWo hg hg0' hχ hχc hKW, add_zero]
  simp only [integral_const_mul, integral_log_norm_sub_mul_laplacian hχ hχc]
  rw [finsum_eq_sum_of_support_subset (s := S), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hdW u]
    ring
  · intro u hu
    rw [hS, Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hu
    intro h
    apply hu
    rw [← hdW u, h]
    simp

end SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable
