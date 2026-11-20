import SGPT.Analysis.CZContact

/-!
# Interior Lipschitz estimate for functions with bounded Laplacian

Lane C11-REAL (`claude-c11-real`, node `c11r:gradient`).  A Calderón–Zygmund-free replacement
for the `W^{2,p}` + Morrey gradient bound used in FPT `lem:penalized-real-hessian`, Step 1 (the
uniform gradient bound for the penalized Monge–Ampère equations on the way to `thm:Tos_C11`),
and for the commutator estimates needed to smooth obstacles with bounded Laplacian.

**Theorem** (`exists_lipschitz_of_laplacian_bound`).  There is a constant `C` depending only on
`n` such that: if `w` is continuous on an open `U ⊆ ℂⁿ`, `|w| ≤ K` on `U`, and
`|∫ w ∑_j ∂_j∂̄_j φ| ≤ M ∫ |φ|` for every test function `φ` supported in `U` (that is,
`|Δw| ≤ 4M`), then for `B̄(y, r) ∪ B̄(y', r) ⊆ U`
`|w(y) - w(y')| ≤ C (K / r + M r) ‖y - y'‖`.

## Proof

Let `κ` be TN's unit radial kernel and `Ψ ≥ 0` the unit radial Poisson potential with
`4 ∑_j ∂_j∂̄_j Ψ = κ - κ_{1/2}`; put `κ_s = s^{-d} κ(·/s)` and `Ψ_s = s^{2-d} Ψ(·/s)` (`d = 2n`), so
that `4 ∑_j ∂_j∂̄_j Ψ_s = κ_s - κ_{s/2}`.  With `A_s(y) = ∫ w κ_s(· - y)` and `T(φ) = ∫ w ∑_j ∂_j∂̄_j φ`,
`A_{s/2}(y) = A_s(y) - 4 T(Ψ_s(· - y))` exactly.  Iterating along `s_m = r 2^{-m}`,
`A_{s_m}(y) - A_{s_m}(y') = A_r(y) - A_r(y') - 4 ∑_{k<m} T(Ψ_{s_k}(· - y) - Ψ_{s_k}(· - y'))`.
The `L¹` modulus of a fixed `C¹` function with compact support is linear
(`∫ |g(u + h) - g(u)| ≤ C_g ‖h‖`), so by scaling
`‖κ_r(· - y) - κ_r(· - y')‖₁ ≤ C ‖y - y'‖ / r` and `‖Ψ_s(· - y) - Ψ_s(· - y')‖₁ ≤ C s ‖y - y'‖`;
since `∑ s_k ≤ 2r` and `A_{s_m} → w` as `m → ∞` the estimate follows.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.Analysis.CZ

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.RadialLeviPreimage
open SGPT.Okounkov.TranscendentalWNReg

variable {n : ℕ}

/-! ### The `L¹` modulus of a `C¹` function with compact support -/

/-- **Linear `L¹` modulus**: a `C¹` function `g` vanishing outside `B̄(0, 1)` satisfies
`∫ |g(u + h) - g(u)| du ≤ C ‖h‖` for all `h`. -/
theorem exists_integral_abs_sub_le {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 1 g)
    (hgs : ∀ x, 1 < ‖x‖ → g x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ComplexModel n, ∫ u, |g (u + h) - g u| ≤ C * ‖h‖ := by
  have hsupp : tsupport g ⊆ closedBall 0 1 := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hx (hgs x (lt_of_not_ge h))
  have hgc : HasCompactSupport g := (isCompact_closedBall 0 1).of_isClosed_subset
    (isClosed_tsupport _) hsupp
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨L, hL⟩ := hDc.bounded_above_of_compact_support (hgc.fderiv (𝕜 := ℝ))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hlip : ∀ x y : ComplexModel n, |g y - g x| ≤ L * ‖y - x‖ := by
    intro x y
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ)
      (fun z _ => (hg.differentiable one_ne_zero) z) (fun z _ => hL z) convex_univ (mem_univ x)
      (mem_univ y)
    simpa [Real.norm_eq_abs] using this
  have hgint : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  set V : ℝ := volume.real (closedBall (0 : ComplexModel n) 2) with hV
  refine ⟨max (L * V) (2 * ∫ u, |g u|), le_max_of_le_right (by positivity), fun h => ?_⟩
  have hcont : Continuous (fun u => |g (u + h) - g u|) :=
    ((hg.continuous.comp (continuous_id.add continuous_const)).sub hg.continuous).abs
  rcases le_or_gt ‖h‖ 1 with hh | hh
  · -- small translations: Lipschitz bound on a fixed ball
    have hzero : ∀ u, u ∉ closedBall (0 : ComplexModel n) 2 → |g (u + h) - g u| = 0 := by
      intro u hu
      rw [mem_closedBall, dist_zero_right, not_le] at hu
      have h1 : g u = 0 := hgs u (by linarith)
      have h2 : g (u + h) = 0 := hgs (u + h) (by
        have := norm_sub_norm_le u (-h)
        rw [sub_neg_eq_add, norm_neg] at this
        linarith)
      rw [h1, h2, sub_zero, abs_zero]
    have hfin : volume (closedBall (0 : ComplexModel n) 2) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hle : ∀ u, |g (u + h) - g u| ≤
        (closedBall (0 : ComplexModel n) 2).indicator (fun _ => L * ‖h‖) u := by
      intro u
      by_cases hu : u ∈ closedBall (0 : ComplexModel n) 2
      · rw [indicator_of_mem hu]
        have := hlip u (u + h)
        rwa [add_sub_cancel_left] at this
      · rw [indicator_of_notMem hu, hzero u hu]
    have hint1 : Integrable (fun u => |g (u + h) - g u|) := by
      refine hcont.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ComplexModel n) 2) fun u hu => ?_
      exact hzero u hu
    calc ∫ u, |g (u + h) - g u|
        ≤ ∫ u, (closedBall (0 : ComplexModel n) 2).indicator (fun _ => L * ‖h‖) u :=
          integral_mono hint1 ((integrable_indicator_iff measurableSet_closedBall).mpr
            (integrableOn_const hfin)) hle
      _ = L * ‖h‖ * V := by
          rw [integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul, hV]
          ring
      _ = L * V * ‖h‖ := by ring
      _ ≤ max (L * V) (2 * ∫ u, |g u|) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg h)
  · -- large translations: the trivial bound
    have hshift : Integrable (fun u => g (u + h)) := hgint.comp_add_right h
    have hint1 : Integrable (fun u => |g (u + h) - g u|) := (hshift.sub hgint).abs
    calc ∫ u, |g (u + h) - g u| ≤ ∫ u, (|g (u + h)| + |g u|) :=
          integral_mono hint1 (hshift.abs.add hgint.abs) fun u => abs_sub _ _
      _ = 2 * ∫ u, |g u| := by
          rw [integral_add hshift.abs hgint.abs,
            integral_add_right_eq_self (fun u => |g u|) h]
          ring
      _ ≤ 2 * (∫ u, |g u|) * ‖h‖ := by
          have : 0 ≤ 2 * ∫ u, |g u| := by positivity
          nlinarith
      _ ≤ max (L * V) (2 * ∫ u, |g u|) * ‖h‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg h)

/-- **Scaled `L¹` modulus**: for `s > 0`,
`∫ |g(s⁻¹(z - y)) - g(s⁻¹(z - y'))| dz ≤ C s^{d-1} ‖y - y'‖` (written `s^d · (‖y - y'‖ / s)`). -/
theorem integral_abs_sub_scaled_le {g : ComplexModel n → ℝ} {C : ℝ}
    (hC : ∀ h : ComplexModel n, ∫ u, |g (u + h) - g u| ≤ C * ‖h‖) {s : ℝ} (hs : 0 < s)
    (y y' : ComplexModel n) :
    ∫ z, |g (s⁻¹ • (z - y)) - g (s⁻¹ • (z - y'))| ≤
      s ^ Module.finrank ℝ (ComplexModel n) * (C * (‖y - y'‖ / s)) := by
  set h : ComplexModel n := s⁻¹ • (y' - y) with hh
  have htrans : ∫ z, |g (s⁻¹ • (z - y)) - g (s⁻¹ • (z - y'))| =
      ∫ z, |g (s⁻¹ • z + h) - g (s⁻¹ • z)| := by
    rw [← integral_add_right_eq_self (fun z => |g (s⁻¹ • (z - y)) - g (s⁻¹ • (z - y'))|) y']
    congr 1
    funext z
    simp only [hh, add_sub_cancel_right]
    congr 3
    rw [← smul_add]
    congr 1
    abel
  rw [htrans]
  have hscale := Measure.integral_comp_inv_smul_of_nonneg volume
    (fun u : ComplexModel n => |g (u + h) - g u|) hs.le
  rw [hscale, smul_eq_mul]
  have hnorm : ‖h‖ = ‖y - y'‖ / s := by
    rw [hh, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, norm_sub_rev, div_eq_inv_mul]
  rw [← hnorm]
  exact mul_le_mul_of_nonneg_left (hC h) (by positivity)

/-! ### Scaled kernels and potentials -/

/-- TN's unit radial probability kernel (radius `1`). -/
def unitKernel (n : ℕ) : ComplexModel n → ℝ := explicitRadialKernel 1 one_pos 0

/-- TN's unit radial Poisson potential: `4 ∑_j ∂_j∂̄_j Ψ = κ - κ_{1/2}`. -/
def unitPotential (n : ℕ) : ComplexModel n → ℝ := explicitRadialPoissonPotential 1 one_pos 0 1

/-- The kernel at scale `s` centred at `y`: `κ_s(z - y) = s^{-d} κ(s⁻¹ (z - y))`. -/
def scaledKernel (s : ℝ) (y z : ComplexModel n) : ℝ :=
  (s ^ Module.finrank ℝ (ComplexModel n))⁻¹ * unitKernel n (s⁻¹ • (z - y))

/-- The potential at scale `s` centred at `y`: `Ψ_s(z - y) = s^{2-d} Ψ(s⁻¹ (z - y))`. -/
def scaledPotential (s : ℝ) (y z : ComplexModel n) : ℝ :=
  s ^ 2 * (s ^ Module.finrank ℝ (ComplexModel n))⁻¹ * unitPotential n (s⁻¹ • (z - y))

theorem unitKernel_contDiff : ContDiff ℝ ∞ (unitKernel n) :=
  explicitRadialKernel_contDiff 1 one_pos 0

theorem unitPotential_contDiff (hn : 0 < n) : ContDiff ℝ ∞ (unitPotential n) :=
  explicitRadialPoissonPotential_contDiff hn 1 one_pos 0 1

theorem unitKernel_eq_zero {x : ComplexModel n} (hx : 1 < ‖x‖) : unitKernel n x = 0 :=
  explicitRadialKernel_eq_zero_of_lt 1 one_pos 0 (by simpa using hx)

theorem unitPotential_eq_zero (hn : 0 < n) {x : ComplexModel n} (hx : 1 < ‖x‖) :
    unitPotential n x = 0 :=
  explicitRadialPoissonPotential_eq_zero_of_outer hn 1 one_pos (Nat.zero_le 1)
    (by simpa using hx.le)

theorem scaledKernel_nonneg (s : ℝ) (hs : 0 < s) (y z : ComplexModel n) :
    0 ≤ scaledKernel s y z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hs.le _)) (explicitRadialKernel_nonneg 1 one_pos 0 _)

theorem scaledKernel_eq_zero {s : ℝ} (hs : 0 < s) {y z : ComplexModel n} (hz : s < ‖z - y‖) :
    scaledKernel s y z = 0 := by
  rw [scaledKernel, unitKernel_eq_zero, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div, lt_div_iff₀ hs,
    one_mul]
  exact hz

theorem scaledPotential_eq_zero (hn : 0 < n) {s : ℝ} (hs : 0 < s) {y z : ComplexModel n}
    (hz : s < ‖z - y‖) : scaledPotential s y z = 0 := by
  rw [scaledPotential, unitPotential_eq_zero hn, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div, lt_div_iff₀ hs,
    one_mul]
  exact hz

theorem scaledKernel_contDiff (s : ℝ) (y : ComplexModel n) :
    ContDiff ℝ ∞ (scaledKernel s y) :=
  contDiff_const.mul (unitKernel_contDiff.comp
    ((contDiff_id.sub contDiff_const).const_smul s⁻¹))

theorem scaledPotential_contDiff (hn : 0 < n) (s : ℝ) (y : ComplexModel n) :
    ContDiff ℝ ∞ (scaledPotential s y) :=
  contDiff_const.mul ((unitPotential_contDiff hn).comp
    ((contDiff_id.sub contDiff_const).const_smul s⁻¹))

theorem tsupport_scaledKernel {s : ℝ} (hs : 0 < s) (y : ComplexModel n) :
    tsupport (scaledKernel s y) ⊆ closedBall y s := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hz (scaledKernel_eq_zero hs (lt_of_not_ge h))

theorem tsupport_scaledPotential (hn : 0 < n) {s : ℝ} (hs : 0 < s) (y : ComplexModel n) :
    tsupport (scaledPotential s y) ⊆ closedBall y s := by
  refine closure_minimal (fun z hz => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hz (scaledPotential_eq_zero hn hs (lt_of_not_ge h))

theorem integral_scaledKernel {s : ℝ} (hs : 0 < s) (y : ComplexModel n) :
    ∫ z, scaledKernel s y z = 1 := by
  have h1 : ∫ z, scaledKernel s y z =
      (s ^ Module.finrank ℝ (ComplexModel n))⁻¹ * ∫ z, unitKernel n (s⁻¹ • z) := by
    simp only [scaledKernel]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun z => unitKernel n (s⁻¹ • z)) y
  rw [h1, Measure.integral_comp_inv_smul_of_nonneg volume (unitKernel n) hs.le, smul_eq_mul,
    unitKernel, explicitRadialKernel_integral_one, mul_one, inv_mul_cancel₀]
  exact pow_ne_zero _ hs.ne'

/-- Scaling of the coordinate Levi trace: `∑_j ∂_j∂̄_j [c u(s⁻¹(· - y))] = c s^{-2} (∑_j ∂_j∂̄_j u)(s⁻¹(· - y))`. -/
theorem coordinateLeviTrace_scale {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 2 u) (c s : ℝ)
    (y z : ComplexModel n) :
    coordinateLeviTrace (fun x => c * u (s⁻¹ • (x - y))) z =
      c * (s⁻¹ * s⁻¹) * coordinateLeviTrace u (s⁻¹ • (z - y)) := by
  have hA : (fun x => u (s⁻¹ • (x - y))) =
      fun x => u (-(s⁻¹ • y) + (s⁻¹ • ContinuousLinearMap.id ℝ (ComplexModel n)) x) := by
    funext x
    congr 1
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_sub]
    abel
  have hR : ∀ a b : ComplexModel n, realHessian (fun x => u (s⁻¹ • (x - y))) z a b =
      s⁻¹ * s⁻¹ * realHessian u (s⁻¹ • (z - y)) a b := by
    intro a b
    rw [hA, realHessian_comp_affine hu]
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
      realHessian_smul_left, realHessian_smul_right]
    have : -(s⁻¹ • y) + s⁻¹ • z = s⁻¹ • (z - y) := by rw [smul_sub]; abel
    rw [this]
    ring
  have hc2 : ContDiff ℝ 2 (fun x => u (s⁻¹ • (x - y))) :=
    hu.comp ((contDiff_id.sub contDiff_const).const_smul s⁻¹)
  have hsmul : (fun x => c * u (s⁻¹ • (x - y))) = c • fun x => u (s⁻¹ • (x - y)) := by
    funext x
    simp
  rw [hsmul]
  simp only [coordinateLeviTrace]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviForm_smul hc2.contDiffAt, leviForm, leviForm, hR, hR]
  ring

/-- **The scaled Poisson identity**: `4 ∑_j ∂_j∂̄_j Ψ_s(· - y) = κ_s(· - y) - κ_{s/2}(· - y)`. -/
theorem four_mul_coordinateLeviTrace_scaledPotential (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    (y z : ComplexModel n) :
    4 * coordinateLeviTrace (scaledPotential s y) z =
      scaledKernel s y z - scaledKernel (s / 2) y z := by
  have hΨ2 : ContDiff ℝ 2 (unitPotential n) :=
    (unitPotential_contDiff hn).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  set d := Module.finrank ℝ (ComplexModel n) with hd
  have hfun : scaledPotential s y =
      fun x => (s ^ 2 * (s ^ d)⁻¹) * unitPotential n (s⁻¹ • (x - y)) := rfl
  rw [hfun, coordinateLeviTrace_scale hΨ2]
  have hT := four_mul_coordinateLeviTrace_explicitRadialPoissonPotential_eq_kernel_sub hn 1
    one_pos 0 1 (s⁻¹ • (z - y))
  have hk := explicitRadialKernel_scale (n := n) 1 one_pos 0 1 (s⁻¹ • (z - y))
  have h2 : (((1 : ℕ) : ℝ) + 1) / (((0 : ℕ) : ℝ) + 1) = 2 := by norm_num
  rw [h2] at hk
  have hhalf : (s / 2)⁻¹ • (z - y) = (2 : ℝ) • (s⁻¹ • (z - y)) := by
    rw [smul_smul]
    congr 1
    field_simp
  have hpow : ((s / 2) ^ d)⁻¹ = 2 ^ d * (s ^ d)⁻¹ := by
    rw [div_pow]
    field_simp
  simp only [scaledKernel, unitKernel, unitPotential] at *
  rw [hhalf, hpow]
  have hs0 : s ≠ 0 := hs.ne'
  calc 4 * (s ^ 2 * (s ^ d)⁻¹ * (s⁻¹ * s⁻¹) *
        coordinateLeviTrace (explicitRadialPoissonPotential 1 one_pos 0 1) (s⁻¹ • (z - y)))
      = (s ^ d)⁻¹ * (4 * coordinateLeviTrace (explicitRadialPoissonPotential 1 one_pos 0 1)
          (s⁻¹ • (z - y))) := by field_simp
    _ = _ := by rw [hT, hk]; ring

/-- The coordinate Levi trace of a difference. -/
theorem coordinateLeviTrace_sub {f g : ComplexModel n → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (z : ComplexModel n) :
    coordinateLeviTrace (fun x => f x - g x) z = coordinateLeviTrace f z - coordinateLeviTrace g z := by
  simp only [coordinateLeviTrace, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => leviForm_sub' hf.contDiffAt hg.contDiffAt _

/-! ### Kernel averages along dyadic scales -/

/-- The exact telescoping step: `A_{s/2}(y) = A_s(y) - 4 T(Ψ_s(· - y))`. -/
theorem integral_mul_scaledKernel_half (hn : 0 < n) {w : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hw : ContinuousOn w U) {s : ℝ} (hs : 0 < s)
    {y : ComplexModel n} (hyU : closedBall y s ⊆ U) :
    ∫ z, w z * scaledKernel (s / 2) y z =
      (∫ z, w z * scaledKernel s y z) -
        4 * ∫ z, w z * coordinateLeviTrace (scaledPotential s y) z := by
  have hs2 : 0 < s / 2 := half_pos hs
  have hK : ∀ t : ℝ, 0 < t → t ≤ s → Integrable (fun z => w z * scaledKernel t y z) := by
    intro t ht hts
    exact integrable_mul_of_continuousOn hU hw (scaledKernel_contDiff t y).continuous
      ((isCompact_closedBall y t).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_scaledKernel ht y))
      ((tsupport_scaledKernel ht y).trans ((closedBall_subset_closedBall hts).trans hyU))
  have hpt : ∀ z, w z * coordinateLeviTrace (scaledPotential s y) z =
      (w z * scaledKernel s y z - w z * scaledKernel (s / 2) y z) / 4 := by
    intro z
    have := four_mul_coordinateLeviTrace_scaledPotential hn hs y z
    rw [show coordinateLeviTrace (scaledPotential s y) z =
      (scaledKernel s y z - scaledKernel (s / 2) y z) / 4 by linarith]
    ring
  simp_rw [hpt]
  rw [integral_div, integral_sub (hK s hs le_rfl) (hK (s / 2) hs2 (half_le_self hs.le))]
  ring

/-- **Approximate identity along dyadic scales**: `A_{r 2^{-m}}(y) → w(y)`. -/
theorem tendsto_integral_mul_scaledKernel {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hw : ContinuousOn w U) {y : ComplexModel n} (hy : y ∈ U) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun m : ℕ => ∫ z, w z * scaledKernel (r / 2 ^ m) y z) atTop (𝓝 (w y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.mp hU y hy
  obtain ⟨δ₂, hδ₂, hδ₂w⟩ := Metric.continuousAt_iff.mp (hw.continuousAt (hU.mem_nhds hy))
    (ε / 2) (half_pos hε)
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ hδ₂
  have htend : Tendsto (fun m : ℕ => r / 2 ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul r |>.congr fun m => by rw [one_div, inv_pow, div_eq_mul_inv]
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp htend) (δ / 2) (half_pos hδ0)
  refine ⟨m₀, fun m hm => ?_⟩
  set s := r / 2 ^ m with hsdef
  have hs : 0 < s := by positivity
  have hsδ : s < δ := by
    have := hm₀ m hm
    rw [Real.dist_eq, sub_zero, abs_of_pos hs] at this
    linarith
  have hball : closedBall y s ⊆ ball y δ := closedBall_subset_ball hsδ
  have hballU : closedBall y s ⊆ U :=
    hball.trans ((ball_subset_ball (min_le_left _ _)).trans hδ₁U)
  have hint : Integrable (fun z => w z * scaledKernel s y z) :=
    integrable_mul_of_continuousOn hU hw (scaledKernel_contDiff s y).continuous
      ((isCompact_closedBall y s).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_scaledKernel hs y)) ((tsupport_scaledKernel hs y).trans hballU)
  have hkint : Integrable (scaledKernel s y) :=
    (scaledKernel_contDiff s y).continuous.integrable_of_hasCompactSupport
      ((isCompact_closedBall y s).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_scaledKernel hs y))
  have hdiff : (∫ z, w z * scaledKernel s y z) - w y =
      ∫ z, (w z - w y) * scaledKernel s y z := by
    have : ∫ z, (w z - w y) * scaledKernel s y z =
        (∫ z, w z * scaledKernel s y z) - ∫ z, w y * scaledKernel s y z := by
      rw [← integral_sub hint (hkint.const_mul (w y))]
      congr 1
      funext z
      ring
    rw [this, integral_const_mul, integral_scaledKernel hs y, mul_one]
  rw [Real.dist_eq, hdiff]
  have hle : ∀ z, |(w z - w y) * scaledKernel s y z| ≤ ε / 2 * scaledKernel s y z := by
    intro z
    rw [abs_mul, abs_of_nonneg (scaledKernel_nonneg s hs y z)]
    by_cases hz : z ∈ ball y δ
    · have hzw : dist (w z) (w y) < ε / 2 :=
        hδ₂w (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
      rw [Real.dist_eq] at hzw
      exact mul_le_mul_of_nonneg_right hzw.le (scaledKernel_nonneg s hs y z)
    · have h0 : scaledKernel s y z = 0 := by
        apply scaledKernel_eq_zero hs
        rw [← dist_eq_norm]
        by_contra h
        exact hz (hball (mem_closedBall.mpr (le_of_not_gt h)))
      rw [h0, mul_zero, mul_zero]
  calc |∫ z, (w z - w y) * scaledKernel s y z|
      ≤ ∫ z, |(w z - w y) * scaledKernel s y z| := abs_integral_le_integral_abs
    _ ≤ ∫ z, ε / 2 * scaledKernel s y z := integral_mono_of_nonneg
        (Eventually.of_forall fun z => abs_nonneg _) (hkint.const_mul _)
        (Eventually.of_forall hle)
    _ = ε / 2 := by rw [integral_const_mul, integral_scaledKernel hs y, mul_one]
    _ < ε := half_lt_self hε

/-- **Smooth functions**: if `u` is smooth on an open `U` and `|∑_j ∂_j∂̄_j u| ≤ M` on `U`, then
`|∫ u ∑_j ∂_j∂̄_j φ| ≤ M ∫ |φ|` for every test function `φ` supported in `U` (two integrations by
parts), so `exists_lipschitz_of_laplacian_bound` applies to `u`. -/
theorem abs_integral_mul_coordinateLeviTrace_le_of_contDiffOn {u : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U) {M : ℝ}
    (hM : ∀ z ∈ U, |coordinateLeviTrace u z| ≤ M) {φ : ComplexModel n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    |∫ z, u z * coordinateLeviTrace φ z| ≤ M * ∫ z, |φ z| := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hint : ∀ j : Fin n, Integrable (fun z => u z * leviForm φ z (coordinateVector j)) := by
    intro j
    have hc : Continuous (fun z => leviForm φ z (coordinateVector j)) :=
      ((continuous_realHessian hφ2 _ _).add (continuous_realHessian hφ2 _ _)).div_const _
    have hsub : Function.support (fun z => leviForm φ z (coordinateVector j)) ⊆ tsupport φ := by
      intro x hx
      by_contra hxs
      apply hx
      have h0 : iteratedFDeriv ℝ 2 φ x = 0 := by
        by_contra hne
        exact hxs (support_iteratedFDeriv_subset (𝕜 := ℝ) (n := 2) (f := φ) hne)
      simp [leviForm, realHessian, h0]
    exact integrable_mul_of_continuousOn hU hu.continuousOn hc (hφc.mono' hsub)
      ((closure_minimal hsub (isClosed_tsupport φ)).trans hφU)
  have hparts : ∫ z, u z * coordinateLeviTrace φ z = ∫ z, coordinateLeviTrace u z * φ z := by
    calc ∫ z, u z * coordinateLeviTrace φ z
        = ∑ j : Fin n, ∫ z, u z * leviForm φ z (coordinateVector j) := by
          rw [← integral_finsetSum _ fun j _ => hint j]
          congr 1
          funext z
          rw [coordinateLeviTrace, Finset.mul_sum]
      _ = ∑ j : Fin n, ∫ z, leviForm u z (coordinateVector j) * φ z := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact integral_mul_leviForm_eq hU hu hφ hφc hφU _
      _ = ∫ z, coordinateLeviTrace u z * φ z := by
          have hint' : ∀ j : Fin n, Integrable (fun z => leviForm u z (coordinateVector j) * φ z) := by
            intro j
            have hcu : ContinuousOn (fun z => leviForm u z (coordinateVector j)) U := by
              have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ u)) U :=
                (hu.fderiv_of_isOpen (m := ∞) hU (by simp)).fderiv_of_isOpen hU (by simp)
              simp only [leviForm, realHessian_eq_fderiv]
              exact (((h2.continuousOn.clm_apply continuousOn_const).clm_apply
                continuousOn_const).add ((h2.continuousOn.clm_apply continuousOn_const).clm_apply
                continuousOn_const)).div_const _
            exact integrable_mul_of_continuousOn hU hcu hφ.continuous hφc hφU
          rw [← integral_finsetSum _ fun j _ => hint' j]
          congr 1
          funext z
          rw [coordinateLeviTrace, Finset.sum_mul]
  rw [hparts, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun z => abs_nonneg _) ?_ (Eventually.of_forall fun z => ?_))
  · exact ((hφ.continuous.integrable_of_hasCompactSupport hφc).abs).const_mul M
  · show |coordinateLeviTrace u z * φ z| ≤ M * |φ z|
    rw [abs_mul]
    by_cases hz : z ∈ U
    · exact mul_le_mul_of_nonneg_right (hM z hz) (abs_nonneg _)
    · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
      simp [this]

/-! ### The Lipschitz estimate -/

/-- **Interior Lipschitz estimate for a bounded Laplacian.**  There is `C` (depending only on `n`)
such that if `w` is continuous on an open `U`, `|w| ≤ K` on `U` and
`|∫ w ∑_j ∂_j∂̄_j φ| ≤ M ∫ |φ|` for every test function `φ` supported in `U`, then
`|w(y) - w(y')| ≤ C (K / r + M r) ‖y - y'‖` whenever `B̄(y, r) ∪ B̄(y', r) ⊆ U`. -/
theorem exists_lipschitz_of_laplacian_bound (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ComplexModel n → ℝ) (U : Set (ComplexModel n)), IsOpen U →
      ContinuousOn w U → ∀ K M : ℝ, (∀ z ∈ U, |w z| ≤ K) →
      (∀ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        |∫ z, w z * coordinateLeviTrace φ z| ≤ M * ∫ z, |φ z|) →
      ∀ (y y' : ComplexModel n) (r : ℝ), 0 < r → closedBall y r ⊆ U → closedBall y' r ⊆ U →
        |w y - w y'| ≤ C * (K / r + M * r) * ‖y - y'‖ := by
  set d := Module.finrank ℝ (ComplexModel n) with hd
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_integral_abs_sub_le (unitKernel_contDiff (n := n).of_le
    (by norm_num)) fun x hx => unitKernel_eq_zero hx
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := exists_integral_abs_sub_le ((unitPotential_contDiff hn).of_le
    (by norm_num)) fun x hx => unitPotential_eq_zero hn hx
  refine ⟨Cκ + 8 * CΨ, by positivity, ?_⟩
  intro w U hU hw K M hK hM y y' r hr hyU hy'U
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK y (hyU (mem_closedBall_self hr.le)))
  have hM0 : 0 ≤ M := by
    -- test with a nonzero nonnegative function
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have hφ := hM (scaledKernel r y) (scaledKernel_contDiff r y)
      ((isCompact_closedBall y r).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_scaledKernel hr y)) ((tsupport_scaledKernel hr y).trans hyU)
    have hpos : 0 < ∫ z, |scaledKernel r y z| := by
      have : ∫ z, |scaledKernel r y z| = 1 := by
        simp_rw [abs_of_nonneg (scaledKernel_nonneg r hr y _)]
        exact integral_scaledKernel hr y
      rw [this]
      exact one_pos
    have := (abs_nonneg _).trans hφ
    nlinarith
  -- notation
  set s : ℕ → ℝ := fun m => r / 2 ^ m with hsdef
  have hs : ∀ m, 0 < s m := fun m => by positivity
  have hsr : ∀ m, s m ≤ r := fun m => div_le_self hr.le (one_le_pow₀ (by norm_num))
  have hs_succ : ∀ m, s (m + 1) = s m / 2 := fun m => by
    simp only [hsdef, pow_succ]
    field_simp
  set A : ℕ → ComplexModel n → ℝ := fun m x => ∫ z, w z * scaledKernel (s m) x z with hAdef
  set T : (ComplexModel n → ℝ) → ℝ := fun φ => ∫ z, w z * coordinateLeviTrace φ z with hTdef
  -- the potential differences as test functions
  have hdiffT : ∀ m, |T (scaledPotential (s m) y) - T (scaledPotential (s m) y')| ≤
      M * (CΨ * (s m) * ‖y - y'‖) := by
    intro m
    have hsm := hs m
    set φ : ComplexModel n → ℝ := fun z => scaledPotential (s m) y z - scaledPotential (s m) y' z
    have hφs : ContDiff ℝ ∞ φ :=
      (scaledPotential_contDiff hn (s m) y).sub (scaledPotential_contDiff hn (s m) y')
    have hφsupp : tsupport φ ⊆ closedBall y (s m) ∪ closedBall y' (s m) := by
      refine closure_minimal (fun z hz => ?_) (isClosed_closedBall.union isClosed_closedBall)
      by_contra h
      simp only [mem_union, mem_closedBall, dist_eq_norm, not_or, not_le] at h
      apply hz
      simp only [φ, scaledPotential_eq_zero hn hsm h.1, scaledPotential_eq_zero hn hsm h.2,
        sub_self]
    have hφU : tsupport φ ⊆ U := hφsupp.trans (union_subset
      ((closedBall_subset_closedBall (hsr m)).trans hyU)
      ((closedBall_subset_closedBall (hsr m)).trans hy'U))
    have hφc : HasCompactSupport φ :=
      ((isCompact_closedBall y _).union (isCompact_closedBall y' _)).of_isClosed_subset
        (isClosed_tsupport _) hφsupp
    have hlin : T φ = T (scaledPotential (s m) y) - T (scaledPotential (s m) y') := by
      have i₁ := integrable_mul_coordinateLeviTrace hU hw (scaledPotential_contDiff hn (s m) y)
        ((isCompact_closedBall y _).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_scaledPotential hn hsm y))
        ((tsupport_scaledPotential hn hsm y).trans
          ((closedBall_subset_closedBall (hsr m)).trans hyU))
      have i₂ := integrable_mul_coordinateLeviTrace hU hw (scaledPotential_contDiff hn (s m) y')
        ((isCompact_closedBall y' _).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_scaledPotential hn hsm y'))
        ((tsupport_scaledPotential hn hsm y').trans
          ((closedBall_subset_closedBall (hsr m)).trans hy'U))
      simp only [hTdef]
      rw [← integral_sub i₁ i₂]
      congr 1
      funext z
      have h2 : ContDiff ℝ 2 (scaledPotential (s m) y) :=
        (scaledPotential_contDiff hn (s m) y).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      have h2' : ContDiff ℝ 2 (scaledPotential (s m) y') :=
        (scaledPotential_contDiff hn (s m) y').of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
      rw [coordinateLeviTrace_sub h2 h2']
      ring
    have hb := hM φ hφs hφc hφU
    have hL1 : ∫ z, |φ z| ≤ CΨ * s m * ‖y - y'‖ := by
      have hscaled := integral_abs_sub_scaled_le hCΨ hsm y y'
      have hφeq : ∀ z, |φ z| = (s m ^ 2 * (s m ^ d)⁻¹) *
          |unitPotential n ((s m)⁻¹ • (z - y)) - unitPotential n ((s m)⁻¹ • (z - y'))| := by
        intro z
        simp only [φ, scaledPotential]
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      simp_rw [hφeq]
      rw [integral_const_mul]
      calc s m ^ 2 * (s m ^ d)⁻¹ *
            ∫ z, |unitPotential n ((s m)⁻¹ • (z - y)) - unitPotential n ((s m)⁻¹ • (z - y'))|
          ≤ s m ^ 2 * (s m ^ d)⁻¹ * (s m ^ d * (CΨ * (‖y - y'‖ / s m))) :=
            mul_le_mul_of_nonneg_left hscaled (by positivity)
        _ = CΨ * s m * ‖y - y'‖ := by
            field_simp
    rw [← hlin]
    calc |T φ| ≤ M * ∫ z, |φ z| := hb
      _ ≤ M * (CΨ * s m * ‖y - y'‖) := mul_le_mul_of_nonneg_left hL1 hM0
  -- the base difference
  have hbase : |A 0 y - A 0 y'| ≤ Cκ * (K / r) * ‖y - y'‖ := by
    have h0 : s 0 = r := by simp [hsdef]
    simp only [hAdef, h0]
    have i₁ : Integrable (fun z => w z * scaledKernel r y z) :=
      integrable_mul_of_continuousOn hU hw (scaledKernel_contDiff r y).continuous
        ((isCompact_closedBall y r).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_scaledKernel hr y)) ((tsupport_scaledKernel hr y).trans hyU)
    have i₂ : Integrable (fun z => w z * scaledKernel r y' z) :=
      integrable_mul_of_continuousOn hU hw (scaledKernel_contDiff r y').continuous
        ((isCompact_closedBall y' r).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_scaledKernel hr y')) ((tsupport_scaledKernel hr y').trans hy'U)
    rw [← integral_sub i₁ i₂]
    have hle : ∀ z, |w z * scaledKernel r y z - w z * scaledKernel r y' z| ≤
        K * ((r ^ d)⁻¹ *
          |unitKernel n (r⁻¹ • (z - y)) - unitKernel n (r⁻¹ • (z - y'))|) := by
      intro z
      rw [← mul_sub, abs_mul]
      by_cases hz : z ∈ U
      · refine mul_le_mul (hK z hz) ?_ (abs_nonneg _) hK0
        simp only [scaledKernel]
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      · have hzy : scaledKernel r y z = 0 := by
          apply scaledKernel_eq_zero hr
          rw [← dist_eq_norm]
          by_contra h
          exact hz (hyU (mem_closedBall.mpr (le_of_not_gt h)))
        have hzy' : scaledKernel r y' z = 0 := by
          apply scaledKernel_eq_zero hr
          rw [← dist_eq_norm]
          by_contra h
          exact hz (hy'U (mem_closedBall.mpr (le_of_not_gt h)))
        rw [hzy, hzy', sub_self, abs_zero, mul_zero]
        positivity
    have hintR : Integrable (fun z => K * ((r ^ d)⁻¹ *
        |unitKernel n (r⁻¹ • (z - y)) - unitKernel n (r⁻¹ • (z - y'))|)) := by
      refine Integrable.const_mul (Integrable.const_mul ?_ _) _
      have hc : Continuous (fun z => unitKernel n (r⁻¹ • (z - y))) :=
        unitKernel_contDiff.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
      have hc' : Continuous (fun z => unitKernel n (r⁻¹ • (z - y'))) :=
        unitKernel_contDiff.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
      have hcs : HasCompactSupport (fun z => unitKernel n (r⁻¹ • (z - y))) := by
        have := (isCompact_closedBall y r).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_scaledKernel hr y)
        refine HasCompactSupport.intro (isCompact_closedBall y r) fun z hz => ?_
        apply unitKernel_eq_zero
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div, lt_div_iff₀ hr,
          one_mul]
        exact hz
      have hcs' : HasCompactSupport (fun z => unitKernel n (r⁻¹ • (z - y'))) := by
        refine HasCompactSupport.intro (isCompact_closedBall y' r) fun z hz => ?_
        apply unitKernel_eq_zero
        rw [mem_closedBall, dist_eq_norm, not_le] at hz
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_eq_div, lt_div_iff₀ hr,
          one_mul]
        exact hz
      exact ((hc.integrable_of_hasCompactSupport hcs).sub
        (hc'.integrable_of_hasCompactSupport hcs')).abs
    calc |∫ z, (w z * scaledKernel r y z - w z * scaledKernel r y' z)|
        ≤ ∫ z, |w z * scaledKernel r y z - w z * scaledKernel r y' z| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, K * ((r ^ d)⁻¹ *
            |unitKernel n (r⁻¹ • (z - y)) - unitKernel n (r⁻¹ • (z - y'))|) :=
          integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hintR
            (Eventually.of_forall hle)
      _ = K * ((r ^ d)⁻¹ *
            ∫ z, |unitKernel n (r⁻¹ • (z - y)) - unitKernel n (r⁻¹ • (z - y'))|) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ K * ((r ^ d)⁻¹ * (r ^ d * (Cκ * (‖y - y'‖ / r)))) := by
          gcongr
          exact integral_abs_sub_scaled_le hCκ hr y y'
      _ = Cκ * (K / r) * ‖y - y'‖ := by
          field_simp
  -- the induction along the dyadic scales
  have hstep : ∀ m, A (m + 1) y - A (m + 1) y' =
      (A m y - A m y') - 4 * (T (scaledPotential (s m) y) - T (scaledPotential (s m) y')) := by
    intro m
    have e₁ := integral_mul_scaledKernel_half hn hU hw (hs m)
      ((closedBall_subset_closedBall (hsr m)).trans hyU)
    have e₂ := integral_mul_scaledKernel_half hn hU hw (hs m)
      ((closedBall_subset_closedBall (hsr m)).trans hy'U)
    simp only [hAdef, hTdef, hs_succ m]
    rw [e₁, e₂]
    ring
  have hind : ∀ m, |A m y - A m y'| ≤ Cκ * (K / r) * ‖y - y'‖ +
      4 * M * CΨ * ‖y - y'‖ * ∑ k ∈ Finset.range m, s k := by
    intro m
    induction m with
    | zero => simpa using hbase
    | succ m ih =>
      rw [hstep m, Finset.sum_range_succ]
      calc |A m y - A m y' - 4 * (T (scaledPotential (s m) y) - T (scaledPotential (s m) y'))|
          ≤ |A m y - A m y'| + 4 * |T (scaledPotential (s m) y) - T (scaledPotential (s m) y')| := by
            refine (abs_sub _ _).trans ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        _ ≤ (Cκ * (K / r) * ‖y - y'‖ + 4 * M * CΨ * ‖y - y'‖ * ∑ k ∈ Finset.range m, s k) +
              4 * (M * (CΨ * s m * ‖y - y'‖)) := add_le_add ih (by linarith [hdiffT m])
        _ = _ := by ring
  have hsum : ∀ m, ∑ k ∈ Finset.range m, s k ≤ 2 * r := by
    intro m
    have hgeom : ∑ k ∈ Finset.range m, s k = r * ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hsdef, div_eq_mul_inv]
    rw [hgeom]
    have : ∑ k ∈ Finset.range m, (1 / 2 : ℝ) ^ k ≤ 2 := by
      have := sum_geometric_two_le m
      simpa using this
    nlinarith
  have hbound : ∀ m, |A m y - A m y'| ≤
      Cκ * (K / r) * ‖y - y'‖ + 8 * M * CΨ * r * ‖y - y'‖ := by
    intro m
    have h1 := hind m
    have h2 : 4 * M * CΨ * ‖y - y'‖ * ∑ k ∈ Finset.range m, s k ≤
        4 * M * CΨ * ‖y - y'‖ * (2 * r) :=
      mul_le_mul_of_nonneg_left (hsum m) (by positivity)
    linarith
  -- passing to the limit
  have hlim : Tendsto (fun m => A m y - A m y') atTop (𝓝 (w y - w y')) :=
    (tendsto_integral_mul_scaledKernel hU hw (hyU (mem_closedBall_self hr.le)) hr).sub
      (tendsto_integral_mul_scaledKernel hU hw (hy'U (mem_closedBall_self hr.le)) hr)
  have hfinal : |w y - w y'| ≤ Cκ * (K / r) * ‖y - y'‖ + 8 * M * CΨ * r * ‖y - y'‖ :=
    le_of_tendsto (hlim.abs) (Eventually.of_forall hbound)
  calc |w y - w y'| ≤ Cκ * (K / r) * ‖y - y'‖ + 8 * M * CΨ * r * ‖y - y'‖ := hfinal
    _ ≤ (Cκ + 8 * CΨ) * (K / r + M * r) * ‖y - y'‖ := by
        have h1 : 0 ≤ K / r := by positivity
        have h2 : 0 ≤ M * r := by positivity
        have hn' : 0 ≤ ‖y - y'‖ := norm_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hCκ0 h2) hn', mul_nonneg (mul_nonneg hCΨ0 h1) hn']

end SGPT.Analysis.CZ
