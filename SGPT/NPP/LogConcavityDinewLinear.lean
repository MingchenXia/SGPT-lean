import SGPT.NPP.LogConcavityDinewUpperTest
import SGPT.Foundations.Analysis.Pending.BedfordTaylorExistence

/-!
# Linear elliptic inequalities for Monge–Ampère subsolutions

FPT `prop:bounded-monge-ampere-linear-density`, (1) ⇒ (3): let `u` be a locally bounded
plurisubharmonic function on `Ω ⊆ ℂⁿ` with `(ddᶜu)ⁿ ≥ c · (n!/πⁿ) dV`, `c > 0`. For every complex
frame `Y` with `|det Y| = 1`, the operator `L_Y χ = ∑ₖ leviForm χ · (frameMap Y eₖ)` satisfies
`∫ u · L_Y χ ≥ n c^{1/n} ∫ χ` for nonnegative `C²` functions `χ` supported in a ball `B(x₀, R/2)` with
`B̄(x₀, R) ⊆ Ω` (`integral_mul_frameLevi_ge`).

Proof: extend `u` from the ball by `max(u, ψ)` with a large quadratic `ψ` (`ballExtension`), so that
the extension is plurisubharmonic on `ℂⁿ` and a viscosity subsolution along the frame; compose with
`frameMap Y` (which turns `L_Y` into the standard `L`), apply the heat-flow argument
(`integral_mul_leviSum_ge_of_psh`) and change variables back.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Matrix
open scoped Topology ComplexOrder ContDiff
open TopologicalSpace

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.MongeAmpere

variable {n : ℕ}

/-! ### Frames as linear isomorphisms -/

theorem frameMap_inv_apply {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det) (z : ComplexModel n) :
    frameMap Y⁻¹ (frameMap Y z) = z := by
  rw [frameMap_mul, Matrix.nonsing_inv_mul _ hY, frameMap_one]

theorem frameMap_apply_inv {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det) (z : ComplexModel n) :
    frameMap Y (frameMap Y⁻¹ z) = z := by
  rw [frameMap_mul, Matrix.mul_nonsing_inv _ hY, frameMap_one]

theorem isUnit_det_of_norm {Y : Matrix (Fin n) (Fin n) ℂ} (hY : ‖Y.det‖ = 1) : IsUnit Y.det :=
  isUnit_iff_ne_zero.mpr (norm_ne_zero_iff.mp (by rw [hY]; norm_num))

/-- The frame as a homeomorphism. -/
def frameHomeomorph {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det) :
    ComplexModel n ≃ₜ ComplexModel n where
  toFun := frameMap Y
  invFun := frameMap Y⁻¹
  left_inv := frameMap_inv_apply hY
  right_inv := frameMap_apply_inv hY
  continuous_toFun := (frameMap Y).continuous
  continuous_invFun := (frameMap Y⁻¹).continuous

/-- **Change of variables** along a frame. -/
theorem exists_integral_comp_frameMap {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ComplexModel n → ℝ, ∫ z, f (frameMap Y z) = c * ∫ y, f y := by
  set T : ComplexModel n →ₗ[ℝ] ComplexModel n :=
    ((frameMap Y).restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n).toLinearMap with hT
  set S : ComplexModel n →ₗ[ℝ] ComplexModel n :=
    ((frameMap Y⁻¹).restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n).toLinearMap with hS
  have hTS : T.comp S = LinearMap.id := by
    ext z; simp [hT, hS, frameMap_apply_inv hY]
  have hdet : LinearMap.det T ≠ 0 := by
    intro h
    have := congrArg LinearMap.det hTS
    rw [LinearMap.det_comp, h, zero_mul, LinearMap.det_id] at this
    exact zero_ne_one this
  refine ⟨|(LinearMap.det T)⁻¹|, abs_pos.mpr (inv_ne_zero hdet), fun f => ?_⟩
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (ComplexModel n)) hdet
  have hemb : MeasurableEmbedding (frameMap Y) := (frameHomeomorph hY).measurableEmbedding
  have := hemb.integral_map (μ := volume) f
  have hTf : (T : ComplexModel n → ComplexModel n) = frameMap Y := by
    funext z; simp [hT]
  rw [hTf] at hmap
  rw [← this, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]

theorem frameMap_I_smul (Y : Matrix (Fin n) (Fin n) ℂ) (v : ComplexModel n) :
    frameMap Y (Complex.I • v) = Complex.I • frameMap Y v := map_smul _ _ _

theorem leviForm_comp_frameMap {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (z v : ComplexModel n) :
    leviForm (fun y => χ (frameMap Y y)) z v = leviForm χ (frameMap Y z) (frameMap Y v) := by
  have h := fun a b => realHessian_comp_affine hχ
    ((frameMap Y).restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel n) 0 z a b
  simp only [zero_add, ContinuousLinearMap.coe_restrictScalars'] at h
  simp only [leviForm, h, frameMap_I_smul]

/-- The frame operator `L_Y`. -/
def frameLevi (Y : Matrix (Fin n) (Fin n) ℂ) (χ : ComplexModel n → ℝ) (y : ComplexModel n) : ℝ :=
  ∑ k, leviForm χ y (frameMap Y (coordinateVector k))

theorem leviSum_comp_frameMap {χ : ComplexModel n → ℝ} (hχ : ContDiff ℝ 2 χ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (z : ComplexModel n) :
    leviSum (fun y => χ (frameMap Y y)) z = frameLevi Y χ (frameMap Y z) := by
  simp only [leviSum, frameLevi, leviForm_comp_frameMap hχ]

/-! ### Transport of upper tests -/

theorem isQuadraticUpperTest_comp_frameMap {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det)
    {g : ComplexModel n → ℝ} {z : ComplexModel n} {ℓ : ComplexModel n →L[ℝ] ℝ}
    {M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (h : IsQuadraticUpperTest (fun y => g (frameMap Y y)) z ℓ M) :
    IsQuadraticUpperTest g (frameMap Y z)
      (ℓ.comp ((frameMap Y⁻¹).restrictScalars ℝ))
      (M.bilinearComp ((frameMap Y⁻¹).restrictScalars ℝ) ((frameMap Y⁻¹).restrictScalars ℝ)) := by
  have hc : Tendsto (frameMap Y⁻¹) (𝓝 (frameMap Y z)) (𝓝 z) := by
    have := (frameMap Y⁻¹).continuous.tendsto (frameMap Y z)
    rwa [frameMap_inv_apply hY] at this
  filter_upwards [hc.eventually h] with w hw
  have e1 : frameMap Y (frameMap Y⁻¹ w) = w := frameMap_apply_inv hY w
  have e2 : frameMap Y⁻¹ w - z = frameMap Y⁻¹ (w - frameMap Y z) := by
    rw [map_sub, frameMap_inv_apply hY]
  simp only [e1] at hw
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [← e2]
  exact hw

/-- The trace of a transported quadratic part along the frame. -/
theorem stdTrace_eq_sum_leviFormOfBilin {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsUnit Y.det)
    (M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) :
    stdTrace M / 2 = ∑ k, leviFormOfBilin
      (M.bilinearComp ((frameMap Y⁻¹).restrictScalars ℝ) ((frameMap Y⁻¹).restrictScalars ℝ) +
        (M.bilinearComp ((frameMap Y⁻¹).restrictScalars ℝ)
          ((frameMap Y⁻¹).restrictScalars ℝ)).flip) (frameMap Y (coordinateVector k)) := by
  simp only [stdTrace, leviFormOfBilin, _root_.add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, frameMap_inv_apply hY,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The ball extension -/

section Extension

variable (x₀ : ComplexModel n) (R A Mu : ℝ) (u : ComplexModel n → ℝ)

/-- The quadratic barrier. -/
def barrier (y : ComplexModel n) : ℝ := A * ‖y - x₀‖ ^ 2 - (A * R ^ 2 / 4 + Mu + 1)

/-- `max(u, ψ)` on `B(x₀, R)`, `ψ` outside. -/
def ballExtension (y : ComplexModel n) : ℝ :=
  if ‖y - x₀‖ < R then max (u y) (barrier x₀ R A Mu y) else barrier x₀ R A Mu y

variable {x₀ R A Mu u}

theorem barrier_le_ballExtension (y : ComplexModel n) :
    barrier x₀ R A Mu y ≤ ballExtension x₀ R A Mu u y := by
  unfold ballExtension; split_ifs <;> simp

theorem le_ballExtension {y : ComplexModel n} (hy : ‖y - x₀‖ < R) :
    u y ≤ ballExtension x₀ R A Mu u y := by
  unfold ballExtension; rw [if_pos hy]; exact le_max_left _ _

theorem ballExtension_eq_of_lt_half (hR : 0 < R) (hMu : ∀ y, ‖y - x₀‖ ≤ R → |u y| ≤ Mu)
    (hA : 0 ≤ A) {y : ComplexModel n} (hy : ‖y - x₀‖ < R / 2) :
    ballExtension x₀ R A Mu u y = u y := by
  have hyR : ‖y - x₀‖ < R := hy.trans (by linarith)
  unfold ballExtension
  rw [if_pos hyR, max_eq_left]
  have h1 := (abs_le.mp (hMu y hyR.le)).1
  have h2 : ‖y - x₀‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy.le 2
  unfold barrier
  nlinarith [mul_le_mul_of_nonneg_left h2 hA]

theorem ballExtension_eq_barrier (hR : 0 < R) (hMu : ∀ y, ‖y - x₀‖ ≤ R → |u y| ≤ Mu)
    (hA : 16 * (2 * Mu + 1) / (5 * R ^ 2) < A) {y : ComplexModel n} (hy : 3 * R / 4 < ‖y - x₀‖) :
    ballExtension x₀ R A Mu u y = barrier x₀ R A Mu y := by
  unfold ballExtension
  split_ifs with hyR
  · rw [max_eq_right]
    have h1 := (abs_le.mp (hMu y hyR.le)).2
    have h2 : (3 * R / 4) ^ 2 ≤ ‖y - x₀‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy.le 2
    have hA' : 16 * (2 * Mu + 1) < A * (5 * R ^ 2) := by
      rwa [div_lt_iff₀ (by positivity)] at hA
    have hA0 : 0 < A := by
      have : 0 ≤ Mu := (abs_nonneg _).trans (hMu x₀ (by simp; linarith))
      have : 0 < 16 * (2 * Mu + 1) := by linarith
      nlinarith [sq_nonneg R]
    unfold barrier
    nlinarith [mul_le_mul_of_nonneg_left h2 hA0.le]
  · rfl

theorem contDiff_barrier : ContDiff ℝ ∞ (barrier x₀ R A Mu) := by
  unfold barrier
  exact (contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).sub
    contDiff_const

theorem leviForm_barrier (y v : ComplexModel n) : leviForm (barrier x₀ R A Mu) y v = A * ‖v‖ ^ 2 := by
  have h : ∀ a b : ComplexModel n, realHessian (barrier x₀ R A Mu) y a b = A * (2 * inner ℝ a b) := by
    intro a b
    have e : barrier x₀ R A Mu = (fun y => A * (fun w : ComplexModel n => ‖w‖ ^ 2)
        (-x₀ + (ContinuousLinearMap.id ℝ (ComplexModel n)) y)) + fun _ => -(A * R ^ 2 / 4 + Mu + 1) := by
      funext w; simp [barrier, sub_eq_add_neg, add_comm]
    have h2 : ContDiff ℝ 2 fun y : ComplexModel n => (fun w : ComplexModel n => ‖w‖ ^ 2)
        (-x₀ + (ContinuousLinearMap.id ℝ (ComplexModel n)) y) :=
      (contDiff_norm_sq ℝ).comp (contDiff_const.add (ContinuousLinearMap.id ℝ _).contDiff)
    rw [e, realHessian_add (contDiff_const.mul h2).contDiffAt contDiffAt_const, realHessian_const,
      add_zero]
    have := realHessian_comp_affine (contDiff_norm_sq ℝ) (ContinuousLinearMap.id ℝ (ComplexModel n))
      (-x₀) y a b
    rw [realHessian_const_mul h2, this, realHessian_norm_sq]
    rfl
  simp only [leviForm, h, real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  ring

theorem plurisubharmonicOn_barrier (hA : 0 ≤ A) :
    PlurisubharmonicOn (fun y => (barrier x₀ R A Mu y : EReal)) univ :=
  plurisubharmonicOn_of_levi_nonneg (contDiff_barrier.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) isOpen_univ fun y _ v => by
      rw [leviForm_barrier]; positivity

theorem plurisubharmonicOn_ballExtension (hR : 0 < R) (hMu : ∀ y, ‖y - x₀‖ ≤ R → |u y| ≤ Mu)
    (hA : 16 * (2 * Mu + 1) / (5 * R ^ 2) < A) (hA0 : 0 ≤ A)
    (hu : PlurisubharmonicOn (fun y => (u y : EReal)) (Metric.ball x₀ R)) :
    PlurisubharmonicOn (fun y => (ballExtension x₀ R A Mu u y : EReal)) univ := by
  intro x _
  have hψ := plurisubharmonicOn_barrier (x₀ := x₀) (R := R) (Mu := Mu) hA0 x (mem_univ x)
  by_cases hx : ‖x - x₀‖ < R
  · have hxb : x ∈ Metric.ball x₀ R := by rwa [Metric.mem_ball, dist_eq_norm]
    obtain ⟨U, hU, hxU, hUu⟩ := hu x hxb
    obtain ⟨V, hV, hxV, hVψ⟩ := hψ
    have hmax : PlurisubharmonicAt (fun y => max (u y : EReal) (barrier x₀ R A Mu y : EReal)) x :=
      ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, (hUu.mono inter_subset_left).max (hVψ.mono inter_subset_right)⟩
    refine hmax.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hxb] with y hy
    have hy' : ‖y - x₀‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hy
    simp only [ballExtension, if_pos hy']
    exact (EReal.coe_strictMono.monotone.map_max).symm
  · push Not at hx
    refine hψ.congr ?_
    have hopen : IsOpen {y : ComplexModel n | 3 * R / 4 < ‖y - x₀‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    filter_upwards [hopen.mem_nhds (show 3 * R / 4 < ‖x - x₀‖ by linarith)] with y hy
    rw [ballExtension_eq_barrier hR hMu hA hy]

theorem abs_ballExtension_le (hMu : ∀ y, ‖y - x₀‖ ≤ R → |u y| ≤ Mu) (hA0 : 0 ≤ A) (hMu0 : 0 ≤ Mu)
    (y : ComplexModel n) :
    |ballExtension x₀ R A Mu u y| ≤
      (2 * A * (1 + ‖x₀‖ ^ 2) + A * R ^ 2 / 4 + 2 * Mu + 1) * (1 + ‖y‖ ^ 2) := by
  have hψ : |barrier x₀ R A Mu y| ≤ 2 * A * (‖y‖ ^ 2 + ‖x₀‖ ^ 2) + (A * R ^ 2 / 4 + Mu + 1) := by
    unfold barrier
    have h1 : ‖y - x₀‖ ^ 2 ≤ 2 * (‖y‖ ^ 2 + ‖x₀‖ ^ 2) := by
      have := norm_sub_le y x₀
      nlinarith [sq_nonneg (‖y‖ - ‖x₀‖), norm_nonneg (y - x₀), norm_nonneg y, norm_nonneg x₀]
    have h2 : 0 ≤ A * ‖y - x₀‖ ^ 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hA0, sq_nonneg R]
  have hbound : |ballExtension x₀ R A Mu u y| ≤
      Mu + 2 * A * (‖y‖ ^ 2 + ‖x₀‖ ^ 2) + (A * R ^ 2 / 4 + Mu + 1) := by
    unfold ballExtension
    split_ifs with hy
    · have h1 := hMu y hy.le
      rw [abs_le] at h1 hψ ⊢
      constructor
      · have := le_max_right (u y) (barrier x₀ R A Mu y)
        linarith
      · rcases le_total (u y) (barrier x₀ R A Mu y) with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith
    · linarith
  refine hbound.trans ?_
  nlinarith [sq_nonneg ‖y‖, sq_nonneg ‖x₀‖, mul_nonneg (sq_nonneg ‖y‖) (sq_nonneg ‖x₀‖),
    mul_nonneg hA0 (mul_nonneg (sq_nonneg ‖y‖) (sq_nonneg ‖x₀‖)), mul_nonneg hA0 (sq_nonneg R),
    mul_nonneg (mul_nonneg hA0 (sq_nonneg R)) (sq_nonneg ‖y‖), mul_nonneg hMu0 (sq_nonneg ‖y‖)]

end Extension

/-! ### The viscosity property along a frame -/

theorem le_of_upperTest_barrier {x₀ : ComplexModel n} {R A Mu : ℝ} {y : ComplexModel n}
    {ℓ : ComplexModel n →L[ℝ] ℝ} {M : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (h : ∀ᶠ w in 𝓝 y, barrier x₀ R A Mu w ≤ barrier x₀ R A Mu y + ℓ (w - y) + M (w - y) (w - y))
    (v : ComplexModel n) : A * ‖v‖ ^ 2 ≤ M v v := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  set s : ℝ := ε / (2 * (‖v‖ + 1)) with hs
  have hs0 : 0 < s := by positivity
  have hsv : s * ‖v‖ < ε := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have key : ∀ σ : ℝ, |σ| = s → barrier x₀ R A Mu (y + σ • v) ≤
      barrier x₀ R A Mu y + ℓ (σ • v) + M (σ • v) (σ • v) := by
    intro σ hσ
    have := hball (y := y + σ • v) (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hσ]; exact hsv)
    simpa only [add_sub_cancel_left] using this
  have h1 := key s (abs_of_pos hs0)
  have h2 := key (-s) (by rw [abs_neg, abs_of_pos hs0])
  have e : ∀ σ : ℝ, barrier x₀ R A Mu (y + σ • v) - barrier x₀ R A Mu y =
      A * (2 * σ * inner ℝ (y - x₀) v + σ ^ 2 * ‖v‖ ^ 2) := by
    intro σ
    unfold barrier
    have : y + σ • v - x₀ = (y - x₀) + σ • v := by abel
    rw [this, norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  have e1 := e s
  have e2 := e (-s)
  simp only [map_smul, _root_.smul_apply, smul_eq_mul] at h1 h2
  have hs2 : 0 < s ^ 2 := by positivity
  have : 2 * s ^ 2 * (A * ‖v‖ ^ 2) ≤ 2 * s ^ 2 * M v v := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- **The viscosity property of the extension along a frame.** -/
theorem isViscositySub_ballExtension_frame (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c)
    (hμ : ENNReal.ofReal (mongeAmpereConst n * c) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    {x₀ : ComplexModel n} {R A Mu : ℝ} (hball : Metric.closedBall x₀ R ⊆ Ω)
    (hAc : c ^ ((n : ℝ)⁻¹) ≤ A) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : ‖Y.det‖ = 1) :
    IsViscositySub (fun z => ballExtension x₀ R A Mu u (frameMap Y z)) (n * c ^ ((n : ℝ)⁻¹)) := by
  intro z ℓ M htest
  have hU := isUnit_det_of_norm hY
  set S : ComplexModel n →L[ℝ] ComplexModel n := (frameMap Y⁻¹).restrictScalars ℝ with hS
  set M' := M.bilinearComp S S with hM'
  set y := frameMap Y z with hy
  have htest' := isQuadraticUpperTest_comp_frameMap hU htest
  rw [stdTrace_eq_sum_leviFormOfBilin hU M]
  by_cases hcase : ‖y - x₀‖ < R ∧ barrier x₀ R A Mu y ≤ u y
  · -- the potential is active
    have hyx : ballExtension x₀ R A Mu u y = u y := by
      unfold ballExtension; rw [if_pos hcase.1, max_eq_left hcase.2]
    have hyΩ : y ∈ Ω := hball (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hcase.1.le)
    have htu : IsQuadraticUpperTest u y (ℓ.comp S) M' := by
      have hopen : IsOpen {w : ComplexModel n | ‖w - x₀‖ < R} :=
        isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
      filter_upwards [htest', hopen.mem_nhds hcase.1] with w hw hwR
      rw [← hyx]
      exact (le_ballExtension hwR).trans hw
    obtain ⟨hpsd, hdet⟩ := upperTest_det_ge hn hu hc hμ hyΩ htu
    rw [sum_leviFormOfBilin_frameMap (symm_add_flip M') Y]
    refine le_trans ?_ (mul_rpow_det_le_trace_frame hn hpsd hY)
    gcongr
  · -- the barrier is active
    have hyx : ballExtension x₀ R A Mu u y = barrier x₀ R A Mu y := by
      unfold ballExtension
      split_ifs with h1
      · push Not at hcase
        exact max_eq_right (hcase h1).le
      · rfl
    have htb : ∀ᶠ w in 𝓝 y, barrier x₀ R A Mu w ≤
        barrier x₀ R A Mu y + (ℓ.comp S) (w - y) + M' (w - y) (w - y) := by
      filter_upwards [htest'] with w hw
      rw [← hyx]
      exact (barrier_le_ballExtension w).trans hw
    have hlow := le_of_upperTest_barrier htb
    have hsum : A * ∑ k, ‖frameMap Y (coordinateVector k)‖ ^ 2 ≤
        ∑ k, leviFormOfBilin (M' + M'.flip) (frameMap Y (coordinateVector k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h1 := hlow (frameMap Y (coordinateVector k))
      have h2 := hlow (Complex.I • frameMap Y (coordinateVector k))
      rw [norm_smul, Complex.norm_I, one_mul] at h2
      simp only [leviFormOfBilin, _root_.add_apply, ContinuousLinearMap.flip_apply]
      linarith
    have hn' := le_sum_norm_frameMap_sq hn hY
    have hA0 : 0 ≤ A := (Real.rpow_nonneg hc.le _).trans hAc
    calc (n : ℝ) * c ^ ((n : ℝ)⁻¹) ≤ n * A := by gcongr
      _ = A * n := by ring
      _ ≤ A * ∑ k, ‖frameMap Y (coordinateVector k)‖ ^ 2 := by gcongr
      _ ≤ _ := hsum

/-- **The linear inequality along a frame** (FPT `prop:bounded-monge-ampere-linear-density`,
(1) ⇒ (3)): `∫ u · L_Y χ ≥ n c^{1/n} ∫ χ` for nonnegative `C²` functions `χ` supported in
`B(x₀, R/2)`, `B̄(x₀, R) ⊆ Ω`, `|det Y| = 1`. -/
theorem integral_mul_frameLevi_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {c : ℝ} (hc : 0 < c)
    (hμ : ENNReal.ofReal (mongeAmpereConst n * c) • volume.restrict (Ω : Set (ComplexModel n)) ≤
      canonicalBedfordTaylorMeasure Ω u hu)
    {x₀ : ComplexModel n} {R : ℝ} (hR : 0 < R) (hball : Metric.closedBall x₀ R ⊆ Ω)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : ‖Y.det‖ = 1) {χ : ComplexModel n → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Metric.ball x₀ (R / 2)) :
    n * c ^ ((n : ℝ)⁻¹) * ∫ x, χ x ≤ ∫ x, u x * frameLevi Y χ x := by
  have hU := isUnit_det_of_norm hY
  obtain ⟨Mu₀, hMu₀⟩ := BedfordTaylor.IsLocallyBoundedPshOn.exists_abs_le hu
    (isCompact_closedBall x₀ R) hball
  set Mu : ℝ := max Mu₀ 0 with hMudef
  have hMu0 : 0 ≤ Mu := le_max_right _ _
  have hMu : ∀ y, ‖y - x₀‖ ≤ R → |u y| ≤ Mu := fun y hy =>
    (hMu₀ y (by rwa [Metric.mem_closedBall, dist_eq_norm])).trans (le_max_left _ _)
  set A : ℝ := max (c ^ ((n : ℝ)⁻¹)) (16 * (2 * Mu + 1) / (5 * R ^ 2) + 1) with hAdef
  have hAc : c ^ ((n : ℝ)⁻¹) ≤ A := le_max_left _ _
  have hA : 16 * (2 * Mu + 1) / (5 * R ^ 2) < A := by
    have := le_max_right (c ^ ((n : ℝ)⁻¹)) (16 * (2 * Mu + 1) / (5 * R ^ 2) + 1)
    linarith
  have hA0 : 0 ≤ A := (Real.rpow_nonneg hc.le _).trans hAc
  set ue := ballExtension x₀ R A Mu u with hue
  set v : ComplexModel n → ℝ := fun z => ue (frameMap Y z) with hv
  have hupsh : PlurisubharmonicOn (fun y => (u y : EReal)) (Metric.ball x₀ R) :=
    hu.1.mono (Metric.ball_subset_closedBall.trans hball)
  have hvpsh : PlurisubharmonicOn (fun z => (v z : EReal)) univ := by
    have := (plurisubharmonicOn_ballExtension hR hMu hA hA0 hupsh).comp_continuousLinearMap
      (frameMap Y)
    simpa using this
  set Cg : ℝ := 2 * A * (1 + ‖x₀‖ ^ 2) + A * R ^ 2 / 4 + 2 * Mu + 1 with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  have hvC : ∀ z, |v z| ≤ (Cg * (1 + ‖frameMap Y‖ ^ 2)) * (1 + ‖z‖ ^ 2) := by
    intro z
    refine (abs_ballExtension_le hMu hA0 hMu0 (frameMap Y z)).trans ?_
    have h1 : ‖frameMap Y z‖ ≤ ‖frameMap Y‖ * ‖z‖ := (frameMap Y).le_opNorm z
    have h2 : ‖frameMap Y z‖ ^ 2 ≤ ‖frameMap Y‖ ^ 2 * ‖z‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have : 1 + ‖frameMap Y z‖ ^ 2 ≤ (1 + ‖frameMap Y‖ ^ 2) * (1 + ‖z‖ ^ 2) := by
      nlinarith [sq_nonneg ‖frameMap Y‖, sq_nonneg ‖z‖, mul_nonneg (sq_nonneg ‖frameMap Y‖)
        (sq_nonneg ‖z‖)]
    calc Cg * (1 + ‖frameMap Y z‖ ^ 2) ≤ Cg * ((1 + ‖frameMap Y‖ ^ 2) * (1 + ‖z‖ ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hvisc := isViscositySub_ballExtension_frame hn hu hc hμ (R := R) (Mu := Mu) hball hAc hY
  set χ' : ComplexModel n → ℝ := fun z => χ (frameMap Y z) with hχ'
  have hχ'd : ContDiff ℝ 2 χ' := hχ.comp ((frameMap Y).restrictScalars ℝ).contDiff
  have hχ'c : HasCompactSupport χ' := hχc.comp_homeomorph (frameHomeomorph hU)
  have hmain := integral_mul_leviSum_ge_of_psh hvpsh hvC (by positivity) hvisc hχ'd hχ'c
    (fun z => hχ0 _)
  obtain ⟨cT, hcT, hcTf⟩ := exists_integral_comp_frameMap hU
  have e1 : ∫ z, χ' z = cT * ∫ y, χ y := hcTf χ
  have e2 : ∫ z, v z * leviSum χ' z = cT * ∫ y, ue y * frameLevi Y χ y := by
    rw [← hcTf (fun y => ue y * frameLevi Y χ y)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hv, hχ', leviSum_comp_frameMap hχ]
  have e3 : ∫ y, ue y * frameLevi Y χ y = ∫ y, u y * frameLevi Y χ y := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ tsupport χ
    · have hy' : ‖y - x₀‖ < R / 2 := by
        have := hsupp hy; rwa [Metric.mem_ball, dist_eq_norm] at this
      simp only [hue, ballExtension_eq_of_lt_half hR hMu hA0 hy']
    · have : frameLevi Y χ y = 0 := by
        simp only [frameLevi, leviForm, realHessian_eq_zero_of_notMem_tsupport hy, add_zero,
          zero_div, Finset.sum_const_zero]
      simp [this]
  rw [e1, e2, e3] at hmain
  have : cT * (n * c ^ ((n : ℝ)⁻¹) * ∫ y, χ y) ≤ cT * ∫ y, u y * frameLevi Y χ y := by
    linarith
  exact le_of_mul_le_mul_left this hcT

end SGPT.NPP.LogConcavityDinew
