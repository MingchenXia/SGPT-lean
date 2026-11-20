import SGPT.Foundations.Analysis.Pending.HolomorphicPullback
import SGPT.Foundations.Analysis.DistributionRegularization
import SGPT.Foundations.Analysis.GermPshLeviPositivity
import SGPT.Foundations.Analysis.PshRegularDistribution
import SGPT.Foundations.Analysis.LocalPshDiscControl

set_option autoImplicit false

/-!
# Decreasing radial regularization of plurisubharmonic functions with poles

Let `U ⊆ ℂⁿ` be open and connected, and let `u : ℂⁿ → [-∞, ∞)` be plurisubharmonic on `U`
and finite somewhere on `U` (poles allowed).  Fix a smooth radial kernel `ρ` (nonnegative,
integral one, supported in the closed unit ball, invariant under the scalar circle action),
put `ρ_ε(y) = ε^{-2n} ρ(y / ε)` (`scaledKernel`) and let

  `u_ε(x) = (u * ρ_ε)(x) = ∫ u(x - y) ρ_ε(y) dy`  (`radialRegularization`),

the convolution of the real representative of `u` (which is locally integrable, and finite
almost everywhere).  On the inner domain `U_ε = {x : d(x, Uᶜ) > ε}` (`innerDomain`):

* `u_ε` is smooth and plurisubharmonic, with nonnegative Levi form
  (`contDiffOn_radialRegularization`, `plurisubharmonicOn_radialRegularization`,
  `leviForm_radialRegularization_nonneg`);
* `ε ↦ u_ε(x)` is nondecreasing (`radialRegularization_mono`);
* `u(x) ≤ u_ε(x)` and `u_ε(x) → u(x)` as `ε ↓ 0`, also at the poles of `u`
  (`le_radialRegularization`, `tendsto_radialRegularization`).

So every sequence `ε_j ↓ 0` gives a pointwise decreasing sequence of smooth PSH functions
converging to `u` on `U_{ε_0}` (`antitone_radialRegularization_seq`,
`tendsto_radialRegularization_seq`).  This is `demailly-cadg` I.5.5 (with I.4.18), the
blueprint theorem `psh:radial-regularization`.

## Route

* Locally bounded case: smooth radial integrals of a smooth PSH function are monotone in the
  radius (`HolomorphicPullback.integral_add_real_smul_mul_mono_of_smooth_pshOn`); a locally
  bounded real PSH function is the decreasing limit of smooth PSH functions on a relatively
  compact ball (`HolomorphicPullback.exists_decreasingMollifierApproximation`); a cutoff makes
  them global and dominated convergence passes the inequality to the limit
  (`integral_mono_of_locallyBoundedPsh`).
* Poles: the truncations `max(u, -k)` are locally bounded PSH; as `k → ∞` dominated
  convergence (the real representative is integrable on compact sets, the poles form a null set)
  gives the monotonicity and the submean inequality for `u` (`integral_mono_of_psh`,
  `le_integral_of_psh`).
* Smoothness and plurisubharmonicity: convolution of a locally integrable function with
  nonnegative distributional Levi form (`discPshOn_translationPairing_of_locallyIntegrableOn`).
* Convergence: the submean inequality from below; upper semicontinuity from above.
-/

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.PshRadialRegularization

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### Radial kernels and their rescalings -/

/-- A smooth radial kernel: smooth, nonnegative, of integral one, supported in the closed unit
ball and invariant under multiplication by complex scalars of modulus one.  (A smooth function of
`‖y‖` with these properties is one.) -/
structure IsRadialKernel (ρ : ComplexModel n → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ρ
  nonneg : ∀ y, 0 ≤ ρ y
  integral_eq_one : ∫ y, ρ y = 1
  tsupport_subset : tsupport ρ ⊆ closedBall 0 1
  circle_invariant : ∀ a : ℂ, ‖a‖ = 1 → ∀ y, ρ (a • y) = ρ y

/-- The rescaled kernel `ρ_ε(y) = ε^{-2n} ρ(ε⁻¹ y)` (`2n` is the real dimension, see
`scaledKernel_eq`). -/
def scaledKernel (ρ : ComplexModel n → ℝ) (ε : ℝ) (y : ComplexModel n) : ℝ :=
  (ε ^ Module.finrank ℝ (ComplexModel n))⁻¹ * ρ (ε⁻¹ • y)

theorem finrank_complexModel : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex]
  simp [ComplexModel]

theorem scaledKernel_eq (ρ : ComplexModel n → ℝ) (ε : ℝ) (y : ComplexModel n) :
    scaledKernel ρ ε y = (ε ^ (2 * n))⁻¹ * ρ (ε⁻¹ • y) := by
  rw [scaledKernel, finrank_complexModel]

/-- The radial regularization `u_ε = u * ρ_ε` of the real representative of `u`. -/
def radialRegularization (ρ : ComplexModel n → ℝ) (u : ComplexModel n → EReal) (ε : ℝ)
    (x : ComplexModel n) : ℝ :=
  ∫ y, (u (x - y)).toReal * scaledKernel ρ ε y

/-- The inner domain `U_ε = {x : d(x, Uᶜ) > ε}`, written without the distance to a possibly empty
complement. -/
def innerDomain (U : Set (ComplexModel n)) (ε : ℝ) : Set (ComplexModel n) :=
  {x | ∃ δ, ε < δ ∧ ball x δ ⊆ U}

namespace IsRadialKernel

variable {ρ : ComplexModel n → ℝ}

theorem neg (hρ : IsRadialKernel ρ) (y : ComplexModel n) : ρ (-y) = ρ y := by
  have h := hρ.circle_invariant (-1) (by simp) y
  simpa using h

theorem continuous (hρ : IsRadialKernel ρ) : Continuous ρ := hρ.contDiff.continuous

theorem hasCompactSupport (hρ : IsRadialKernel ρ) : HasCompactSupport ρ :=
  (isCompact_closedBall (0 : ComplexModel n) 1).of_isClosed_subset (isClosed_tsupport ρ)
    hρ.tsupport_subset

theorem eq_zero_of_one_lt_norm (hρ : IsRadialKernel ρ) {y : ComplexModel n} (hy : 1 < ‖y‖) :
    ρ y = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hρ.tsupport_subset h
  rw [mem_closedBall_zero_iff] at this
  linarith

theorem integrable (hρ : IsRadialKernel ρ) : Integrable ρ :=
  hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport

end IsRadialKernel

section Scaled

variable {ρ : ComplexModel n → ℝ}

theorem scaledKernel_nonneg (hρ : IsRadialKernel ρ) {ε : ℝ} (hε : 0 < ε) (y : ComplexModel n) :
    0 ≤ scaledKernel ρ ε y :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _)) (hρ.nonneg _)

theorem contDiff_scaledKernel (hρ : IsRadialKernel ρ) (ε : ℝ) :
    ContDiff ℝ ∞ (scaledKernel ρ ε) :=
  contDiff_const.mul (hρ.contDiff.comp (contDiff_const_smul _))

theorem scaledKernel_eq_zero (hρ : IsRadialKernel ρ) {ε : ℝ} (hε : 0 < ε) {y : ComplexModel n}
    (hy : ε < ‖y‖) : scaledKernel ρ ε y = 0 := by
  rw [scaledKernel, hρ.eq_zero_of_one_lt_norm, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, inv_mul_eq_div, one_lt_div hε]
  exact hy

theorem tsupport_scaledKernel_subset (hρ : IsRadialKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaledKernel ρ ε) ⊆ closedBall 0 ε := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall_zero_iff]
  by_contra h
  exact hy (scaledKernel_eq_zero hρ hε (not_le.mp h))

theorem hasCompactSupport_scaledKernel (hρ : IsRadialKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (scaledKernel ρ ε) :=
  (isCompact_closedBall (0 : ComplexModel n) ε).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_scaledKernel_subset hρ hε)

theorem scaledKernel_circle_invariant (hρ : IsRadialKernel ρ) (ε : ℝ) (a : ℂ) (ha : ‖a‖ = 1)
    (y : ComplexModel n) : scaledKernel ρ ε (a • y) = scaledKernel ρ ε y := by
  rw [scaledKernel, scaledKernel, smul_comm, hρ.circle_invariant a ha]

theorem scaledKernel_neg (hρ : IsRadialKernel ρ) (ε : ℝ) (y : ComplexModel n) :
    scaledKernel ρ ε (-y) = scaledKernel ρ ε y := by
  rw [scaledKernel, scaledKernel, smul_neg, hρ.neg]

/-- **Dilation.**  `∫ f(y) ρ_ε(y) dy = ∫ f(ε w) ρ(w) dw`. -/
theorem integral_mul_scaledKernel {ε : ℝ} (hε : 0 < ε) (f : ComplexModel n → ℝ) :
    ∫ y, f y * scaledKernel ρ ε y = ∫ w, f (ε • w) * ρ w := by
  have h := Measure.integral_comp_smul (volume : Measure (ComplexModel n))
    (fun y => f y * scaledKernel ρ ε y) ε
  have hd : (0 : ℝ) < ε ^ Module.finrank ℝ (ComplexModel n) := pow_pos hε _
  have hfun : (fun w : ComplexModel n => f (ε • w) * scaledKernel ρ ε (ε • w)) =
      fun w => (ε ^ Module.finrank ℝ (ComplexModel n))⁻¹ * (f (ε • w) * ρ w) := by
    funext w
    rw [scaledKernel, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    ring
  simp only [hfun, integral_const_mul, smul_eq_mul, abs_inv, abs_of_pos hd] at h
  have h' := congrArg (fun t => ε ^ Module.finrank ℝ (ComplexModel n) * t) h
  simp only [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at h'
  exact h'.symm

theorem integral_scaledKernel (hρ : IsRadialKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    ∫ y, scaledKernel ρ ε y = 1 := by
  have h := integral_mul_scaledKernel (ρ := ρ) hε (fun _ => 1)
  simp only [one_mul] at h
  rw [h, hρ.integral_eq_one]

/-- `u_ε(x) = ∫ u(x + ε w) ρ(w) dw`. -/
theorem radialRegularization_eq_dilate (hρ : IsRadialKernel ρ) (u : ComplexModel n → EReal)
    {ε : ℝ} (hε : 0 < ε) (x : ComplexModel n) :
    radialRegularization ρ u ε x = ∫ w, (u (x + ε • w)).toReal * ρ w := by
  rw [radialRegularization, integral_mul_scaledKernel hε (fun y => (u (x - y)).toReal)]
  rw [← integral_neg_eq_self]
  simp only [smul_neg, sub_neg_eq_add, hρ.neg]

/-- `u_{ε₁}(x) = ∫ u(x + (ε₁/ε₂) y) ρ_{ε₂}(y) dy`. -/
theorem radialRegularization_eq_scaled (hρ : IsRadialKernel ρ) (u : ComplexModel n → EReal)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (x : ComplexModel n) :
    radialRegularization ρ u ε₁ x =
      ∫ y, (u (x + (ε₁ / ε₂) • y)).toReal * scaledKernel ρ ε₂ y := by
  rw [radialRegularization_eq_dilate hρ u hε₁,
    integral_mul_scaledKernel hε₂ (fun y => (u (x + (ε₁ / ε₂) • y)).toReal)]
  simp only [smul_smul, div_mul_cancel₀ ε₁ hε₂.ne']

/-- `u_ε` is the translation pairing of the real representative with `ρ_ε` (the kernel is
even). -/
theorem radialRegularization_eq_translationPairing (hρ : IsRadialKernel ρ)
    (u : ComplexModel n → EReal) (ε : ℝ) :
    radialRegularization ρ u ε =
      translationPairing volume (fun y => (u y).toReal) (scaledKernel ρ ε) := by
  funext x
  rw [radialRegularization, translationPairing,
    ← integral_sub_left_eq_self _ (μ := (volume : Measure (ComplexModel n))) x]
  congr 1
  funext y
  rw [sub_sub_cancel, ← scaledKernel_neg hρ, neg_sub]

end Scaled

/-! ### The locally bounded case -/

section LocallyBounded

/-- `ψ F` is globally smooth when `ψ` is smooth with topological support in an open set on which
`F` is smooth. -/
theorem contDiff_mul_of_tsupport {ψ F : ComplexModel n → ℝ} {W : Set (ComplexModel n)}
    (hW : IsOpen W) (hψ : ContDiff ℝ ∞ ψ) (hψW : tsupport ψ ⊆ W) (hF : ContDiffOn ℝ ∞ F W) :
    ContDiff ℝ ∞ (fun z => ψ z * F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ W
  · exact hψ.contDiffAt.mul (hF.contDiffAt (hW.mem_nhds hz))
  · have hzs : z ∉ tsupport ψ := fun h => hz (hψW h)
    have hev : (fun z => ψ z * F z) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hzs] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem add_smul_mem_closedBall {z y : ComplexModel n} {R t : ℝ} (hy : ‖y‖ ≤ R) (ht : |t| ≤ 1)
    (hR : 0 ≤ R) : z + t • y ∈ closedBall z R := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  nlinarith [abs_nonneg t, norm_nonneg y]

/-- **Monotonicity of radial integrals, locally bounded case.**  Let `p` be a locally bounded
real PSH function on `Ω`, and `κ ≥ 0` continuous, circle invariant, supported in `closedBall 0 R`,
with `ball z δ ⊆ Ω` for some `δ > R`.  Then `t ↦ ∫ p(z + t y) κ(y) dy` is nondecreasing on
`[0, 1]`. -/
theorem integral_mono_of_locallyBoundedPsh
    {Ω : Opens (ComplexModel n)} {p : ComplexModel n → ℝ} (hp : IsLocallyBoundedPshOn Ω p)
    {κ : ComplexModel n → ℝ} (hκ : Continuous κ) (hκn : ∀ y, 0 ≤ κ y)
    (hκrad : ∀ a : ℂ, ‖a‖ = 1 → ∀ y, κ (a • y) = κ y)
    {z : ComplexModel n} {R δ : ℝ} (hκR : tsupport κ ⊆ closedBall 0 R) (hRδ : R < δ)
    (hzδ : ball z δ ⊆ Ω) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    ∫ y, p (z + r • y) * κ y ≤ ∫ y, p (z + s • y) * κ y := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hκc : HasCompactSupport κ :=
    (isCompact_closedBall (0 : ComplexModel n) R).of_isClosed_subset (isClosed_tsupport κ) hκR
  by_cases hR : R < 0
  · have hκ0 : ∀ y, κ y = 0 := fun y => image_eq_zero_of_notMem_tsupport (fun h => by
      have := hκR h
      rw [mem_closedBall_zero_iff] at this
      linarith [norm_nonneg y])
    simp [hκ0]
  push Not at hR
  have hnorm : ∀ y ∈ tsupport κ, ‖y‖ ≤ R := fun y hy => mem_closedBall_zero_iff.mp (hκR hy)
  set R1 := R + (δ - R) / 4 with hR1
  set R2 := R + (δ - R) / 2 with hR2
  set R3 := R + 3 * (δ - R) / 4 with hR3
  have h0R1 : 0 < R1 := by rw [hR1]; linarith
  have hRR1 : R < R1 := by rw [hR1]; linarith
  have hR12 : R1 < R2 := by rw [hR1, hR2]; linarith
  have hR23 : R2 < R3 := by rw [hR2, hR3]; linarith
  have hR3δ : R3 < δ := by rw [hR3]; linarith
  let A : Opens (ComplexModel n) := ⟨ball z R3, isOpen_ball⟩
  have hAset : (A : Set (ComplexModel n)) = ball z R3 := rfl
  have hA : RelativelyCompactIn A Ω := by
    rw [RelativelyCompactIn, hAset, closure_ball z (by linarith : R3 ≠ 0)]
    exact ⟨isCompact_closedBall z R3, (closedBall_subset_ball hR3δ).trans hzδ⟩
  obtain ⟨f, hfs, hfa, hft⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation hp hA
  obtain ⟨b, hbIn, hbOut⟩ : ∃ b : ContDiffBump z, b.rIn = R1 ∧ b.rOut = R2 :=
    ⟨⟨R1, R2, h0R1, hR12⟩, rfl, rfl⟩
  have hb1 : ∀ x ∈ ball z R1, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (by rw [hbIn]; exact ball_subset_closedBall hx)
  have hbsupp : tsupport b ⊆ (A : Set (ComplexModel n)) := by
    rw [b.tsupport_eq, hAset, hbOut]
    exact closedBall_subset_ball hR23
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ComplexModel n → ℝ, g = fun j x => b x * f j x := ⟨_, rfl⟩
  have hg : ∀ j, ContDiff ℝ ∞ (g j) := fun j => by
    rw [hg_def]
    exact contDiff_mul_of_tsupport A.isOpen b.contDiff hbsupp (hfs j).1
  have hgf : ∀ j, ∀ x ∈ ball z R1, g j x = f j x := fun j x hx => by
    simp only [hg_def, hb1 x hx, one_mul]
  have haff : ∀ t : ℝ, Continuous (fun y : ComplexModel n => z + t • y) := fun t => by
    fun_prop
  have hKR1 : closedBall z R ⊆ ball z R1 := closedBall_subset_ball hRR1
  have hR1A : ball z R1 ⊆ (A : Set (ComplexModel n)) := by
    rw [hAset]
    exact ball_subset_ball (by linarith)
  have hgpsh : ∀ j, PlurisubharmonicOn (fun x => (g j x : EReal)) (ball z R1) := by
    intro j x hx
    refine ((hfs j).2.1 x (hR1A hx)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hx] with w hw
    rw [hgf j w hw]
  have hsm : ∀ j, ∫ y, g j (z + r • y) * κ y ≤ ∫ y, g j (z + s • y) * κ y := by
    intro j
    have h := HolomorphicPullback.integral_add_real_smul_mul_mono_of_smooth_pshOn (hg j)
      isOpen_ball (hgpsh j) hκ hκc hκn hκrad z (fun y hy ζ hζ => by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
        nlinarith [hnorm y hy, norm_nonneg ζ, norm_nonneg y]) hr hrs hs
    simpa only [Complex.coe_smul] using h
  obtain ⟨Cp, -, hCp⟩ := hp.exists_compact_abs_bound (isCompact_closedBall z R)
    (hKR1.trans (hR1A.trans ((ball_subset_ball hR3δ.le).trans hzδ)))
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall z R).exists_bound_of_continuousOn
    ((hfs 0).1.continuousOn.mono (hKR1.trans hR1A))
  set C := |Cp| + |C0| with hC
  have hfbound : ∀ j, ∀ x ∈ closedBall z R, |f j x| ≤ C := by
    intro j x hx
    have hxA : x ∈ (A : Set (ComplexModel n)) := hR1A (hKR1 hx)
    have h1 : p x ≤ f j x := (hfa x hxA).le_of_tendsto (hft x hxA) j
    have h2 : f j x ≤ f 0 x := hfa x hxA (Nat.zero_le j)
    have h3 := abs_le.mp ((hCp x hx).trans (le_abs_self Cp))
    have h4 := abs_le.mp (((Real.norm_eq_abs _).symm.le.trans (hC0 x hx)).trans (le_abs_self C0))
    rw [hC]
    exact abs_le.mpr ⟨by linarith [abs_nonneg C0], by linarith [abs_nonneg Cp]⟩
  have hlim : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Tendsto (fun j => ∫ y, g j (z + t • y) * κ y) atTop (𝓝 (∫ y, p (z + t • y) * κ y)) := by
    intro t ht0 ht1
    have hmem : ∀ y ∈ tsupport κ, z + t • y ∈ closedBall z R := fun y hy =>
      add_smul_mem_closedBall (hnorm y hy) (by rw [abs_of_nonneg ht0]; exact ht1) hR
    refine tendsto_integral_of_dominated_convergence (fun y => C * κ y) ?_
      ((hκ.integrable_of_hasCompactSupport hκc).const_mul C) ?_ ?_
    · intro j
      exact (((hg j).continuous.comp (haff t)).mul hκ).aestronglyMeasurable
    · intro j
      refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ tsupport κ
      · rw [hgf j _ (hKR1 (hmem y hy)), norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hκn y)]
        exact mul_le_mul_of_nonneg_right (hfbound j _ (hmem y hy)) (hκn y)
      · rw [image_eq_zero_of_notMem_tsupport hy]
        simp
    · refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ tsupport κ
      · have hfun : (fun j => g j (z + t • y) * κ y) = fun j => f j (z + t • y) * κ y :=
          funext fun j => by rw [hgf j _ (hKR1 (hmem y hy))]
        rw [hfun]
        exact (hft _ (hR1A (hKR1 (hmem y hy)))).mul_const _
      · simp [image_eq_zero_of_notMem_tsupport hy]
  exact le_of_tendsto_of_tendsto' (hlim r hr (hrs.trans hs)) (hlim s (hr.trans hrs) hs) hsm

end LocallyBounded

/-! ### Poles: truncation and dominated convergence -/

section Poles

variable {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}

theorem toReal_max_coe {a : EReal} (ha : a ≠ ⊤) (hb : a ≠ ⊥) (k : ℝ) :
    (max a (k : EReal)).toReal = max a.toReal k := by
  rw [← EReal.coe_toReal ha hb, ← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe,
    EReal.toReal_coe]

theorem abs_toReal_max_le {a : EReal} (ha : a ≠ ⊤) (hb : a ≠ ⊥) {k : ℝ} (hk : 0 ≤ k) :
    |(max a ((-k : ℝ) : EReal)).toReal| ≤ |a.toReal| := by
  rw [toReal_max_coe ha hb]
  rcases le_total (-k) a.toReal with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, abs_neg, abs_of_nonneg hk, abs_of_nonpos (by linarith)]
    linarith

/-- The truncation `max(u, k)` of a PSH function is a locally bounded real PSH function. -/
theorem isLocallyBoundedPshOn_truncation (hU : IsOpen U) (hu : PlurisubharmonicOn u U) (k : ℝ) :
    IsLocallyBoundedPshOn ⟨U, hU⟩ (fun x => (max (u x) (k : EReal)).toReal) := by
  have hne_top : ∀ x ∈ U, max (u x) (k : EReal) ≠ ⊤ := fun x hx =>
    (max_lt (lt_top_iff_ne_top.mpr (hu x hx).ne_top) (EReal.coe_lt_top k)).ne
  have hne_bot : ∀ x, max (u x) (k : EReal) ≠ ⊥ := fun x =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot k) (le_max_right _ _)
  have hcoe : ∀ x ∈ U, (((max (u x) (k : EReal)).toReal : ℝ) : EReal) = max (u x) (k : EReal) :=
    fun x hx => EReal.coe_toReal (hne_top x hx) (hne_bot x)
  refine ⟨?_, ?_⟩
  · intro x hx
    have hmax : PlurisubharmonicAt (fun y => max (u y) (k : EReal)) x :=
      (hu x hx).max ((discPshOn_const (k : EReal) (EReal.coe_ne_top k) U).plurisubharmonicOn hU
        x hx)
    refine hmax.congr ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hcoe y hy]
  · intro x hx
    obtain ⟨c, hxc, -⟩ := EReal.lt_iff_exists_real_btwn.mp
      (lt_top_iff_ne_top.mpr (hu x hx).ne_top)
    have hev : ∀ᶠ y in 𝓝 x, u y < (c : EReal) ∧ y ∈ U :=
      ((hu x hx).upperSemicontinuousAt (c : EReal) hxc).and (hU.mem_nhds hx)
    obtain ⟨t, hts, hto, hxt⟩ := _root_.mem_nhds_iff.mp hev
    refine ⟨⟨t, hto⟩, hxt, fun y hy => (hts hy).2, |c| + |k|, fun y hy => ?_⟩
    have hyU : y ∈ U := (hts hy).2
    have h1 : ((k : ℝ) : EReal) ≤ (((max (u y) (k : EReal)).toReal : ℝ) : EReal) := by
      rw [hcoe y hyU]
      exact le_max_right _ _
    have h2 : (((max (u y) (k : EReal)).toReal : ℝ) : EReal) ≤ ((max c k : ℝ) : EReal) := by
      rw [hcoe y hyU, EReal.coe_strictMono.monotone.map_max]
      exact max_le_max (hts hy).1.le le_rfl
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le k, abs_nonneg c]
    · have hm : max c k ≤ |c| + |k| :=
        max_le ((le_abs_self c).trans (le_add_of_nonneg_right (abs_nonneg k)))
          ((le_abs_self k).trans (le_add_of_nonneg_left (abs_nonneg c)))
      linarith

/-- The affine map `y ↦ z + t y`, `t ≠ 0`, pulls null sets back to null sets. -/
theorem quasiMeasurePreserving_add_smul (z : ComplexModel n) {t : ℝ} (ht : t ≠ 0) :
    Measure.QuasiMeasurePreserving (fun y : ComplexModel n => z + t • y) volume volume := by
  have hs : Measure.QuasiMeasurePreserving (fun y : ComplexModel n => t • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ht
  have ht' : Measure.QuasiMeasurePreserving (fun y : ComplexModel n => z + y) volume volume :=
    (measurePreserving_add_left volume z).quasiMeasurePreserving
  simpa only [Function.comp_def] using ht'.comp hs

/-- Off the closed ball `L ⊇ z + t • tsupport κ`, `κ` vanishes: the integrand only sees `h` on
`L`. -/
theorem comp_mul_eq_indicator {κ : ComplexModel n → ℝ} {z : ComplexModel n} {t : ℝ}
    {L : Set (ComplexModel n)} (hmem : ∀ y ∈ tsupport κ, z + t • y ∈ L) (h : ComplexModel n → ℝ) :
    (fun y => h (z + t • y) * κ y) = fun y => L.indicator h (z + t • y) * κ y := by
  funext y
  by_cases hy : y ∈ tsupport κ
  · rw [indicator_of_mem (hmem y hy)]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

theorem integrable_comp_mul {κ : ComplexModel n → ℝ} (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    {g : ComplexModel n → ℝ} (hg : Integrable g) (z : ComplexModel n) {t : ℝ} (ht : t ≠ 0) :
    Integrable (fun y => g (z + t • y) * κ y) := by
  obtain ⟨C, hC⟩ := hκ.bounded_above_of_compact_support hκc
  have h1 : Integrable (fun y => g (z + t • y)) := (hg.comp_add_left z).comp_smul ht
  exact h1.mul_bdd hκ.aestronglyMeasurable (Eventually.of_forall hC)

/-- **Truncation limit.**  As `k → ∞`, `∫ max(u, -k)(z + t y) κ(y) dy → ∫ u(z + t y) κ(y) dy`
(dominated convergence; the poles of `u` form a null set). -/
theorem tendsto_integral_truncation (hU : IsOpen U) (hUc : IsPreconnected U)
    (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {κ : ComplexModel n → ℝ} (hκ : Continuous κ) (hκn : ∀ y, 0 ≤ κ y)
    {z : ComplexModel n} {R : ℝ} (hκR : tsupport κ ⊆ closedBall 0 R)
    (hzR : closedBall z R ⊆ U) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    Tendsto (fun k : ℕ => ∫ y, (max (u (z + t • y)) ((-(k : ℝ) : ℝ) : EReal)).toReal * κ y)
      atTop (𝓝 (∫ y, (u (z + t • y)).toReal * κ y)) := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hκc : HasCompactSupport κ :=
    (isCompact_closedBall (0 : ComplexModel n) R).of_isClosed_subset (isClosed_tsupport κ) hκR
  by_cases hR : R < 0
  · have hκ0 : ∀ y, κ y = 0 := fun y => image_eq_zero_of_notMem_tsupport (fun h => by
      have := hκR h
      rw [mem_closedBall_zero_iff] at this
      linarith [norm_nonneg y])
    simp [hκ0]
  push Not at hR
  have hnorm : ∀ y ∈ tsupport κ, ‖y‖ ≤ R := fun y hy => mem_closedBall_zero_iff.mp (hκR hy)
  have hmem : ∀ y ∈ tsupport κ, z + t • y ∈ closedBall z R := fun y hy =>
    add_smul_mem_closedBall (hnorm y hy) (by rw [abs_of_pos ht0]; exact ht1) hR
  have hqmp := quasiMeasurePreserving_add_smul z ht0.ne'
  have hfin : ∀ᵐ x ∂(volume : Measure (ComplexModel n)), x ∈ U → u x ≠ ⊤ ∧ u x ≠ ⊥ :=
    (ae_restrict_iff' hU.measurableSet).mp (hu.ae_finite volume hUc hne)
  have hfin' : ∀ᵐ y ∂(volume : Measure (ComplexModel n)),
      z + t • y ∈ U → u (z + t • y) ≠ ⊤ ∧ u (z + t • y) ≠ ⊥ := hqmp.ae hfin
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) U volume :=
    hu.locallyIntegrableOn_toReal volume hUc hne
  have hLint : Integrable ((closedBall z R).indicator (fun x => (u x).toReal)) :=
    ((huL.mono_set hzR).integrableOn_isCompact (isCompact_closedBall z R)).integrable_indicator
      measurableSet_closedBall
  have hbound : Integrable (fun y => |(u (z + t • y)).toReal| * κ y) := by
    have h := integrable_comp_mul hκ hκc hLint.abs z ht0.ne'
    refine h.congr (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport κ
    · simp only [indicator_of_mem (hmem y hy)]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  refine tendsto_integral_of_dominated_convergence (fun y => |(u (z + t • y)).toReal| * κ y)
    ?_ hbound ?_ ?_
  · intro k
    have hp := isLocallyBoundedPshOn_truncation hU hu (-(k : ℝ))
    have hpL := locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
    have hpint : Integrable ((closedBall z R).indicator
        (fun x => (max (u x) ((-(k : ℝ) : ℝ) : EReal)).toReal)) :=
      ((hpL.mono_set hzR).integrableOn_isCompact (isCompact_closedBall z R)).integrable_indicator
        measurableSet_closedBall
    have h := (integrable_comp_mul hκ hκc hpint z ht0.ne').aestronglyMeasurable
    rwa [← comp_mul_eq_indicator hmem] at h
  · intro k
    filter_upwards [hfin'] with y hy
    by_cases hyκ : y ∈ tsupport κ
    · obtain ⟨h1, h2⟩ := hy (hzR (hmem y hyκ))
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hκn y)]
      exact mul_le_mul_of_nonneg_right (abs_toReal_max_le h1 h2 (Nat.cast_nonneg k)) (hκn y)
    · rw [image_eq_zero_of_notMem_tsupport hyκ]
      simp
  · filter_upwards [hfin'] with y hy
    by_cases hyκ : y ∈ tsupport κ
    · obtain ⟨h1, h2⟩ := hy (hzR (hmem y hyκ))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈-(u (z + t • y)).toReal⌉₊] with k hk
      have hk' : -(k : ℝ) ≤ (u (z + t • y)).toReal := by
        have := (Nat.le_ceil (-(u (z + t • y)).toReal)).trans (Nat.cast_le.mpr hk)
        linarith
      rw [toReal_max_coe h1 h2, max_eq_left hk']
    · simp [image_eq_zero_of_notMem_tsupport hyκ]

/-- **Monotonicity of radial integrals, with poles.** -/
theorem integral_mono_of_psh (hU : IsOpen U) (hUc : IsPreconnected U)
    (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {κ : ComplexModel n → ℝ} (hκ : Continuous κ) (hκn : ∀ y, 0 ≤ κ y)
    (hκrad : ∀ a : ℂ, ‖a‖ = 1 → ∀ y, κ (a • y) = κ y)
    {z : ComplexModel n} {R δ : ℝ} (hκR : tsupport κ ⊆ closedBall 0 R) (hRδ : R < δ)
    (hzδ : ball z δ ⊆ U) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs : s ≤ 1) :
    ∫ y, (u (z + r • y)).toReal * κ y ≤ ∫ y, (u (z + s • y)).toReal * κ y := by
  have hzR : closedBall z R ⊆ U := (closedBall_subset_ball hRδ).trans hzδ
  refine le_of_tendsto_of_tendsto'
    (tendsto_integral_truncation hU hUc hu hne hκ hκn hκR hzR hr (hrs.trans hs))
    (tendsto_integral_truncation hU hUc hu hne hκ hκn hκR hzR (hr.trans_le hrs) hs) fun k => ?_
  exact integral_mono_of_locallyBoundedPsh (isLocallyBoundedPshOn_truncation hU hu (-(k : ℝ)))
    hκ hκn hκrad hκR hRδ hzδ hr.le hrs hs

/-- **Submean inequality against a radial kernel, with poles.** -/
theorem le_integral_of_psh (hU : IsOpen U) (hUc : IsPreconnected U)
    (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {κ : ComplexModel n → ℝ} (hκ : Continuous κ) (hκn : ∀ y, 0 ≤ κ y)
    (hκrad : ∀ a : ℂ, ‖a‖ = 1 → ∀ y, κ (a • y) = κ y) (hκ1 : ∫ y, κ y = 1)
    {z : ComplexModel n} {R δ : ℝ} (hκR : tsupport κ ⊆ closedBall 0 R) (hRδ : R < δ)
    (hzδ : ball z δ ⊆ U) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1) :
    u z ≤ ((∫ y, (u (z + s • y)).toReal * κ y : ℝ) : EReal) := by
  by_cases hz : u z = ⊥
  · rw [hz]
    exact bot_le
  have hR : 0 ≤ R := by
    by_contra hR
    have hκ0 : ∀ y, κ y = 0 := fun y => image_eq_zero_of_notMem_tsupport (fun h => by
      have := hκR h
      rw [mem_closedBall_zero_iff] at this
      linarith [norm_nonneg y])
    simp [hκ0] at hκ1
  have hzU : z ∈ U := hzδ (mem_ball_self (hR.trans_lt hRδ))
  have hztop : u z ≠ ⊤ := (hu z hzU).ne_top
  have hzR : closedBall z R ⊆ U := (closedBall_subset_ball hRδ).trans hzδ
  have hk : ∀ k : ℕ, (max (u z) ((-(k : ℝ) : ℝ) : EReal)).toReal ≤
      ∫ y, (max (u (z + s • y)) ((-(k : ℝ) : ℝ) : EReal)).toReal * κ y := by
    intro k
    have h := integral_mono_of_locallyBoundedPsh
      (isLocallyBoundedPshOn_truncation hU hu (-(k : ℝ))) hκ hκn hκrad hκR hRδ hzδ le_rfl
      hs0.le hs
    simp only [zero_smul, add_zero] at h
    rwa [integral_const_mul, hκ1, mul_one] at h
  have hlim := tendsto_integral_truncation hU hUc hu hne hκ hκn hκR hzR hs0 hs
  have hev : ∀ᶠ k : ℕ in atTop,
      (u z).toReal ≤ ∫ y, (max (u (z + s • y)) ((-(k : ℝ) : ℝ) : EReal)).toReal * κ y := by
    filter_upwards [eventually_ge_atTop ⌈-(u z).toReal⌉₊] with k hk'
    have hk'' : -(k : ℝ) ≤ (u z).toReal := by
      have := (Nat.le_ceil (-(u z).toReal)).trans (Nat.cast_le.mpr hk')
      linarith
    have := hk k
    rwa [toReal_max_coe hztop hz, max_eq_left hk''] at this
  rw [← EReal.coe_toReal hztop hz, EReal.coe_le_coe_iff]
  exact ge_of_tendsto hlim hev

end Poles

/-! ### The inner domains -/

section Inner

theorem isOpen_innerDomain (U : Set (ComplexModel n)) (ε : ℝ) : IsOpen (innerDomain U ε) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨δ, hεδ, hball⟩
  refine ⟨(δ - ε) / 2, by linarith, fun y hy => ⟨δ - dist y x, ?_, ?_⟩⟩
  · rw [mem_ball] at hy
    linarith
  · intro w hw
    apply hball
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w y x]

theorem innerDomain_subset {U : Set (ComplexModel n)} {ε : ℝ} (hε : 0 ≤ ε) :
    innerDomain U ε ⊆ U := fun _ ⟨_, hεδ, hball⟩ => hball (mem_ball_self (hε.trans_lt hεδ))

theorem innerDomain_anti {U : Set (ComplexModel n)} {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    innerDomain U ε₂ ⊆ innerDomain U ε₁ := fun _ ⟨δ, hεδ, hball⟩ => ⟨δ, h.trans_lt hεδ, hball⟩

theorem iUnion_innerDomain {U : Set (ComplexModel n)} (hU : IsOpen U) :
    ⋃ ε > (0 : ℝ), innerDomain U ε = U := by
  apply Subset.antisymm
  · simp only [iUnion_subset_iff]
    exact fun ε hε => innerDomain_subset hε.le
  · intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
    simp only [mem_iUnion]
    exact ⟨δ / 2, by linarith, ⟨δ, by linarith, hball⟩⟩

theorem tsupport_scaledKernel_translate_subset {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (z : ComplexModel n) :
    tsupport (fun x => scaledKernel ρ ε (x - z)) ⊆ closedBall z ε := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hx (scaledKernel_eq_zero hρ hε (not_le.mp h))

/-- Around a point of `U_ε`, the translated kernels have supports in one compact subset of `U`. -/
theorem exists_local_support {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {U : Set (ComplexModel n)} {ε : ℝ} (hε : 0 < ε) {x₀ : ComplexModel n}
    (hx₀ : x₀ ∈ innerDomain U ε) :
    ∃ N K : Set (ComplexModel n), IsOpen N ∧ x₀ ∈ N ∧ IsCompact K ∧ K ⊆ U ∧
      ∀ z ∈ N, tsupport (fun x => scaledKernel ρ ε (x - z)) ⊆ K := by
  obtain ⟨δ, hεδ, hball⟩ := hx₀
  refine ⟨ball x₀ ((δ - ε) / 2), closedBall x₀ ((ε + δ) / 2), isOpen_ball,
    mem_ball_self (by linarith), isCompact_closedBall _ _,
    (closedBall_subset_ball (by linarith)).trans hball, fun z hz => ?_⟩
  refine (tsupport_scaledKernel_translate_subset hρ hε z).trans
    (closedBall_subset_closedBall' ?_)
  rw [mem_ball] at hz
  linarith

theorem leviForm_congr {F G : ComplexModel n → ℝ} {x : ComplexModel n} (h : F =ᶠ[𝓝 x] G)
    (v : ComplexModel n) : leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

end Inner

/-! ### The regularization -/

section Main

variable {ρ : ComplexModel n → ℝ} {U : Set (ComplexModel n)} {u : ComplexModel n → EReal}

/-- `u_ε` is smooth on `U_ε`. -/
theorem contDiffOn_radialRegularization (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (radialRegularization ρ u ε) (innerDomain U ε) := by
  intro x₀ hx₀
  obtain ⟨N, K, hN, hx₀N, hK, hKU, hNK⟩ := exists_local_support hρ hε hx₀
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) (⟨U, hU⟩ : Opens (ComplexModel n))
      volume := hu.locallyIntegrableOn_toReal volume hUc hne
  have h := contDiffOn_translationPairing_of_locallyIntegrableOn huL
    (hasCompactSupport_scaledKernel hρ hε) (contDiff_scaledKernel hρ ε) hK hKU hNK
  rw [radialRegularization_eq_translationPairing hρ]
  exact (h.contDiffAt (hN.mem_nhds hx₀N)).contDiffWithinAt

/-- `u_ε` is plurisubharmonic on `U_ε`. -/
theorem plurisubharmonicOn_radialRegularization (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {ε : ℝ} (hε : 0 < ε) :
    PlurisubharmonicOn (fun x => (radialRegularization ρ u ε x : EReal)) (innerDomain U ε) := by
  intro x₀ hx₀
  obtain ⟨N, K, hN, hx₀N, hK, hKU, hNK⟩ := exists_local_support hρ hε hx₀
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) (⟨U, hU⟩ : Opens (ComplexModel n))
      volume := hu.locallyIntegrableOn_toReal volume hUc hne
  have hT := hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (Ω := (⟨U, hU⟩ : Opens (ComplexModel n))) huL (hu.ae_finite volume hUc hne)
  have h := discPshOn_translationPairing_of_locallyIntegrableOn huL hT
    (hasCompactSupport_scaledKernel hρ hε) (contDiff_scaledKernel hρ ε)
    (scaledKernel_nonneg hρ hε) hK hKU hNK
  refine ⟨N, hN, hx₀N, ?_⟩
  rw [radialRegularization_eq_translationPairing hρ]
  exact h

/-- `u_ε` has nonnegative Levi form on `U_ε`. -/
theorem leviForm_radialRegularization_nonneg (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {ε : ℝ} (hε : 0 < ε) {x : ComplexModel n} (hx : x ∈ innerDomain U ε) (v : ComplexModel n) :
    0 ≤ leviForm (radialRegularization ρ u ε) x v := by
  obtain ⟨N, K, hN, hxN, hK, hKU, hNK⟩ := exists_local_support hρ hε hx
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) (⟨U, hU⟩ : Opens (ComplexModel n))
      volume := hu.locallyIntegrableOn_toReal volume hUc hne
  have hT := hu.hasNonnegativeDistributionalLevi_of_locallyIntegrable
    (Ω := (⟨U, hU⟩ : Opens (ComplexModel n))) huL (hu.ae_finite volume hUc hne)
  have h := leviForm_translationPairing_indicator_nonneg huL hT
    (hasCompactSupport_scaledKernel hρ hε) (contDiff_scaledKernel hρ ε)
    (scaledKernel_nonneg hρ hε) hK hKU x (hNK x hxN) v
  have hev : radialRegularization ρ u ε =ᶠ[𝓝 x]
      translationPairing volume (K.indicator fun y => (u y).toReal) (scaledKernel ρ ε) := by
    filter_upwards [hN.mem_nhds hxN] with z hz
    rw [radialRegularization_eq_translationPairing hρ,
      translationPairing_indicator_eq _ _ z (hNK z hz)]
  rwa [leviForm_congr hev]

/-- **Monotonicity:** `ε ↦ u_ε(x)` is nondecreasing on `(0, ε₂]` for `x ∈ U_{ε₂}`. -/
theorem radialRegularization_mono (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (h₁₂ : ε₁ ≤ ε₂) {x : ComplexModel n}
    (hx : x ∈ innerDomain U ε₂) :
    radialRegularization ρ u ε₁ x ≤ radialRegularization ρ u ε₂ x := by
  have hε₂ : 0 < ε₂ := hε₁.trans_le h₁₂
  rw [radialRegularization_eq_scaled hρ u hε₁ hε₂ x, radialRegularization_eq_scaled hρ u hε₂ hε₂ x]
  obtain ⟨δ, hεδ, hball⟩ := hx
  exact integral_mono_of_psh hU hUc hu hne (contDiff_scaledKernel hρ ε₂).continuous
    (scaledKernel_nonneg hρ hε₂) (scaledKernel_circle_invariant hρ ε₂)
    (tsupport_scaledKernel_subset hρ hε₂) hεδ hball (div_pos hε₁ hε₂)
    (div_le_div_of_nonneg_right h₁₂ hε₂.le) (by rw [div_self hε₂.ne'])

/-- **Submean inequality:** `u(x) ≤ u_ε(x)` on `U_ε`, poles included. -/
theorem le_radialRegularization (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {ε : ℝ} (hε : 0 < ε) {x : ComplexModel n} (hx : x ∈ innerDomain U ε) :
    u x ≤ (radialRegularization ρ u ε x : EReal) := by
  rw [radialRegularization_eq_scaled hρ u hε hε x]
  obtain ⟨δ, hεδ, hball⟩ := hx
  exact le_integral_of_psh hU hUc hu hne (contDiff_scaledKernel hρ ε).continuous
    (scaledKernel_nonneg hρ hε) (scaledKernel_circle_invariant hρ ε) (integral_scaledKernel hρ hε)
    (tsupport_scaledKernel_subset hρ hε) hεδ hball (div_pos hε hε) (by rw [div_self hε.ne'])

/-- An upper bound for `u` near `x` bounds `u_ε(x)` for small `ε`. -/
theorem radialRegularization_le (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {x : ComplexModel n} {δ A : ℝ} (hball : ball x δ ⊆ U) (hA : ∀ y ∈ ball x δ, u y < A)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ) :
    radialRegularization ρ u ε x ≤ A := by
  have : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  rw [radialRegularization_eq_dilate hρ u hε x]
  have hmem : ∀ w ∈ tsupport ρ, x + ε • w ∈ closedBall x ε := fun w hw => by
    have h1 := mem_closedBall_zero_iff.mp (hρ.tsupport_subset hw)
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε]
    nlinarith [norm_nonneg w]
  have hεU : closedBall x ε ⊆ U := (closedBall_subset_ball hεδ).trans hball
  have huL : LocallyIntegrableOn (fun x => (u x).toReal) U volume :=
    hu.locallyIntegrableOn_toReal volume hUc hne
  have hLint : Integrable ((closedBall x ε).indicator (fun x => (u x).toReal)) :=
    ((huL.mono_set hεU).integrableOn_isCompact (isCompact_closedBall x ε)).integrable_indicator
      measurableSet_closedBall
  have hint : Integrable (fun w => (u (x + ε • w)).toReal * ρ w) := by
    rw [comp_mul_eq_indicator hmem (fun y => (u y).toReal)]
    exact integrable_comp_mul hρ.continuous hρ.hasCompactSupport hLint x hε.ne'
  have hfin : ∀ᵐ y ∂(volume : Measure (ComplexModel n)), y ∈ U → u y ≠ ⊤ ∧ u y ≠ ⊥ :=
    (ae_restrict_iff' hU.measurableSet).mp (hu.ae_finite volume hUc hne)
  have hfin' := (quasiMeasurePreserving_add_smul x hε.ne').ae hfin
  calc ∫ w, (u (x + ε • w)).toReal * ρ w ≤ ∫ w, A * ρ w := by
        refine integral_mono_ae hint (hρ.integrable.const_mul A) ?_
        filter_upwards [hfin'] with w hw
        by_cases hwρ : w ∈ tsupport ρ
        · have hwb : x + ε • w ∈ ball x δ := closedBall_subset_ball hεδ (hmem w hwρ)
          obtain ⟨h1, h2⟩ := hw (hball hwb)
          have hlt := hA _ hwb
          rw [← EReal.coe_toReal h1 h2, EReal.coe_lt_coe_iff] at hlt
          exact mul_le_mul_of_nonneg_right hlt.le (hρ.nonneg w)
        · simp [image_eq_zero_of_notMem_tsupport hwρ]
    _ = A := by rw [integral_const_mul, hρ.integral_eq_one, mul_one]

/-- **Convergence:** `u_ε(x) → u(x)` as `ε ↓ 0`, for every `x ∈ U`, poles included. -/
theorem tendsto_radialRegularization (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {x : ComplexModel n} (hx : x ∈ U) :
    Tendsto (fun ε => (radialRegularization ρ u ε x : EReal)) (𝓝[>] 0) (𝓝 (u x)) := by
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.mp hU x hx
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with ε hε
    exact ha.trans_le (le_radialRegularization hρ hU hUc hu hne hε.1 ⟨δ₀, hε.2, hball₀⟩)
  · intro a ha
    obtain ⟨A, hxA, hAa⟩ := EReal.lt_iff_exists_real_btwn.mp ha
    have hev : ∀ᶠ y in 𝓝 x, u y < A := (hu x hx).upperSemicontinuousAt A hxA
    obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hev
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₀ hδ₁)] with ε hε
    have h := radialRegularization_le hρ hU hUc hu hne
      ((ball_subset_ball (min_le_left δ₀ δ₁)).trans hball₀)
      (fun y hy => hball₁ (ball_subset_ball (min_le_right δ₀ δ₁) hy)) hε.1 hε.2
    exact (EReal.coe_le_coe_iff.mpr h).trans_lt hAa

/-- **Decreasing smooth PSH approximation.**  For `ε_j ↓ 0`, the functions `u_{ε_j}` decrease
pointwise on `U_{ε_0}`. -/
theorem antitone_radialRegularization_seq (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {εs : ℕ → ℝ} (hpos : ∀ j, 0 < εs j) (hanti : Antitone εs) {x : ComplexModel n}
    (hx : x ∈ innerDomain U (εs 0)) :
    Antitone fun j => radialRegularization ρ u (εs j) x := by
  intro j k hjk
  exact radialRegularization_mono hρ hU hUc hu hne (hpos k) (hanti hjk)
    (innerDomain_anti (hanti (Nat.zero_le j)) hx)

/-- For `ε_j ↓ 0` (`ε_j > 0`), `u_{ε_j}(x) → u(x)` for every `x ∈ U`. -/
theorem tendsto_radialRegularization_seq (hρ : IsRadialKernel ρ) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hu : PlurisubharmonicOn u U) (hne : ∃ a ∈ U, u a ≠ ⊥)
    {εs : ℕ → ℝ} (hpos : ∀ j, 0 < εs j) (hlim : Tendsto εs atTop (𝓝 0)) {x : ComplexModel n}
    (hx : x ∈ U) :
    Tendsto (fun j => (radialRegularization ρ u (εs j) x : EReal)) atTop (𝓝 (u x)) :=
  (tendsto_radialRegularization hρ hU hUc hu hne hx).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩)

end Main

end SGPT.Foundations.Analysis.Pending.PshRadialRegularization
