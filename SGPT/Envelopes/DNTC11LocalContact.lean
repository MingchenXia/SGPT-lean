import SGPT.Envelopes.DNTC11Local

/-!
# The local contact inequality and the density formula for bounded Hessian densities

Lane S53 (`claude-dnt-c11`).  This file extends WN-REG2's local contact argument
(`ContactLocal`, node `tok-wn-reg:dnt-local`) from smooth obstacles to obstacles `q` that are only
continuous with a bounded density `H` of their distributional complex Hessian
(`IsBoundedHessianDensityOn q H Ω`), and proves the density formula for the Bedford–Taylor measure
of a continuous plurisubharmonic function with a bounded Hessian density.

* `exists_setLIntegral_sub_le_of_contact`: quadratic ball averages of `q - V` at contact points
  (the comparison function `M|· - y|² - q` is plurisubharmonic because its Hessian density is
  semipositive, `plurisubharmonicOn_of_hermQuad_nonneg`).
* `tendsto_leviForm_mollified_of_flat`, `ae_tendsto_smoothDensity_mollified_contact`: at almost
  every contact point the complex Hessians of the mollified potentials converge to `H`
  (flatness at density points + Lebesgue points of `H`).
* `canonicalBedfordTaylorMeasure_contact_ge`, `truncationLimitMeasure_contact_ge`: the local
  contact inequality `∫_T (n!/πⁿ) det H ≤ ⟨(ddᶜU)ⁿ⟩(T)` on subsets `T` of the contact set.
* `canonicalBedfordTaylorMeasure_eq_density`: for `Q` continuous plurisubharmonic with bounded
  density `H`, `(ddᶜQ)ⁿ = (n!/πⁿ) det H dV` (dominated convergence along the mollifications and
  the Besicovitch–Vitali differentiation of measures); `ae_hessDensity_nonneg_of_psh`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Envelopes.DNTC11

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Okounkov.TranscendentalWNReg SGPT.Okounkov.TranscendentalWNReg.ContactLocal

variable {n : ℕ}

/-! ### Quadratic ball averages at contact points -/

section Submean

variable {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
  {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {x₀ : ComplexModel n} {R : ℝ}

/-- **Quadratic ball averages at contact points**, for an obstacle with a bounded Hessian density.
There is `M ≥ 0` with `∫_{B̄(y,s)} (q - V) ≤ M s² |B̄(y,s)|` at every contact point `y` and every
`B̄(y, s) ⊆ B(x₀, 4R)`. -/
theorem exists_setLIntegral_sub_le_of_contact (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : IsBoundedHessianDensityOn q H Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ComplexModel n, y ∈ Ω → V y = q y → ∀ s : ℝ, 0 < s →
      closedBall y s ⊆ ball x₀ (4 * R) →
        ∫⁻ x in closedBall y s, ENNReal.ofReal (q x - V x) ≤
          ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set W : Set (ComplexModel n) := ball x₀ (4 * R) with hW
  have hWΩ : W ⊆ Ω := ball_subset_closedBall.trans hball
  obtain ⟨M, hM0, hM⟩ := hq.exists_ae_abs_hermQuad_le (isCompact_closedBall x₀ (4 * R)) hball
  have hMW : ∀ᵐ z ∂(volume.restrict W), ∀ v, |hermQuad (H z) v| ≤ M * ‖v‖ ^ 2 :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hM
  refine ⟨M, hM0, fun y hyΩ hyq s hs hsW => ?_⟩
  -- the plurisubharmonic comparison function `M|· - y|² - q`
  set k : ComplexModel n → ℝ := fun x => M * ‖x - y‖ ^ 2 + (-1) * q x with hk
  have hsq : ContDiffOn ℝ ∞ (fun x : ComplexModel n => ‖x - y‖ ^ 2) W :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffOn
  have hkd := ((isBoundedHessianDensityOn_of_contDiffOn isOpen_ball hsq).smul M).add
    ((hq.mono isOpen_ball hWΩ).smul (-1))
  have hkpsh : PlurisubharmonicOn (fun x => (k x : EReal)) W := by
    refine plurisubharmonicOn_of_hermQuad_nonneg hkd fun v => ?_
    filter_upwards [hMW, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzW
    rw [hermQuad_add, hermQuad_smul, hermQuad_smul]
    have hsmooth : smoothHess W (fun x : ComplexModel n => ‖x - y‖ ^ 2) z = 1 := by
      simp only [smoothHess, hzW, if_true]
      exact SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.complexHessian_norm_sub_sq y z
    rw [hsmooth, hermQuad_one]
    have := hz v
    have := le_abs_self (hermQuad (H z) v)
    linarith
  have hsum : PlurisubharmonicOn (fun x => ((V x + k x : ℝ) : EReal)) W := by
    have h1 := (hV.1.mono hWΩ).add hkpsh
    simpa only [EReal.coe_add] using h1
  have hsubmean := PSHD.real_ball_submean
    (FirstPass.PlurisubharmonicOn.discPshOn hsum) volume y hs hsW
  have hy0 : V y + k y = 0 := by simp [hk, hyq]
  rw [hy0, mul_zero] at hsubmean
  -- integrability on the ball
  have hBΩ : closedBall y s ⊆ Ω := hsW.trans hWΩ
  have hVint : IntegrableOn V (closedBall y s) :=
    (locallyIntegrableOn_of_plurisubharmonicOn_real hV.1).integrableOn_compact_subset hBΩ
      (isCompact_closedBall y s)
  have hqint : IntegrableOn q (closedBall y s) :=
    (hq.continuousOn.mono hBΩ).integrableOn_compact (isCompact_closedBall y s)
  have hnint : IntegrableOn (fun x : ComplexModel n => M * ‖x - y‖ ^ 2) (closedBall y s) :=
    (by fun_prop : Continuous fun x : ComplexModel n => M * ‖x - y‖ ^ 2).continuousOn
      |>.integrableOn_compact (isCompact_closedBall y s)
  have hVb := hVint.mono_set ball_subset_closedBall
  have hqb := hqint.mono_set ball_subset_closedBall
  have hnb := hnint.mono_set ball_subset_closedBall
  have hdiff : ∫ x in ball y s, (q x - V x) ≤ M * s ^ 2 * (volume (ball y s)).toReal := by
    have e : ∫ x in ball y s, (q x - V x) =
        (∫ x in ball y s, M * ‖x - y‖ ^ 2) - ∫ x in ball y s, (V x + k x) := by
      have hsumint : IntegrableOn (fun x => V x + k x) (ball y s) :=
        hVb.add (hnb.add (hqb.const_mul (-1)))
      rw [← integral_sub hnb hsumint]
      congr 1
      funext x
      simp only [hk]
      ring
    have hn2 : ∫ x in ball y s, M * ‖x - y‖ ^ 2 ≤ ∫ x in ball y s, M * s ^ 2 := by
      refine setIntegral_mono_on hnb (integrableOn_const measure_ball_lt_top.ne)
        measurableSet_ball fun x hx => ?_
      have hx' : ‖x - y‖ ≤ s := (mem_ball_iff_norm.mp hx).le
      gcongr
    rw [setIntegral_const, smul_eq_mul, mul_comm] at hn2
    rw [e]
    simp only [Measure.real] at hn2
    linarith
  have hball_eq : volume (closedBall y s) = volume (ball y s) :=
    Measure.addHaar_closedBall_eq_addHaar_ball volume y s
  have hae : (ball y s : Set (ComplexModel n)) =ᵐ[volume] closedBall y s :=
    ae_eq_of_subset_of_measure_ge ball_subset_closedBall hball_eq.le
      measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  calc ∫⁻ x in closedBall y s, ENNReal.ofReal (q x - V x)
      = ∫⁻ x in ball y s, ENNReal.ofReal (q x - V x) := setLIntegral_congr hae.symm
    _ = ENNReal.ofReal (∫ x in ball y s, (q x - V x)) := by
        have hsubint : IntegrableOn (fun x => q x - V x) (ball y s) := hqb.sub hVb
        rw [ofReal_integral_eq_lintegral_ofReal hsubint]
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact sub_nonneg.mpr (hVq x (hWΩ (hsW (ball_subset_closedBall hx))))
    _ ≤ ENNReal.ofReal (M * s ^ 2 * (volume (ball y s)).toReal) := ENNReal.ofReal_le_ofReal hdiff
    _ = ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hM0 (sq_nonneg s)),
          ENNReal.ofReal_toReal measure_ball_lt_top.ne, hball_eq]

end Submean

/-! ### Convergence of the densities on the contact set -/

section Bounded

variable {Ω : Opens (ComplexModel n)} {V q : ComplexModel n → ℝ}
  {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {x₀ : ComplexModel n} {R : ℝ}

theorem measurableSet_contactBall' (hV : IsLocallyBoundedPshOn Ω V) (hq : ContinuousOn q Ω) :
    MeasurableSet (contactBall Ω V q x₀ R) :=
  (SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.measurableSet_eq_of_upperSemicontinuousOn hq
    hV.1.upperSemicontinuousOn).inter measurableSet_ball

theorem leviForm_explicitRadialKernel_eq_zero (hR : 0 < R) (j : ℕ) {z x : ComplexModel n}
    (hx : R / ((j : ℝ) + 1) < dist x z) (w : ComplexModel n) :
    leviForm (explicitRadialKernel (n := n) R hR j) (x - z) w = 0 := by
  simp only [leviForm, realHessian_explicitRadialKernel_sub_eq_zero R hR j hx, add_zero, zero_div]

theorem continuous_leviForm_explicitRadialKernel (hR : 0 < R) (j : ℕ) (w : ComplexModel n) :
    Continuous fun y => leviForm (explicitRadialKernel (n := n) R hR j) y w :=
  continuous_leviForm (explicitRadialKernel_contDiff_two R hR j) w

theorem hasCompactSupport_leviForm_explicitRadialKernel (hR : 0 < R) (j : ℕ) (w : ComplexModel n) :
    HasCompactSupport fun y => leviForm (explicitRadialKernel (n := n) R hR j) y w := by
  refine (explicitRadialKernel_hasCompactSupport R hR j).mono' fun y hy => ?_
  by_contra hyt
  apply hy
  simp only [leviForm, ContactLocal.realHessian_eq_zero_of_notMem_tsupport hyt, add_zero, zero_div]

/-- **The Levi forms of the mollified potentials at a flat contact point** follow those of the
mollified obstacle: if `∫_{B̄(z,r)} (q - V) = o(r² |B̄(z,r)|)`, then
`∂_w∂̄_w(V * κ_j)(z) - ∂_w∂̄_w(q * κ_j)(z) → 0`. -/
theorem tendsto_leviForm_mollified_of_flat (hV : IsLocallyBoundedPshOn Ω V)
    (hqc : ContinuousOn q Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {z : ComplexModel n} (hz : z ∈ ball x₀ (2 * R))
    (hflat : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) ≤
        ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r))
    (w : ComplexModel n) {a : ℝ}
    (hA : Tendsto (fun j => leviForm (mollified q x₀ R hR j) z w) atTop (𝓝 a)) :
    Tendsto (fun j => leviForm (mollified V x₀ R hR j) z w) atTop (𝓝 a) := by
  set K : Set (ComplexModel n) := closedBall x₀ (3 * R) with hK
  have hKΩ : K ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  have hzK : closedBall z R ⊆ K := closedBall_subset_of_mem_innerBall hz
  have hgV := locallyIntegrable_indicator hV hball hR
  have hgq := locallyIntegrable_indicator_closedBall hqc hR hball
  set L : ℕ → ComplexModel n → ℝ := fun j y => leviForm (explicitRadialKernel (n := n) R hR j) y w
    with hL
  have hrad : ∀ j : ℕ, R / ((j : ℝ) + 1) ≤ R := fun j =>
    shrinkingBump_rOut_le (E := ComplexModel n) R hR j
  -- the decomposition `∂_w∂̄_w V_j(z) = ∂_w∂̄_w q_j(z) - B_j`
  set B : ℕ → ℝ := fun j => ∫ x, (K.indicator q x - K.indicator V x) * L j (x - z) with hB
  have hdecomp : ∀ j, leviForm (mollified V x₀ R hR j) z w =
      leviForm (mollified q x₀ R hR j) z w - B j := by
    intro j
    have h1 := integrable_translationPairing hgq
      (hasCompactSupport_leviForm_explicitRadialKernel hR j w)
      (continuous_leviForm_explicitRadialKernel hR j w) z
    have h2 := integrable_translationPairing hgV
      (hasCompactSupport_leviForm_explicitRadialKernel hR j w)
      (continuous_leviForm_explicitRadialKernel hR j w) z
    rw [mollified, mollified, leviForm_translationPairing hgV
      (explicitRadialKernel_hasCompactSupport R hR j) (explicitRadialKernel_contDiff_two R hR j),
      leviForm_translationPairing hgq (explicitRadialKernel_hasCompactSupport R hR j)
      (explicitRadialKernel_contDiff_two R hR j)]
    have e : B j = (∫ x, (closedBall x₀ (3 * R)).indicator q x *
          leviForm (explicitRadialKernel R hR j) (x - z) w) -
        ∫ x, (closedBall x₀ (3 * R)).indicator V x *
          leviForm (explicitRadialKernel R hR j) (x - z) w := by
      rw [← integral_sub h1 h2]
      show (∫ x, (K.indicator q x - K.indicator V x) * L j (x - z)) = _
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hL, hK]
      ring
    rw [e]
    ring
  -- `B_j → 0`
  obtain ⟨M₁, hM₁, hM₁b⟩ := exists_abs_realHessian_explicitRadialKernel_le (n := n) R hR w w
  obtain ⟨M₂, hM₂, hM₂b⟩ :=
    exists_abs_realHessian_explicitRadialKernel_le (n := n) R hR (Complex.I • w) (Complex.I • w)
  set M₀ : ℝ := (M₁ + M₂) / 4 with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set d := Module.finrank ℝ (ComplexModel n) with hd
  have hLb : ∀ (j : ℕ) y, |L j y| ≤ ((j : ℝ) + 1) ^ (d + 2) * M₀ := by
    intro j y
    simp only [hL, leviForm]
    have e1 := hM₁b j y
    have e2 := hM₂b j y
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc |realHessian (explicitRadialKernel R hR j) y w w +
          realHessian (explicitRadialKernel R hR j) y (Complex.I • w) (Complex.I • w)| / 4
        ≤ (((j : ℝ) + 1) ^ (d + 2) * M₁ + ((j : ℝ) + 1) ^ (d + 2) * M₂) / 4 := by
          gcongr
          exact (abs_add_le _ _).trans (add_le_add e1 e2)
      _ = ((j : ℝ) + 1) ^ (d + 2) * M₀ := by rw [hM₀]; ring
  set c₁ := volume (ball (0 : ComplexModel n) 1) with hc₁
  have hc₁top : c₁ ≠ ⊤ := measure_ball_lt_top.ne
  have hBlim : Tendsto B atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    set Λ : ℝ := M₀ * R ^ (d + 2) * c₁.toReal with hΛ
    have hΛ0 : 0 ≤ Λ := by positivity
    set ε : ℝ := ε' / (2 * (Λ + 1)) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨J, hJ⟩ := ((tendsto_kernel_radius R hR).eventually (hflat ε hε0)).exists_forall_of_atTop
    refine ⟨J, fun j hj => ?_⟩
    have hJj := hJ j hj
    set r : ℝ := R / ((j : ℝ) + 1) with hr
    set cj : ℝ := (j : ℝ) + 1 with hcj
    have hcj0 : 0 < cj := by positivity
    have hr0 : 0 < r := by positivity
    have hrR : r ≤ R := hrad j
    have hpt : ∀ x, ‖(K.indicator q x - K.indicator V x) * L j (x - z)‖ₑ ≤
        (closedBall z r).indicator
          (fun x => ENNReal.ofReal (cj ^ (d + 2) * M₀) * ENNReal.ofReal (q x - V x)) x := by
      intro x
      by_cases hx : x ∈ closedBall z r
      · have hxK : x ∈ K := hzK (closedBall_subset_closedBall hrR hx)
        have hxΩ : x ∈ Ω := hKΩ hxK
        rw [indicator_of_mem hx, indicator_of_mem hxK, indicator_of_mem hxK,
          Real.enorm_eq_ofReal_abs, abs_mul,
          abs_of_nonneg (sub_nonneg.mpr (hVq x hxΩ)), ← ENNReal.ofReal_mul (by positivity),
          mul_comm]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hLb j (x - z))
          (sub_nonneg.mpr (hVq x hxΩ)))
      · have hxr : r < dist x z := not_le.mp hx
        rw [indicator_of_notMem hx]
        simp [hL, leviForm_explicitRadialKernel_eq_zero hR j hxr w]
    have hvol : volume (closedBall z r) = ENNReal.ofReal (r ^ d) * c₁ :=
      Measure.addHaar_closedBall volume z hr0.le
    have hbound : ‖B j‖ₑ ≤ ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
      calc ‖B j‖ₑ ≤ ∫⁻ x, ‖(K.indicator q x - K.indicator V x) * L j (x - z)‖ₑ :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ x, (closedBall z r).indicator
              (fun x => ENNReal.ofReal (cj ^ (d + 2) * M₀) * ENNReal.ofReal (q x - V x)) x :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (cj ^ (d + 2) * M₀) *
              ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) := by
            rw [lintegral_indicator measurableSet_closedBall,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (cj ^ (d + 2) * M₀) *
              (ENNReal.ofReal (ε * r ^ 2) * (ENNReal.ofReal (r ^ d) * c₁)) := by
            rw [← hvol]
            gcongr
        _ = ENNReal.ofReal (cj ^ (d + 2) * M₀ * (ε * r ^ 2) * r ^ d) * c₁ := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cj ^ (d + 2) * M₀ * (ε * r ^ 2)),
              ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ cj ^ (d + 2) * M₀)]
            ring
        _ = ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
            congr 2
            have hcr : cj * r = R := by rw [hr, hcj]; field_simp
            calc cj ^ (d + 2) * M₀ * (ε * r ^ 2) * r ^ d
                = M₀ * ε * (cj * r) ^ (d + 2) := by rw [mul_pow, pow_add, pow_add]; ring
              _ = M₀ * ε * R ^ (d + 2) := by rw [hcr]
    have hreal : |B j| ≤ M₀ * ε * R ^ (d + 2) * c₁.toReal := by
      have h1 : ENNReal.ofReal |B j| ≤ ENNReal.ofReal (M₀ * ε * R ^ (d + 2)) * c₁ := by
        rw [← Real.enorm_eq_ofReal_abs]
        exact hbound
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hc₁top),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
      exact h1
    rw [Real.dist_eq, sub_zero]
    calc |B j| ≤ M₀ * ε * R ^ (d + 2) * c₁.toReal := hreal
      _ = Λ * ε := by rw [hΛ]; ring
      _ = Λ * ε' / (2 * (Λ + 1)) := by rw [hε]; ring
      _ < ε' := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
  have hlim := hA.sub hBlim
  rw [sub_zero] at hlim
  exact hlim.congr fun j => (hdecomp j).symm

/-- **Almost every contact point is flat and a Lebesgue point of `H`**, so the Monge–Ampère
densities of the mollified potentials converge there to that of the obstacle. -/
theorem ae_tendsto_smoothDensity_mollified_contact (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : IsBoundedHessianDensityOn q H Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z ∂volume.restrict (contactBall Ω V q x₀ R),
      Tendsto (fun j => smoothDensity (mollified V x₀ R hR j) z) atTop (𝓝 (hessDensity H z)) := by
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall' hV hq.continuousOn
  set G : ComplexModel n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Ω : Set (ComplexModel n)).indicator q x -
      (Ω : Set (ComplexModel n)).indicator V x) with hG
  have hGm : Measurable G := by
    have hqm : Measurable ((Ω : Set (ComplexModel n)).indicator q) := by
      classical
      have h := hq.continuousOn.measurable_piecewise (continuousOn_const (c := (0 : ℝ)))
        Ω.isOpen.measurableSet
      convert h using 1
      ext x
      by_cases hx : x ∈ (Ω : Set (ComplexModel n)) <;> simp [Set.piecewise, hx]
    exact ENNReal.measurable_ofReal.comp
      (hqm.sub (LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn hV))
  have hGeq : ∀ x ∈ (Ω : Set (ComplexModel n)), G x = ENNReal.ofReal (q x - V x) := by
    intro x hx
    simp only [hG, indicator_of_mem hx]
  obtain ⟨M, hM0, hM⟩ := exists_setLIntegral_sub_le_of_contact hn hV hq hVq hball
  have hleb : ∀ᵐ z, ∀ t : Fin n × Fin n × Fin 4, z ∈ ball x₀ (2 * R) →
      Tendsto (fun j => leviForm (mollified q x₀ R hR j) z (polVec t.1 t.2.1 t.2.2)) atTop
        (𝓝 (hermQuad (H z) (polVec t.1 t.2.1 t.2.2))) :=
    ae_all_iff.mpr fun t => ae_tendsto_leviForm_mollified hq hR hball _
  filter_upwards [DensityPoint.ae_eventually_measure_closedBall_diff_le volume hSm,
    ae_restrict_mem hSm, ae_restrict_of_ae hleb] with z hdens hzS hzleb
  have hz2 : z ∈ ball x₀ (2 * R) := hzS.2
  have hzR : ball z R ⊆ ball x₀ (4 * R) :=
    ball_subset_ball' (by rw [mem_ball] at hz2; linarith)
  have hsub : ∀ y ∈ S, ∀ s : ℝ, 0 < s → dist y z + s < R →
      ∫⁻ x in closedBall y s, G x ∂volume ≤ ENNReal.ofReal (M * s ^ 2) * volume (closedBall y s) := by
    intro y hy s hs hys
    have hsub1 : closedBall y s ⊆ ball x₀ (4 * R) :=
      (closedBall_subset_ball' (by linarith)).trans hzR
    have hsubΩ : closedBall y s ⊆ Ω := hsub1.trans (ball_subset_closedBall.trans hball)
    rw [setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsubΩ hx)]
    exact hM y hy.1.1 hy.1.2 s hs hsub1
  have hflatG := DensityPoint.eventually_setLIntegral_le_of_density volume hGm hSm hzS hM0 hR
    hsub hdens
  have hflat : ∀ ε : ℝ, 0 < ε → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ x in closedBall z r, ENNReal.ofReal (q x - V x) ≤
        ENNReal.ofReal (ε * r ^ 2) * volume (closedBall z r) := by
    intro ε hε
    filter_upwards [hflatG ε hε, Ioo_mem_nhdsGT hR] with r hr hrR
    have hsubΩ : closedBall z r ⊆ Ω :=
      ((closedBall_subset_ball hrR.2).trans hzR).trans (ball_subset_closedBall.trans hball)
    rwa [setLIntegral_congr_fun measurableSet_closedBall fun x hx => hGeq x (hsubΩ hx)] at hr
  have hfun : (fun j => complexHessian (mollified V x₀ R hR j) z) =
      fun j => polarize (leviForm (mollified V x₀ R hR j) z) := by
    funext j
    exact complexHessian_eq_polarize
      ((contDiff_mollified hV hball hR j).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hH : Tendsto (fun j => complexHessian (mollified V x₀ R hR j) z) atTop (𝓝 (H z)) := by
    rw [hfun, ← polarize_hermQuad (hq.isHermitian z)]
    exact tendsto_polarize fun a b i =>
      tendsto_leviForm_mollified_of_flat hV hq.continuousOn hVq hR hball hz2 hflat _
        (hzleb ⟨a, b, i⟩ hz2)
  exact tendsto_hessDensity hH

/-- The bounded test-function inequality: for a bump `φ` supported in `B(x₀, 2R)`,
`∫_C φ (n!/πⁿ) det H ≤ ∫ φ d(ddᶜV)ⁿ` (Fatou along the mollified potentials). -/
theorem setLIntegral_contactBall_mul_le (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : IsBoundedHessianDensityOn q H Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {φ : ComplexModel n → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ ball x₀ (2 * R)) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ z in contactBall Ω V q x₀ R, ENNReal.ofReal (φ z * hessDensity H z) ≤
      ENNReal.ofReal (∫ z, φ z ∂canonicalBedfordTaylorMeasure Ω V hV) := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set U := innerBall x₀ R with hUdef
  set f := mollified V x₀ R hR with hf
  have hU : RelativelyCompactIn U Ω := by
    have hcl : closure (U : Set (ComplexModel n)) ⊆ closedBall x₀ (2 * R) :=
      closure_ball_subset_closedBall
    exact ⟨(isCompact_closedBall x₀ (2 * R)).of_isClosed_subset isClosed_closure hcl,
      hcl.trans ((closedBall_subset_closedBall (by linarith)).trans hball)⟩
  have hdec := isDecreasingApproximation_mollified hV hR hball
  have hweak := ((canonicalBedfordTaylorMeasure_spec Ω V hV).2.2.2 U hU).2 f hdec φ hφ hφc hφU
  have hlint : ∀ j, ENNReal.ofReal (∫ z, φ z ∂smoothMeasure U (f j) (hdec.1 j)) =
      ∫⁻ z in (U : Set (ComplexModel n)), ENNReal.ofReal (φ z * smoothDensity (f j) z) := by
    intro j
    obtain ⟨-, hint, heq⟩ :=
      FirstPass.MongeAmpere.smoothMeasure_test_integral (hdec.1 j) φ hφ hφc hφU
    rw [heq, ofReal_integral_eq_lintegral_ofReal hint]
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with z hz
    exact mul_nonneg (hφ0 z) (smoothDensity_nonneg ((hdec.1 j).2.2 z hz))
  have hlim : Tendsto (fun j => ∫⁻ z in (U : Set (ComplexModel n)),
      ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop
      (𝓝 (ENNReal.ofReal (∫ z, φ z ∂μ))) := by
    simp_rw [← hlint]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hweak
  have hmeas : ∀ j, AEMeasurable (fun z => ENNReal.ofReal (φ z * smoothDensity (f j) z))
      (volume.restrict (contactBall Ω V q x₀ R)) := by
    intro j
    have hc : Continuous (smoothDensity (f j)) :=
      continuousOn_univ.mp (SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_smoothDensity
        isOpen_univ (contDiff_mollified hV hball hR j).contDiffOn)
    exact (ENNReal.continuous_ofReal.comp (hφ.mul hc)).measurable.aemeasurable
  have hSU : contactBall Ω V q x₀ R ⊆ U := inter_subset_right
  calc ∫⁻ z in contactBall Ω V q x₀ R, ENNReal.ofReal (φ z * hessDensity H z)
      = ∫⁻ z in contactBall Ω V q x₀ R,
          liminf (fun j => ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_tendsto_smoothDensity_mollified_contact hn hV hq hVq hR hball] with z hz
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hz.const_mul (φ z))).liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ z in contactBall Ω V q x₀ R,
          ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun j => ∫⁻ z in (U : Set (ComplexModel n)),
          ENNReal.ofReal (φ z * smoothDensity (f j) z)) atTop := by
        refine liminf_le_liminf (Eventually.of_forall fun j => lintegral_mono_set hSU) ?_ ?_
        · isBoundedDefault
        · isBoundedDefault
    _ = ENNReal.ofReal (∫ z, φ z ∂μ) := hlim.liminf_eq

/-- `ofReal (∫ b dμ) ≤ μ(B̄(y, δ + r))` for the bump `b` of radii `r < δ + r`. -/
theorem ofReal_integral_bump_le (μ : Measure (ComplexModel n)) {y : ComplexModel n}
    (b : ContDiffBump y) :
    ENNReal.ofReal (∫ z, b z ∂μ) ≤ μ (closedBall y b.rOut) := by
  by_cases hi : Integrable (b : ComplexModel n → ℝ) μ
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => b.nonneg),
      ← lintegral_indicator_one measurableSet_closedBall]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ closedBall y b.rOut
    · rw [indicator_of_mem hz, Pi.one_apply, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal b.le_one
    · have hz' : z ∉ tsupport (b : ComplexModel n → ℝ) := by rwa [b.tsupport_eq]
      rw [image_eq_zero_of_notMem_tsupport hz', ENNReal.ofReal_zero]
      simp
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    simp

/-- **The contact bound on closed balls.**  For `B̄(y, 2r) ⊆ B(x₀, 2R)`,
`∫_{C ∩ B̄(y, r)} (n!/πⁿ) det H ≤ (ddᶜV)ⁿ(B̄(y, r))`. -/
theorem setLIntegral_contactBall_closedBall_le (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : IsBoundedHessianDensityOn q H Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {y : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hyr : closedBall y (2 * r) ⊆ ball x₀ (2 * R)) :
    ∫⁻ z in contactBall Ω V q x₀ R ∩ closedBall y r, ENNReal.ofReal (hessDensity H z) ≤
      canonicalBedfordTaylorMeasure Ω V hV (closedBall y r) := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall' hV hq.continuousOn
  have hBΩ : closedBall y (2 * r) ⊆ Ω :=
    hyr.trans (ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans
      hball))
  have hδ : ∀ δ : ℝ, 0 < δ → δ ≤ r →
      ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (hessDensity H z) ≤
        μ (closedBall y (δ + r)) := by
    intro δ hδ0 hδr
    let b : ContDiffBump y := ⟨r, δ + r, hr, by linarith⟩
    have hbc : Continuous (b : ComplexModel n → ℝ) := b.continuous
    have hbs : HasCompactSupport (b : ComplexModel n → ℝ) := b.hasCompactSupport
    have hbt : tsupport (b : ComplexModel n → ℝ) = closedBall y (δ + r) := b.tsupport_eq
    have hbU : tsupport (b : ComplexModel n → ℝ) ⊆ ball x₀ (2 * R) := by
      rw [hbt]
      exact (closedBall_subset_closedBall (by linarith)).trans hyr
    have hkey := setLIntegral_contactBall_mul_le hn hV hq hVq hR hball hbc hbs hbU fun _ => b.nonneg
    calc ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (hessDensity H z)
        = ∫⁻ z in S ∩ closedBall y r, ENNReal.ofReal (b z * hessDensity H z) := by
          refine setLIntegral_congr_fun (hSm.inter measurableSet_closedBall) fun z hz => ?_
          rw [b.one_of_mem_closedBall hz.2, one_mul]
      _ ≤ ∫⁻ z in S, ENNReal.ofReal (b z * hessDensity H z) :=
          lintegral_mono_set inter_subset_left
      _ ≤ ENNReal.ofReal (∫ z, b z ∂μ) := hkey
      _ ≤ μ (closedBall y (δ + r)) := ofReal_integral_bump_le μ b
  have hfin : μ (Metric.cthickening r (closedBall y r)) ≠ ⊤ := by
    rw [cthickening_closedBall hr.le hr.le]
    exact (canonicalBedfordTaylorMeasure_finiteOnCompacts hV (isCompact_closedBall _ _)
      (by rw [show r + r = 2 * r by ring]; exact hBΩ)).ne
  have htend := (tendsto_measure_cthickening_of_isClosed ⟨r, hr, hfin⟩ isClosed_closedBall).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine ge_of_tendsto htend ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with δ hδm
  rw [cthickening_closedBall hδm.1.le hr.le]
  exact hδ δ hδm.1 hδm.2

/-- **The contact bound for bounded potentials.**  Let `V ≤ q` on `Ω`, `V` locally bounded
plurisubharmonic, `q` continuous with bounded Hessian density `H`, and `B̄(x₀, 4R) ⊆ Ω`.  For every
`T ⊆ {V = q} ∩ B(x₀, R)`, `∫_T (n!/πⁿ) det H ≤ (ddᶜV)ⁿ(T)`. -/
theorem canonicalBedfordTaylorMeasure_contact_ge (hn : 0 < n) (hV : IsLocallyBoundedPshOn Ω V)
    (hq : IsBoundedHessianDensityOn q H Ω) (hVq : ∀ z ∈ Ω, V z ≤ q z) (hR : 0 < R)
    (hball : closedBall x₀ (4 * R) ⊆ Ω) {T : Set (ComplexModel n)}
    (hT : T ⊆ {z | z ∈ Ω ∧ V z = q z} ∩ ball x₀ R) :
    ∫⁻ z in T, ENNReal.ofReal (hessDensity H z) ≤ canonicalBedfordTaylorMeasure Ω V hV T := by
  set μ := canonicalBedfordTaylorMeasure Ω V hV with hμ
  set S := contactBall Ω V q x₀ R with hS
  have hSm : MeasurableSet S := measurableSet_contactBall' hV hq.continuousOn
  have hTS : T ⊆ S := fun z hz =>
    ⟨(hT hz).1, ball_subset_ball (by linarith) (hT hz).2⟩
  set ρ := (volume.restrict S).withDensity fun z => ENNReal.ofReal (hessDensity H z) with hρ
  have hρac : ρ ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have h2R : closedBall x₀ (2 * R) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  set ν := μ.restrict (closedBall x₀ (2 * R)) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (canonicalBedfordTaylorMeasure_finiteOnCompacts hV (isCompact_closedBall _ _) h2R).ne
  have key := (Besicovitch.vitaliFamily (volume : Measure (ComplexModel n))).measure_le_of_frequently_le
    ν hρac T ?_
  · calc ∫⁻ z in T, ENNReal.ofReal (hessDensity H z) = ρ T := by
          rw [hρ, withDensity_apply', Measure.restrict_restrict' hSm, inter_eq_left.mpr hTS]
      _ ≤ ν T := key
      _ ≤ μ T := Measure.restrict_apply_le _ _
  · intro y hy
    rw [VitaliFamily.frequently_filterAt_iff]
    intro ε hε
    have hyR : dist y x₀ < R := (hT hy).2
    set r := min ε (R / 2) with hr
    have hr0 : 0 < r := lt_min hε (by positivity)
    have hrε : r ≤ ε := min_le_left _ _
    have hrR : r ≤ R / 2 := min_le_right _ _
    have hyr : closedBall y (2 * r) ⊆ ball x₀ (2 * R) :=
      closedBall_subset_ball' (by linarith)
    refine ⟨closedBall y r, ⟨r, hr0, rfl⟩, closedBall_subset_closedBall hrε, ?_⟩
    have hsub : closedBall y r ⊆ closedBall x₀ (2 * R) :=
      (closedBall_subset_closedBall (by linarith)).trans (hyr.trans ball_subset_closedBall)
    rw [hρ, withDensity_apply _ measurableSet_closedBall, Measure.restrict_restrict
      measurableSet_closedBall, inter_comm, hν, Measure.restrict_apply measurableSet_closedBall,
      inter_eq_left.mpr hsub]
    exact setLIntegral_contactBall_closedBall_le hn hV hq hVq hR hball hr0 hyr

end Bounded

/-! ### Potentials with poles -/

/-- **The local contact bound "`≥`"** for an obstacle with a bounded Hessian density.  Let
`U ≤ q` on `Ω`, with `U` plurisubharmonic (possibly with poles) and `q` continuous on `Ω` with
bounded Hessian density `H` (not necessarily plurisubharmonic), and `B̄(x₀, 5R) ⊆ Ω`.  For every
`T ⊆ {U = q} ∩ B(x₀, R)`, `∫_T (n!/πⁿ) det H ≤ ⟨(ddᶜU)ⁿ⟩(T)`. -/
theorem truncationLimitMeasure_contact_ge (hn : 0 < n) {Ω : Opens (ComplexModel n)}
    {U : ComplexModel n → EReal} (hU : PlurisubharmonicOn U Ω) {q : ComplexModel n → ℝ}
    {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} (hq : IsBoundedHessianDensityOn q H Ω)
    (hUq : ∀ z ∈ Ω, U z ≤ q z) {x₀ : ComplexModel n} {R : ℝ}
    (hR : 0 < R) (hball : closedBall x₀ (5 * R) ⊆ Ω) {T : Set (ComplexModel n)}
    (hT : T ⊆ {z | z ∈ Ω ∧ U z = q z} ∩ ball x₀ R) :
    ∫⁻ z in T, ENNReal.ofReal (hessDensity H z) ≤ truncationLimitMeasure Ω U hU T := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall x₀ (5 * R)).exists_bound_of_continuousOn
    (hq.continuousOn.mono hball)
  set k : ℕ := ⌈B⌉₊ + 1 with hk
  have hkB : B < k := by
    rw [hk]; push_cast
    linarith [Nat.le_ceil B]
  have hqk : ∀ z ∈ closedBall x₀ (5 * R), -(k : ℝ) < q z := by
    intro z hz
    have := hB z hz
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (q z)]
  let Ω' : Opens (ComplexModel n) := ⟨ball x₀ (5 * R), isOpen_ball⟩
  have hΩ' : Ω' ≤ Ω := ball_subset_closedBall.trans hball
  have hVk : IsLocallyBoundedPshOn Ω (truncationReal U k) := truncationReal_isLocallyBoundedPshOn hU k
  have hVk' : IsLocallyBoundedPshOn Ω' (truncationReal U k) :=
    BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hVk hΩ'
  have htr : ∀ z ∈ Ω, (truncationReal U k z : EReal) = max (U z) ((-(k : ℝ) : ℝ) : EReal) :=
    fun z hz => coe_truncationReal hU k hz
  have hVq : ∀ z ∈ Ω', truncationReal U k z ≤ q z := by
    intro z hz
    have h := htr z (hΩ' hz)
    have hle : max (U z) ((-(k : ℝ) : ℝ) : EReal) ≤ (q z : EReal) :=
      max_le (hUq z (hΩ' hz)) (EReal.coe_le_coe_iff.mpr (hqk z (ball_subset_closedBall hz)).le)
    rw [← h] at hle
    exact EReal.coe_le_coe_iff.mp hle
  have hlocus : T ⊆ strictTruncationLocus Ω U k := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, hzB⟩ := hT hz
    refine ⟨hzΩ, ?_⟩
    rw [hzU]
    exact EReal.coe_lt_coe_iff.mpr (hqk z (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hzB))
  have hT' : T ⊆ {z | z ∈ Ω' ∧ truncationReal U k z = q z} ∩ ball x₀ R := by
    intro z hz
    obtain ⟨⟨hzΩ, hzU⟩, hzB⟩ := hT hz
    have hzΩ' : z ∈ Ω' := ball_subset_ball (by linarith) hzB
    refine ⟨⟨hzΩ', ?_⟩, hzB⟩
    have h := htr z hzΩ
    rw [hzU, max_eq_left (EReal.coe_le_coe_iff.mpr
      (hqk z (ball_subset_closedBall hzΩ')).le)] at h
    exact EReal.coe_eq_coe_iff.mp h
  have hball' : closedBall x₀ (4 * R) ⊆ Ω' := closedBall_subset_ball (by linarith)
  calc ∫⁻ z in T, ENNReal.ofReal (hessDensity H z)
      ≤ canonicalBedfordTaylorMeasure Ω' (truncationReal U k) hVk' T :=
        canonicalBedfordTaylorMeasure_contact_ge hn hVk' (hq.mono isOpen_ball hΩ') hVq hR hball' hT'
    _ = (canonicalBedfordTaylorMeasure Ω (truncationReal U k) hVk).restrict
          (Ω' : Set (ComplexModel n)) T := by
        rw [canonicalBedfordTaylorMeasure_restrict hΩ' hVk hVk']
    _ ≤ canonicalBedfordTaylorMeasure Ω (truncationReal U k) hVk T :=
        Measure.restrict_apply_le _ _
    _ = truncationMeasure Ω U hU k T := by
        rw [truncationMeasure, Measure.restrict_eq_self _ hlocus]
    _ = (truncationLimitMeasure Ω U hU).restrict (strictTruncationLocus Ω U k) T := by
        rw [truncationLimitMeasure_restrict_strictLocus]
    _ ≤ truncationLimitMeasure Ω U hU T := Measure.restrict_apply_le _ _


/-! ### The density formula for plurisubharmonic functions with a bounded Hessian density -/

section Density

variable {Ω : Opens (ComplexModel n)} {Q : ComplexModel n → ℝ}
  {H : ComplexModel n → Matrix (Fin n) (Fin n) ℂ} {x₀ : ComplexModel n} {R : ℝ}

/-- The Hessian density of a plurisubharmonic function has nonnegative determinant almost
everywhere (limit of the nonnegative densities of its smooth mollifications). -/
theorem ae_hessDensity_nonneg_of_psh (hQ : IsLocallyBoundedPshOn Ω Q)
    (hd : IsBoundedHessianDensityOn Q H Ω) (hR : 0 < R) (hball : closedBall x₀ (4 * R) ⊆ Ω) :
    ∀ᵐ z, z ∈ ball x₀ (2 * R) → 0 ≤ hessDensity H z := by
  have hdec := isDecreasingApproximation_mollified hQ hR hball
  filter_upwards [ae_tendsto_smoothDensity_mollified_of_density hd hR hball] with z hz hz2
  exact ge_of_tendsto (hz hz2)
    (Eventually.of_forall fun j => smoothDensity_nonneg ((hdec.1 j).2.2 z hz2))

/-- **Test integrals of the Bedford–Taylor measure** of a continuous psh function with bounded
Hessian density: `∫ φ d(ddᶜQ)ⁿ = ∫ φ (n!/πⁿ) det H` (dominated convergence along the
mollifications). -/
theorem integral_canonicalBedfordTaylorMeasure_eq (hQ : IsLocallyBoundedPshOn Ω Q)
    (hd : IsBoundedHessianDensityOn Q H Ω) (hR : 0 < R) (hball : closedBall x₀ (4 * R) ⊆ Ω)
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ ball x₀ (2 * R)) :
    ∫ z, φ z ∂canonicalBedfordTaylorMeasure Ω Q hQ =
      ∫ z in ball x₀ (2 * R), φ z * hessDensity H z := by
  set U := innerBall x₀ R with hUdef
  set f := mollified Q x₀ R hR with hf
  have hU : RelativelyCompactIn U Ω := by
    have hcl : closure (U : Set (ComplexModel n)) ⊆ closedBall x₀ (2 * R) :=
      closure_ball_subset_closedBall
    exact ⟨(isCompact_closedBall x₀ (2 * R)).of_isClosed_subset isClosed_closure hcl,
      hcl.trans ((closedBall_subset_closedBall (by linarith)).trans hball)⟩
  have hdec := isDecreasingApproximation_mollified hQ hR hball
  have hweak := ((canonicalBedfordTaylorMeasure_spec Ω Q hQ).2.2.2 U hU).2 f hdec φ hφ hφc hφU
  have heq : ∀ j, ∫ z, φ z ∂smoothMeasure U (f j) (hdec.1 j) =
      ∫ z in ball x₀ (2 * R), φ z * smoothDensity (f j) z := fun j =>
    (FirstPass.MongeAmpere.smoothMeasure_test_integral (hdec.1 j) φ hφ hφc hφU).2.2
  have hlim2 : Tendsto (fun j => ∫ z in ball x₀ (2 * R), φ z * smoothDensity (f j) z) atTop
      (𝓝 (∫ z in ball x₀ (2 * R), φ z * hessDensity H z)) := by
    obtain ⟨C, hC0, hC⟩ := exists_norm_complexHessian_mollified_le hd hR hball
    obtain ⟨Bφ, hBφ⟩ := hφc.exists_bound_of_continuous hφ
    set D : ℝ := (n.factorial : ℝ) / Real.pi ^ n * ((n.factorial : ℝ) * C ^ n) with hD
    refine tendsto_integral_of_dominated_convergence (fun _ => Bφ * D) (fun j => ?_)
      (integrableOn_const measure_ball_lt_top.ne) (fun j => ?_) ?_
    · have hc : Continuous (smoothDensity (f j)) :=
        continuousOn_univ.mp
          (SGPT.Okounkov.TranscendentalWN.EnvelopeLocal.continuousOn_smoothDensity isOpen_univ
            (contDiff_mollified hQ hball hR j).contDiffOn)
      exact (hφ.mul hc).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul (hBφ z) ?_ (abs_nonneg _) ((norm_nonneg _).trans (hBφ z))
      rw [smoothDensity]
      exact abs_hessDensity_le (hC j z hz)
    · filter_upwards [ae_restrict_of_ae (ae_tendsto_smoothDensity_mollified_of_density hd hR hball),
        ae_restrict_mem measurableSet_ball] with z hz hzU
      exact (hz hzU).const_mul (φ z)
  exact tendsto_nhds_unique hweak (hlim2.congr fun j => (heq j).symm)

/-- `μ(B̄(y, r)) ≤ ofReal (∫ b dμ)` for a bump `b` equal to `1` on `B̄(y, r)`. -/
theorem measure_closedBall_le_ofReal_integral_bump (μ : Measure (ComplexModel n)) {y : ComplexModel n}
    (b : ContDiffBump y) (hb : Integrable (b : ComplexModel n → ℝ) μ) :
    μ (closedBall y b.rIn) ≤ ENNReal.ofReal (∫ z, b z ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hb (Eventually.of_forall fun _ => b.nonneg),
    ← lintegral_indicator_one measurableSet_closedBall]
  refine lintegral_mono fun z => ?_
  by_cases hz : z ∈ closedBall y b.rIn
  · rw [indicator_of_mem hz, Pi.one_apply, b.one_of_mem_closedBall hz, ENNReal.ofReal_one]
  · rw [indicator_of_notMem hz]
    simp

/-- **The density formula.**  Let `Q` be continuous and plurisubharmonic on `Ω`, with bounded Hessian
density `H`, and `B̄(x₀, 4R) ⊆ Ω`.  On `B(x₀, R)` the Bedford–Taylor measure of `Q` is
`(n!/πⁿ) det H dV`. -/
theorem canonicalBedfordTaylorMeasure_eq_density (hn : 0 < n) (hQ : IsLocallyBoundedPshOn Ω Q)
    (hd : IsBoundedHessianDensityOn Q H Ω) (hR : 0 < R) (hball : closedBall x₀ (4 * R) ⊆ Ω)
    {T : Set (ComplexModel n)} (hT : T ⊆ ball x₀ R) :
    canonicalBedfordTaylorMeasure Ω Q hQ T = ∫⁻ z in T, ENNReal.ofReal (hessDensity H z) := by
  set μ := canonicalBedfordTaylorMeasure Ω Q hQ with hμ
  have h2R : closedBall x₀ (2 * R) ⊆ Ω := (closedBall_subset_closedBall (by linarith)).trans hball
  refine le_antisymm ?_ ?_
  · -- `(ddᶜQ)ⁿ ≤ ρ`: Besicovitch–Vitali for the finite measure `(ddᶜQ)ⁿ` restricted to `B̄(x₀, 2R)`
    set ν := μ.restrict (closedBall x₀ (2 * R)) with hν
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
      (canonicalBedfordTaylorMeasure_finiteOnCompacts hQ (isCompact_closedBall _ _) h2R).ne
    set ρ := (volume.restrict (ball x₀ (2 * R))).withDensity
      (fun z => ENNReal.ofReal (hessDensity H z)) with hρ
    obtain ⟨C, hC⟩ := hd.bounded (closedBall x₀ (2 * R)) (isCompact_closedBall _ _) h2R
    set D : ℝ := (n.factorial : ℝ) / Real.pi ^ n * ((n.factorial : ℝ) * C ^ n) with hD
    have : IsFiniteMeasure ρ := by
      refine ⟨?_⟩
      rw [hρ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      calc ∫⁻ z in ball x₀ (2 * R), ENNReal.ofReal (hessDensity H z)
          ≤ ∫⁻ _z in ball x₀ (2 * R), ENNReal.ofReal D := by
            refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
            have hC' : ∀ᵐ z ∂volume, z ∈ closedBall x₀ (2 * R) → ∀ i j, ‖H z i j‖ ≤ C :=
              (ae_restrict_iff' measurableSet_closedBall).mp hC
            filter_upwards [hC'] with z hz hzb
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
              (abs_hessDensity_le (hz (ball_subset_closedBall hzb))))
        _ = ENNReal.ofReal D * volume (ball x₀ (2 * R)) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
    have hnn := ae_hessDensity_nonneg_of_psh hQ hd hR hball
    have key := (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le (ρ := ν) ρ
      Measure.AbsolutelyContinuous.rfl T ?_
    · calc μ T = ν T := by
            rw [hν, Measure.restrict_eq_self _ (hT.trans (ball_subset_closedBall.trans
              (closedBall_subset_closedBall (by linarith))))]
        _ ≤ ρ T := key
        _ = ∫⁻ z in T, ENNReal.ofReal (hessDensity H z) := by
            rw [hρ, withDensity_apply', Measure.restrict_restrict' measurableSet_ball,
              inter_eq_left.mpr (hT.trans (ball_subset_ball (by linarith)))]
    · intro y hy
      rw [VitaliFamily.frequently_filterAt_iff]
      intro ε hε
      have hyR : dist y x₀ < R := hT hy
      set r := min ε (R / 2) with hr
      have hr0 : 0 < r := lt_min hε (by positivity)
      have hrε : r ≤ ε := min_le_left _ _
      have hrR : r ≤ R / 2 := min_le_right _ _
      have hyr : closedBall y (2 * r) ⊆ ball x₀ (2 * R) :=
        closedBall_subset_ball' (by linarith)
      refine ⟨closedBall y r, ⟨r, hr0, rfl⟩, closedBall_subset_closedBall hrε, ?_⟩
      have hsub : closedBall y r ⊆ closedBall x₀ (2 * R) :=
        (closedBall_subset_closedBall (by linarith)).trans (hyr.trans ball_subset_closedBall)
      rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub]
      have hδ : ∀ δ : ℝ, 0 < δ → δ ≤ r → μ (closedBall y r) ≤ ρ (closedBall y (δ + r)) := by
        intro δ hδ0 hδr
        let b : ContDiffBump y := ⟨r, δ + r, hr0, by linarith⟩
        have hbt : tsupport (b : ComplexModel n → ℝ) = closedBall y (δ + r) := b.tsupport_eq
        have hbU : tsupport (b : ComplexModel n → ℝ) ⊆ ball x₀ (2 * R) := by
          rw [hbt]
          exact (closedBall_subset_closedBall (by linarith)).trans hyr
        have hbint : Integrable (b : ComplexModel n → ℝ) μ := by
          have hfin := canonicalBedfordTaylorMeasure_finiteOnCompacts hQ
            (isCompact_closedBall y (δ + r))
            ((closedBall_subset_closedBall (by linarith)).trans
              (hyr.trans (ball_subset_closedBall.trans h2R)))
          have h1 : IntegrableOn (b : ComplexModel n → ℝ) (closedBall y (δ + r)) μ :=
            Measure.integrableOn_of_bounded hfin.ne b.continuous.aestronglyMeasurable
              (M := 1) (Eventually.of_forall fun z => by
                rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]; exact b.le_one)
          rw [← hbt] at h1
          exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp h1
        have hbintU : IntegrableOn (fun z => b z * hessDensity H z) (ball x₀ (2 * R)) := by
          have h1 := (hd.integrable_hermQuad_mul b.continuous b.hasCompactSupport
            (hbU.trans (ball_subset_closedBall.trans h2R)) 0)
          refine Measure.integrableOn_of_bounded measure_ball_lt_top.ne
            ((b.continuous.aestronglyMeasurable).mul
              (measurable_hessDensity hd.measurable).aestronglyMeasurable) (M := D) ?_
          have hC' : ∀ᵐ z ∂volume, z ∈ closedBall x₀ (2 * R) → ∀ i j, ‖H z i j‖ ≤ C :=
            (ae_restrict_iff' measurableSet_closedBall).mp hC
          filter_upwards [ae_restrict_of_ae hC', ae_restrict_mem measurableSet_ball] with z hz hzb
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
          calc b z * |hessDensity H z| ≤ 1 * D :=
                mul_le_mul b.le_one (abs_hessDensity_le (hz (ball_subset_closedBall hzb)))
                  (abs_nonneg _) zero_le_one
            _ = D := one_mul D
        calc μ (closedBall y r) ≤ ENNReal.ofReal (∫ z, b z ∂μ) :=
              measure_closedBall_le_ofReal_integral_bump μ b hbint
          _ = ENNReal.ofReal (∫ z in ball x₀ (2 * R), b z * hessDensity H z) := by
              rw [integral_canonicalBedfordTaylorMeasure_eq hQ hd hR hball b.continuous
                b.hasCompactSupport hbU]
          _ = ∫⁻ z in ball x₀ (2 * R), ENNReal.ofReal (b z * hessDensity H z) := by
              rw [ofReal_integral_eq_lintegral_ofReal hbintU]
              filter_upwards [ae_restrict_of_ae hnn, ae_restrict_mem measurableSet_ball] with z hz hzb
              exact mul_nonneg b.nonneg (hz hzb)
          _ ≤ ∫⁻ z in ball x₀ (2 * R),
                (closedBall y (δ + r)).indicator (fun z => ENNReal.ofReal (hessDensity H z)) z := by
              refine lintegral_mono fun z => ?_
              by_cases hz : z ∈ closedBall y (δ + r)
              · rw [indicator_of_mem hz]
                rcases le_total 0 (hessDensity H z) with h0 | h0
                · exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left h0 b.le_one)
                · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos b.nonneg h0)]
                  simp
              · have hz' : z ∉ tsupport (b : ComplexModel n → ℝ) := by rwa [hbt]
                rw [image_eq_zero_of_notMem_tsupport hz', zero_mul, ENNReal.ofReal_zero]
                simp
          _ = ρ (closedBall y (δ + r)) := by
              rw [lintegral_indicator measurableSet_closedBall, hρ,
                withDensity_apply _ measurableSet_closedBall, Measure.restrict_restrict
                measurableSet_closedBall]
      have hfin : ρ (Metric.cthickening r (closedBall y r)) ≠ ⊤ := measure_ne_top _ _
      have htend := (tendsto_measure_cthickening_of_isClosed ⟨r, hr0, hfin⟩
        isClosed_closedBall).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      refine ge_of_tendsto htend ?_
      filter_upwards [Ioc_mem_nhdsGT hr0] with δ hδm
      rw [cthickening_closedBall hδm.1.le hr0.le]
      exact hδ δ hδm.1 hδm.2
  · -- `ρ ≤ (ddᶜQ)ⁿ`: the contact inequality with `V = q = Q`
    refine canonicalBedfordTaylorMeasure_contact_ge hn hQ hd (fun _ _ => le_rfl) hR hball ?_
    intro z hz
    exact ⟨⟨h2R (ball_subset_closedBall (ball_subset_ball (by linarith) (hT hz))), rfl⟩, hT hz⟩

end Density

end SGPT.Envelopes.DNTC11
