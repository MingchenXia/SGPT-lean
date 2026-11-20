import SGPT.Okounkov.TranscendentalWNLegendreApprox
import SGPT.Okounkov.TranscendentalWNLegendreSmooth
import SGPT.Foundations.Analysis.Pending.ConvexExhaustion
import SGPT.Foundations.Analysis.Pending.PshConvexCone

/-!
# The smooth strictly convex approximants of `u` (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:approx` (second part).  Let `B ⊆ ℂᴺ` be open and
preconnected, `u` circle-invariant psh on `B × ℂ*` with `û_λ ≡ -∞` on `B` for `λ ∉ [a, b]` and
`|û_λ| ≤ C` on `B` for `λ ∈ [a, b]` (`IsBoundedLegendreData B u a b C`).  With
`R_δ = Ũ * ρ_δ` the radial regularizations of `Ũ(z, ζ) = u(z, e^{ζ/2})` (functions of
`(z, Re ζ)`, `regularizedProfile`), the model profile
`ψ(y) = (a + b)/2 y + (b - a)/2 √(1 + y²)` (`legendreModelProfile`), the constant
`c = C + 2 max(|a|, |b|) + 1` and the scales `s_k = δ₀/(k + 1)`, `0 < δ₀ ≤ 1/2`, put

  `F_k(z, y) = (1 - s_k) R_{s_k}(z, y) + s_k (c + ψ(y))`   (`approxProfile`).

On `D = B'_{2δ₀} = {z : ∃ δ' > 2δ₀, ball z δ' ⊆ B}`:

* `F_k` satisfies the hypotheses of the smooth case `IsSmoothLegendreData D F_k a b`
  (`isSmoothLegendreData_approxProfile`) and `(z, τ) ↦ F_k(z, log |τ|²)` is psh on `D × ℂ*`
  (`plurisubharmonicOn_approxProfile`);
* `-C + max(ay, by) ≤ F_k(z, y) ≤ c + (b - a)/2 + max(ay, by)` (`approxProfile_bounds`);
* `F_{k+1} ≤ F_k`, `Ũ ≤ F_k` and `F_k → Ũ` pointwise (`approxProfile_succ_le`,
  `expPullback_le_approxProfile`, `tendsto_approxProfile`);
* the smooth partial Legendre transforms `legendreValue F_k · λ` decrease to `û_λ` for
  `λ ∈ (a, b)` and satisfy `-C ≤ legendreValue F_k z λ ≤ c + (b - a)/2`
  (`antitone_legendreValue_approxProfile`, `tendsto_legendreValue_approxProfile`,
  `legendreValue_approxProfile_bounds`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality
  SGPT.Foundations.Analysis.Pending.PshRadialRegularization
  SGPT.Foundations.Analysis.Pending.MixedDensityRankOneSlot

/-! ### The model profile `ψ` -/

section Profile

/-- `ψ(y) = (a + b)/2 y + (b - a)/2 √(1 + y²)`. -/
def legendreModelProfile (a b y : ℝ) : ℝ :=
  (a + b) / 2 * y + (b - a) / 2 * Real.sqrt (1 + y ^ 2)

/-- `ψ'(y) = (a + b)/2 + (b - a)/2 · y / √(1 + y²)`. -/
def legendreModelSlope (a b y : ℝ) : ℝ :=
  (a + b) / 2 + (b - a) / 2 * (y / Real.sqrt (1 + y ^ 2))

/-- `ψ''(y) = (b - a)/2 · 1 / ((1 + y²) √(1 + y²))`. -/
def legendreModelCurv (a b y : ℝ) : ℝ :=
  (b - a) / 2 * (1 / ((1 + y ^ 2) * Real.sqrt (1 + y ^ 2)))

theorem one_add_sq_pos (y : ℝ) : 0 < 1 + y ^ 2 := by positivity

theorem sqrt_one_add_sq_pos (y : ℝ) : 0 < Real.sqrt (1 + y ^ 2) :=
  Real.sqrt_pos.mpr (one_add_sq_pos y)

theorem hasDerivAt_sqrt_one_add_sq (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2)) (y / Real.sqrt (1 + y ^ 2)) y := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).const_add 1
  have h2 := h1.sqrt (one_add_sq_pos y).ne'
  convert h2 using 1
  field_simp

theorem hasDerivAt_legendreModelProfile (a b y : ℝ) :
    HasDerivAt (legendreModelProfile a b) (legendreModelSlope a b y) y := by
  have h : HasDerivAt (legendreModelProfile a b)
      ((a + b) / 2 * 1 + (b - a) / 2 * (y / Real.sqrt (1 + y ^ 2))) y :=
    ((hasDerivAt_id y).const_mul ((a + b) / 2)).add
      ((hasDerivAt_sqrt_one_add_sq y).const_mul ((b - a) / 2))
  exact h.congr_deriv (by rw [legendreModelSlope, mul_one])

theorem hasDerivAt_legendreModelSlope (a b y : ℝ) :
    HasDerivAt (legendreModelSlope a b) (legendreModelCurv a b y) y := by
  have hs := hasDerivAt_sqrt_one_add_sq y
  have hq : HasDerivAt (fun t : ℝ => t / Real.sqrt (1 + t ^ 2))
      ((1 * Real.sqrt (1 + y ^ 2) - y * (y / Real.sqrt (1 + y ^ 2))) /
        Real.sqrt (1 + y ^ 2) ^ 2) y :=
    (hasDerivAt_id y).div hs (sqrt_one_add_sq_pos y).ne'
  have h : HasDerivAt (legendreModelSlope a b) ((b - a) / 2 *
      ((1 * Real.sqrt (1 + y ^ 2) - y * (y / Real.sqrt (1 + y ^ 2))) /
        Real.sqrt (1 + y ^ 2) ^ 2)) y := (hq.const_mul ((b - a) / 2)).const_add ((a + b) / 2)
  refine h.congr_deriv ?_
  have hp := (sqrt_one_add_sq_pos y).ne'
  have hsq : Real.sqrt (1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (one_add_sq_pos y).le
  have hq1 : (1 + y ^ 2) ≠ 0 := (one_add_sq_pos y).ne'
  rw [hsq, legendreModelCurv]
  field_simp
  rw [hsq]
  ring

theorem legendreModelCurv_pos {a b : ℝ} (hab : a < b) (y : ℝ) : 0 < legendreModelCurv a b y := by
  have := sqrt_one_add_sq_pos y
  have := one_add_sq_pos y
  unfold legendreModelCurv
  have : 0 < (b - a) / 2 := by linarith
  positivity

theorem contDiff_legendreModelProfile (a b : ℝ) : ContDiff ℝ ∞ (legendreModelProfile a b) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.sqrt (1 + t ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t => (one_add_sq_pos t).ne'
  exact (contDiff_const.mul contDiff_id).add (contDiff_const.mul hs)

theorem max_mul_eq (a b y : ℝ) (hab : a ≤ b) :
    max (a * y) (b * y) = (a + b) / 2 * y + (b - a) / 2 * |y| := by
  rcases le_total 0 y with hy | hy
  · rw [max_eq_right (mul_le_mul_of_nonneg_right hab hy), abs_of_nonneg hy]
    ring
  · rw [max_eq_left (mul_le_mul_of_nonpos_right hab hy), abs_of_nonpos hy]
    ring

/-- `max(ay, by) ≤ ψ(y) ≤ max(ay, by) + (b - a)/2`. -/
theorem legendreModelProfile_bounds {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    max (a * y) (b * y) ≤ legendreModelProfile a b y ∧
      legendreModelProfile a b y ≤ max (a * y) (b * y) + (b - a) / 2 := by
  have h1 : |y| ≤ Real.sqrt (1 + y ^ 2) := Real.abs_le_sqrt (by linarith [sq_nonneg y])
  have h2 : Real.sqrt (1 + y ^ 2) ≤ |y| + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg y, sq_abs y]
  have hba : 0 ≤ (b - a) / 2 := by linarith
  rw [max_mul_eq a b y hab, legendreModelProfile]
  constructor
  · nlinarith
  · nlinarith

theorem strictMono_legendreModelSlope {a b : ℝ} (hab : a < b) :
    StrictMono (legendreModelSlope a b) :=
  strictMono_of_hasDerivAt_pos (fun y => hasDerivAt_legendreModelSlope a b y)
    (legendreModelCurv_pos hab)

theorem convexOn_legendreModelProfile {a b : ℝ} (hab : a < b) :
    ConvexOn ℝ univ (legendreModelProfile a b) := by
  have hd : ∀ y, deriv (legendreModelProfile a b) y = legendreModelSlope a b y :=
    fun y => (hasDerivAt_legendreModelProfile a b y).deriv
  refine MonotoneOn.convexOn_of_deriv convex_univ
    (contDiff_legendreModelProfile a b).continuous.continuousOn
    (fun y _ => (hasDerivAt_legendreModelProfile a b y).differentiableAt.differentiableWithinAt) ?_
  intro x _ y _ hxy
  rw [hd, hd]
  exact (strictMono_legendreModelSlope hab).monotone hxy

theorem abs_max_mul_sub_max_mul_le (a b y₁ y₂ : ℝ) :
    |max (a * y₁) (b * y₁) - max (a * y₂) (b * y₂)| ≤ max |a| |b| * |y₁ - y₂| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  · rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

end Profile

/-! ### Descent of functions of `(z, Re ζ)` to `(z, log |τ|²)` -/

section Descent

variable {N : ℕ}

/-- **Descent**: if `(z, ζ) ↦ g(z, Re ζ)` is psh on `D × ℂ`, then `(z, τ) ↦ g(z, log |τ|²)` is psh
on `D × ℂ*` (local holomorphic branches `2 log τ`, `2 log (-τ)`). -/
theorem plurisubharmonicOn_descend_of_re {D : Set (ComplexModel N)} (hD : IsOpen D)
    {g : ComplexModel N × ℝ → ℝ}
    (hg : PlurisubharmonicOn (fun p : ComplexModel N × ℂ => (g (p.1, p.2.re) : EReal))
      (D ×ˢ univ)) :
    PlurisubharmonicOn (fun p : ComplexModel N × ℂ => (g (p.1, logNormSq p.2) : EReal))
      (D ×ˢ puncturedPlane) := by
  have hre₁ : ∀ τ : ℂ, τ ≠ 0 → (2 * Complex.log τ).re = logNormSq τ := by
    intro τ _
    rw [logNormSq, Real.log_pow]
    simp [Complex.log_re]
  have hre₂ : ∀ τ : ℂ, τ ≠ 0 → (2 * Complex.log (-τ)).re = logNormSq τ := by
    intro τ _
    rw [logNormSq, Real.log_pow]
    simp [Complex.log_re, norm_neg]
  intro p hp
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane (show p.2 ≠ 0 from hp.2) with hs | hs
  · set U₁ : Set (ComplexModel N × ℂ) := D ×ˢ Complex.slitPlane
    have hU₁ : IsOpen U₁ := hD.prod Complex.isOpen_slitPlane
    have hd : DifferentiableOn ℂ (fun p : ComplexModel N × ℂ => (p.1, 2 * Complex.log p.2)) U₁ := by
      intro x hx
      exact (differentiableAt_fst.prodMk ((differentiableAt_const _).mul
        ((Complex.differentiableAt_log hx.2).comp x differentiableAt_snd))).differentiableWithinAt
    have h1 := plurisubharmonicOn_comp_holomorphic_strip hU₁ hd
      (fun x hx => mk_mem_prod hx.1 (mem_univ _)) hg
    refine (h1 p ⟨hp.1, hs⟩).congr ?_
    filter_upwards [hU₁.mem_nhds ⟨hp.1, hs⟩] with x hx
    rw [hre₁ x.2 (Complex.slitPlane_ne_zero hx.2)]
  · set U₂ : Set (ComplexModel N × ℂ) := D ×ˢ {τ | -τ ∈ Complex.slitPlane}
    have hU₂ : IsOpen U₂ := hD.prod (Complex.isOpen_slitPlane.preimage continuous_neg)
    have hd : DifferentiableOn ℂ
        (fun p : ComplexModel N × ℂ => (p.1, 2 * Complex.log (-p.2))) U₂ := by
      intro x hx
      exact (differentiableAt_fst.prodMk ((differentiableAt_const _).mul
        ((Complex.differentiableAt_log hx.2).comp x differentiableAt_snd.neg))).differentiableWithinAt
    have h1 := plurisubharmonicOn_comp_holomorphic_strip hU₂ hd
      (fun x hx => mk_mem_prod hx.1 (mem_univ _)) hg
    refine (h1 p ⟨hp.1, hs⟩).congr ?_
    filter_upwards [hU₂.mem_nhds ⟨hp.1, hs⟩] with x hx
    have hx0 : x.2 ≠ 0 := fun h0 => Complex.slitPlane_ne_zero hx.2 (by simp [h0])
    rw [hre₂ x.2 hx0]

/-- `q ↦ c + ψ(Re q_last)` is psh on `ℂᴺ⁺¹` (a continuous convex function). -/
theorem plurisubharmonicOn_modelProfile_last {a b : ℝ} (hab : a < b) (c : ℝ) :
    PlurisubharmonicOn (fun q : ComplexModel (N + 1) =>
      ((c + legendreModelProfile a b (q (Fin.last N)).re : ℝ) : EReal)) univ := by
  set ℓ : ComplexModel (N + 1) →ₗ[ℝ] ℝ := Complex.reLm.comp
    (((EuclideanSpace.proj (Fin.last N) : ComplexModel (N + 1) →L[ℂ] ℂ) :
      ComplexModel (N + 1) →ₗ[ℂ] ℂ).restrictScalars ℝ) with hℓ
  have hconv : ConvexOn ℝ univ (fun q : ComplexModel (N + 1) =>
      c + legendreModelProfile a b (q (Fin.last N)).re) := by
    have h1 := (convexOn_legendreModelProfile hab).comp_linearMap ℓ
    rw [preimage_univ] at h1
    exact (convexOn_const c convex_univ).add h1
  have hcont : Continuous (fun q : ComplexModel (N + 1) =>
      c + legendreModelProfile a b (q (Fin.last N)).re) :=
    continuous_const.add ((contDiff_legendreModelProfile a b).continuous.comp
      (Complex.continuous_re.comp
        (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (N + 1)) (Fin.last N)).continuous))
  exact plurisubharmonicOn_of_convexOn isOpen_univ hconv hcont.continuousOn

end Descent

/-! ### The radial regularizations of `Ũ` -/

section Regularization

variable {N : ℕ} {B : Set (ComplexModel N)} {u : ComplexModel N → ℂ → EReal} {a b C : ℝ}

theorem innerSet_anti {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) : innerSet B δ₂ ⊆ innerSet B δ₁ :=
  fun _ ⟨δ', hδ', hball⟩ => ⟨δ', h.trans_lt hδ', hball⟩

theorem innerSet_subset {δ : ℝ} (hδ : 0 ≤ δ) : innerSet B δ ⊆ B :=
  fun _ ⟨_, hδ', hball⟩ => hball (mem_ball_self (hδ.trans_lt hδ'))

theorem stripModelEquiv_symm_mem_stripDomain {z : ComplexModel N} (hz : z ∈ B) (ζ : ℂ) :
    (stripModelEquiv N).symm (z, ζ) ∈ stripDomain B := by
  show (stripModelEquiv N ((stripModelEquiv N).symm (z, ζ))).1 ∈ B
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact hz

theorem isPreconnected_stripDomain (hB : IsPreconnected B) : IsPreconnected (stripDomain B) := by
  have h := (hB.prod (isPreconnected_univ (α := ℂ))).image _
    (stripModelEquiv N).symm.continuous.continuousOn
  convert h using 1
  ext q
  simp only [stripDomain, mem_ofPred_eq, mem_image, mem_prod, mem_univ, and_true]
  constructor
  · intro hq
    exact ⟨stripModelEquiv N q, hq, ContinuousLinearEquiv.symm_apply_apply _ _⟩
  · rintro ⟨p, hp, rfl⟩
    rwa [ContinuousLinearEquiv.apply_symm_apply]

/-- `max(|a|, |b|)`. -/
def slopeBound (a b : ℝ) : ℝ := max |a| |b|

theorem slopeBound_nonneg (a b : ℝ) : 0 ≤ slopeBound a b :=
  (abs_nonneg a).trans (le_max_left _ _)

/-- `c = C + 2 max(|a|, |b|) + 1`. -/
def approxConst (a b C : ℝ) : ℝ := C + 2 * slopeBound a b + 1

namespace IsBoundedLegendreData

variable (h : IsBoundedLegendreData B u a b C)
include h

omit h in
theorem expPullback_symm (z : ComplexModel N) (ζ : ℂ) :
    expPullback u ((stripModelEquiv N).symm (z, ζ)) = u z (Complex.exp (ζ / 2)) := by
  simp only [expPullback, ContinuousLinearEquiv.apply_symm_apply]

theorem nonneg_C {z : ComplexModel N} (hz : z ∈ B) : 0 ≤ C := by
  have h1 := h.lower a ⟨le_rfl, h.lt.le⟩ z hz
  have h2 := h.upper a ⟨le_rfl, h.lt.le⟩ z hz
  have := h1.trans h2
  rw [EReal.coe_le_coe_iff] at this
  linarith

theorem expPullback_ne_bot {q : ComplexModel (N + 1)} (hq : q ∈ stripDomain B) :
    expPullback u q ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h.expPullback_bounds hq).1

theorem expPullback_ne_top {q : ComplexModel (N + 1)} (hq : q ∈ stripDomain B) :
    expPullback u q ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (h.expPullback_bounds hq).2

theorem exists_expPullback_ne_bot {z : ComplexModel N} (hz : z ∈ B) :
    ∃ q ∈ stripDomain B, expPullback u q ≠ ⊥ :=
  ⟨_, stripModelEquiv_symm_mem_stripDomain hz 0,
    h.expPullback_ne_bot (stripModelEquiv_symm_mem_stripDomain hz 0)⟩

theorem plurisubharmonicOn_expPullback' : PlurisubharmonicOn (expPullback u) (stripDomain B) :=
  plurisubharmonicOn_expPullback h.isOpen h.psh

variable {ρ : ComplexModel (N + 1) → ℝ} (hρ : IsRadialKernel ρ) (hBc : IsPreconnected B)
include hρ hBc

/-- `-C + max(ay, by) ≤ R_δ(z, y)` (submean inequality). -/
theorem regularizedProfile_lower {δ : ℝ} (hδ : 0 < δ) {z : ComplexModel N}
    (hz : z ∈ innerSet B δ) (y : ℝ) :
    -C + max (a * y) (b * y) ≤ regularizedProfile ρ u δ (z, y) := by
  have hzB : z ∈ B := innerSet_subset hδ.le hz
  set x := (stripModelEquiv N).symm (z, (y : ℂ))
  have hx : x ∈ innerDomain (stripDomain B) δ := stripModelEquiv_symm_mem_innerDomain hz _
  have h1 := le_radialRegularization hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) hδ hx
  have h2 := (h.expPullback_bounds (stripModelEquiv_symm_mem_stripDomain hzB (y : ℂ))).1
  have hre : (stripModelEquiv N x).2.re = y := by simp [x]
  rw [hre] at h2
  exact EReal.coe_le_coe_iff.mp (h2.trans h1)

/-- `R_δ(z, y) ≤ c + max(ay, by)` for `δ ≤ 1` and `z ∈ B'_{2δ}`. -/
theorem regularizedProfile_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : ComplexModel N}
    (hz : z ∈ innerSet B (2 * δ)) (y : ℝ) :
    regularizedProfile ρ u δ (z, y) ≤ approxConst a b C + max (a * y) (b * y) := by
  obtain ⟨δ', hδ', hballz⟩ := hz
  have hzB : z ∈ B := hballz (mem_ball_self (by linarith))
  set x := (stripModelEquiv N).symm (z, (y : ℂ)) with hx_def
  have hxz : stripModelEquiv N x = (z, (y : ℂ)) := ContinuousLinearEquiv.apply_symm_apply _ _
  have hball : ball x (2 * δ) ⊆ stripDomain B := by
    intro q hq
    show (stripModelEquiv N q).1 ∈ B
    apply hballz
    rw [mem_ball, dist_eq_norm] at hq ⊢
    have := norm_stripModelEquiv_fst_le (q - x)
    rw [map_sub, Prod.fst_sub, hxz] at this
    linarith
  set M₀ := slopeBound a b
  set A : ℝ := C + max (a * y) (b * y) + 2 * M₀ * δ + 1
  have hA : ∀ q ∈ ball x (2 * δ), expPullback u q < (A : EReal) := by
    intro q hq
    have hb := (h.expPullback_bounds (hball hq)).2
    set yq := (stripModelEquiv N q).2.re
    have hyq : |yq - y| ≤ ‖q - x‖ := by
      have := abs_re_stripModelEquiv_snd_le (q - x)
      rwa [map_sub, Prod.snd_sub, hxz, Complex.sub_re, Complex.ofReal_re] at this
    have hq' : ‖q - x‖ < 2 * δ := by rwa [mem_ball, dist_eq_norm] at hq
    have hlip := abs_max_mul_sub_max_mul_le a b yq y
    have hM : max (a * yq) (b * yq) ≤ max (a * y) (b * y) + 2 * M₀ * δ := by
      have h1 : max |a| |b| * |yq - y| ≤ M₀ * (2 * δ) :=
        mul_le_mul_of_nonneg_left (hyq.trans hq'.le) (slopeBound_nonneg a b)
      have h2 := (abs_le.mp hlip).2
      linarith
    refine hb.trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
    linarith
  have h1 := radialRegularization_le hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) hball hA hδ (by linarith)
  have hM0 : 2 * M₀ * δ ≤ 2 * M₀ := by
    have := slopeBound_nonneg a b
    nlinarith
  calc regularizedProfile ρ u δ (z, y) = radialRegularization ρ (expPullback u) δ x := rfl
    _ ≤ A := h1
    _ ≤ approxConst a b C + max (a * y) (b * y) := by
        simp only [A, approxConst]
        linarith

omit h hρ hBc in
/-- The real-linear map `(z, y) ↦ (z, y)` into `ℂᴺ⁺¹` is smooth. -/
theorem contDiff_symm_ofReal' :
    ContDiff ℝ ∞ (fun p : ComplexModel N × ℝ => (stripModelEquiv N).symm (p.1, (p.2 : ℂ))) := by
  have hL : ContDiff ℝ ∞ (((stripModelEquiv N).symm : ComplexModel N × ℂ →L[ℂ]
      ComplexModel (N + 1)).restrictScalars ℝ) := ContinuousLinearMap.contDiff _
  have hp : ContDiff ℝ ∞ (fun p : ComplexModel N × ℝ => ((p.1, (p.2 : ℂ)) : ComplexModel N × ℂ)) :=
    contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  exact hL.comp hp

/-- `R_δ` is smooth on `B'_δ × ℝ`. -/
theorem contDiffOn_regularizedProfile {δ : ℝ} (hδ : 0 < δ) {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ B) :
    ContDiffOn ℝ ∞ (regularizedProfile ρ u δ) (innerSet B δ ×ˢ univ) := by
  have hR := contDiffOn_radialRegularization hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hz₀) hδ
  exact hR.comp contDiff_symm_ofReal'.contDiffOn
    (fun p hp => stripModelEquiv_symm_mem_innerDomain hp.1 _)

/-- `t ↦ R_δ(z, t)` is convex (a psh function of `Re ζ`). -/
theorem convexOn_regularizedProfile_slice {δ : ℝ} (hδ : 0 < δ) {z : ComplexModel N}
    (hz : z ∈ innerSet B δ) :
    ConvexOn ℝ univ (fun t : ℝ => regularizedProfile ρ u δ (z, t)) := by
  have hzB : z ∈ B := innerSet_subset hδ.le hz
  have hR := plurisubharmonicOn_radialRegularization hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) hδ
  set L : ℂ →L[ℂ] ComplexModel (N + 1) :=
    ((stripModelEquiv N).symm : ComplexModel N × ℂ →L[ℂ] ComplexModel (N + 1)).comp
      (ContinuousLinearMap.inr ℂ (ComplexModel N) ℂ)
  have hline : ∀ ζ : ℂ, (stripModelEquiv N).symm (z, 0) + L ζ = (stripModelEquiv N).symm (z, ζ) := by
    intro ζ
    simp only [L, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe, ← map_add, Prod.mk_add_mk,
      add_zero, zero_add]
  have h1 := hR.comp_affine L ((stripModelEquiv N).symm (z, 0))
  have hpre : (fun y => (stripModelEquiv N).symm (z, 0) + L y) ⁻¹' innerDomain (stripDomain B) δ =
      univ := by
    ext ζ
    simp only [mem_preimage, mem_univ, iff_true, hline]
    exact stripModelEquiv_symm_mem_innerDomain hz ζ
  rw [hpre] at h1
  have h2 : PlurisubharmonicOn (fun ζ : ℂ => ((regularizedProfile ρ u δ (z, ζ.re) : ℝ) : EReal))
      univ := by
    refine plurisubharmonicOn_congr_of_eqOn isOpen_univ h1 fun ζ _ => ?_
    simp only [hline, regularizedProfile]
    rw [radialRegularization_expPullback_re h.circleInvariant]
  have h3 := convexOn_toReal_of_plurisubharmonicOn_comp_re
    (v := fun t : ℝ => ((regularizedProfile ρ u δ (z, t) : ℝ) : EReal)) h2
    (fun _ => EReal.coe_ne_bot _)
  simpa only [EReal.toReal_coe] using h3

/-- `∂²R_δ/∂y² ≥ 0` on `B'_δ × ℝ`. -/
theorem partialYY_regularizedProfile_nonneg {δ : ℝ} (hδ : 0 < δ) {z : ComplexModel N}
    (hz : z ∈ innerSet B δ) (y : ℝ) :
    0 ≤ partialYY (regularizedProfile ρ u δ) (z, y) := by
  have hzB : z ∈ B := innerSet_subset hδ.le hz
  have hopen : IsOpen (innerSet B δ ×ˢ (univ : Set ℝ)) := (isOpen_innerSet B δ).prod isOpen_univ
  have hcd := h.contDiffOn_regularizedProfile hρ hBc hδ hzB
  have hc2 : ∀ t : ℝ, ContDiffAt ℝ 2 (regularizedProfile ρ u δ) (z, t) := by
    intro t
    have h0 : ContDiffAt ℝ ∞ (regularizedProfile ρ u δ) (z, t) :=
      hcd.contDiffAt (hopen.mem_nhds (mk_mem_prod hz (mem_univ t)))
    exact h0.of_le two_le_infty
  have hconv := h.convexOn_regularizedProfile_slice hρ hBc hδ hz
  have hmono : MonotoneOn (deriv fun t : ℝ => regularizedProfile ρ u δ (z, t)) univ :=
    hconv.monotoneOn_deriv fun t _ => (hasDerivAt_slice (hc2 t)).differentiableAt
  have hm : Monotone fun t => partialY (regularizedProfile ρ u δ) (z, t) := by
    intro s t hst
    have h1 := hmono (mem_univ s) (mem_univ t) hst
    rwa [(hasDerivAt_slice (hc2 s)).deriv, (hasDerivAt_slice (hc2 t)).deriv] at h1
  have h2 : 0 ≤ deriv (fun t => partialY (regularizedProfile ρ u δ) (z, t)) y := hm.deriv_nonneg
  rwa [(hasDerivAt_partialY_slice (hc2 y)).deriv] at h2

end IsBoundedLegendreData

end Regularization

/-! ### The approximants `F_k` -/

section Approximants

variable {N : ℕ}

/-- The scales `s_k = δ₀ / (k + 1)`. -/
def approxScale (δ₀ : ℝ) (k : ℕ) : ℝ := δ₀ / (k + 1)

theorem approxScale_pos {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (k : ℕ) : 0 < approxScale δ₀ k := by
  unfold approxScale; positivity

theorem approxScale_le {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (k : ℕ) : approxScale δ₀ k ≤ δ₀ := by
  unfold approxScale
  exact div_le_self hδ₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

theorem approxScale_antitone {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) : Antitone (approxScale δ₀) := by
  intro k l hkl
  unfold approxScale
  exact div_le_div_of_nonneg_left hδ₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hkl)

theorem tendsto_approxScale (δ₀ : ℝ) : Tendsto (approxScale δ₀) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ₀
  rw [mul_zero] at h
  refine h.congr fun k => ?_
  simp [approxScale, div_eq_mul_inv]

/-- **The approximants** `F_k(z, y) = (1 - s_k) R_{s_k}(z, y) + s_k (c + ψ(y))`. -/
def approxProfile (ρ : ComplexModel (N + 1) → ℝ) (u : ComplexModel N → ℂ → EReal)
    (a b C δ₀ : ℝ) (k : ℕ) (p : ComplexModel N × ℝ) : ℝ :=
  (1 - approxScale δ₀ k) * regularizedProfile ρ u (approxScale δ₀ k) p +
    approxScale δ₀ k * (approxConst a b C + legendreModelProfile a b p.2)

/-- The slack `K₁ + K₂ = C + c + (b - a)/2` of the growth bounds. -/
def approxSlack (a b C : ℝ) : ℝ := C + (approxConst a b C + (b - a) / 2)

/-- The domain `B'_{2δ₀}` as an open set. -/
def approxDomain (B : Set (ComplexModel N)) (δ₀ : ℝ) : Opens (ComplexModel N) :=
  ⟨innerSet B (2 * δ₀), isOpen_innerSet B _⟩

variable {B : Set (ComplexModel N)} {u : ComplexModel N → ℂ → EReal} {a b C : ℝ}
  {ρ : ComplexModel (N + 1) → ℝ} {δ₀ : ℝ}

theorem mem_innerSet_two_mul_approxScale (hδ₀ : 0 < δ₀) {z : ComplexModel N}
    (hz : z ∈ approxDomain B δ₀) (k : ℕ) : z ∈ innerSet B (2 * approxScale δ₀ k) :=
  innerSet_anti (by linarith [approxScale_le hδ₀.le k]) hz

theorem mem_innerSet_approxScale (hδ₀ : 0 < δ₀) {z : ComplexModel N}
    (hz : z ∈ approxDomain B δ₀) (k : ℕ) : z ∈ innerSet B (approxScale δ₀ k) :=
  innerSet_anti (by linarith [approxScale_le hδ₀.le k, approxScale_pos hδ₀ k]) hz

namespace IsBoundedLegendreData

variable (h : IsBoundedLegendreData B u a b C) (hρ : IsRadialKernel ρ) (hBc : IsPreconnected B)
  (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ ≤ 1 / 2)
include h hρ hBc hδ₀ hδ₀'

/-- **Growth bounds**: `-C + max(ay, by) ≤ F_k(z, y) ≤ c + (b - a)/2 + max(ay, by)`. -/
theorem approxProfile_bounds {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (k : ℕ)
    (y : ℝ) :
    -C + max (a * y) (b * y) ≤ approxProfile ρ u a b C δ₀ k (z, y) ∧
      approxProfile ρ u a b C δ₀ k (z, y) ≤
        approxConst a b C + (b - a) / 2 + max (a * y) (b * y) := by
  have hs := approxScale_pos hδ₀ k
  have hs1 := approxScale_le hδ₀.le k
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hC := h.nonneg_C hzB
  have hR1 := h.regularizedProfile_lower hρ hBc hs (mem_innerSet_approxScale hδ₀ hz k) y
  have hR2 := h.regularizedProfile_upper hρ hBc hs (by linarith)
    (mem_innerSet_two_mul_approxScale hδ₀ hz k) y
  have hψ := legendreModelProfile_bounds h.lt.le y
  have hM := slopeBound_nonneg a b
  have hab := h.lt
  simp only [approxProfile, approxConst] at hR2 ⊢
  set s := approxScale δ₀ k
  set R := regularizedProfile ρ u s (z, y)
  set m := max (a * y) (b * y)
  constructor
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - s by linarith) (show 0 ≤ R - (-C + m) by linarith),
      mul_nonneg hs.le (show 0 ≤ C + 2 * slopeBound a b + 1 + legendreModelProfile a b y - (-C + m)
        by linarith)]
  · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - s by linarith)
      (show 0 ≤ C + 2 * slopeBound a b + 1 + m - R by linarith),
      mul_nonneg hs.le (show 0 ≤ m + (b - a) / 2 - legendreModelProfile a b y by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - s by linarith) (show (0 : ℝ) ≤ (b - a) / 2 by linarith)]

omit hδ₀' in
/-- `F_k` is smooth on `B'_{2δ₀} × ℝ`. -/
theorem contDiffOn_approxProfile {z₀ : ComplexModel N} (hz₀ : z₀ ∈ B) (k : ℕ) :
    ContDiffOn ℝ ∞ (approxProfile ρ u a b C δ₀ k) ((approxDomain B δ₀ : Set _) ×ˢ univ) := by
  have hs := approxScale_pos hδ₀ k
  have hR := (h.contDiffOn_regularizedProfile hρ hBc hs hz₀).mono
    (prod_mono (show (approxDomain B δ₀ : Set (ComplexModel N)) ⊆ innerSet B (approxScale δ₀ k)
      from fun z hz => mem_innerSet_approxScale hδ₀ hz k) subset_rfl)
  have hψ : ContDiff ℝ ∞ (fun p : ComplexModel N × ℝ =>
      approxConst a b C + legendreModelProfile a b p.2) :=
    contDiff_const.add ((contDiff_legendreModelProfile a b).comp contDiff_snd)
  exact (contDiffOn_const.mul hR).add (contDiffOn_const.mul hψ.contDiffOn)

omit hδ₀' in
/-- `∂F_k/∂y = (1 - s_k) ∂R/∂y + s_k ψ'` and `∂²F_k/∂y² = (1 - s_k) ∂²R/∂y² + s_k ψ''`. -/
theorem partialYY_approxProfile {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (k : ℕ)
    (y : ℝ) :
    partialYY (approxProfile ρ u a b C δ₀ k) (z, y) =
      (1 - approxScale δ₀ k) * partialYY (regularizedProfile ρ u (approxScale δ₀ k)) (z, y) +
        approxScale δ₀ k * legendreModelCurv a b y := by
  have hs := approxScale_pos hδ₀ k
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  set s := approxScale δ₀ k
  have hzs : z ∈ innerSet B s := mem_innerSet_approxScale hδ₀ hz k
  have hopenR : IsOpen (innerSet B s ×ˢ (univ : Set ℝ)) := (isOpen_innerSet B s).prod isOpen_univ
  have hcdR := h.contDiffOn_regularizedProfile hρ hBc hs hzB
  have hcR : ∀ t : ℝ, ContDiffAt ℝ 2 (regularizedProfile ρ u s) (z, t) := by
    intro t
    have h0 : ContDiffAt ℝ ∞ (regularizedProfile ρ u s) (z, t) :=
      hcdR.contDiffAt (hopenR.mem_nhds (mk_mem_prod hzs (mem_univ t)))
    exact h0.of_le two_le_infty
  have hopenF : IsOpen ((approxDomain B δ₀ : Set (ComplexModel N)) ×ˢ (univ : Set ℝ)) :=
    (approxDomain B δ₀).isOpen.prod isOpen_univ
  have hcdF := h.contDiffOn_approxProfile hρ hBc hδ₀ hzB k
  have hcF : ∀ t : ℝ, ContDiffAt ℝ 2 (approxProfile ρ u a b C δ₀ k) (z, t) := by
    intro t
    have h0 : ContDiffAt ℝ ∞ (approxProfile ρ u a b C δ₀ k) (z, t) :=
      hcdF.contDiffAt (hopenF.mem_nhds (mk_mem_prod hz (mem_univ t)))
    exact h0.of_le two_le_infty
  have hY : ∀ t : ℝ, partialY (approxProfile ρ u a b C δ₀ k) (z, t) =
      (1 - s) * partialY (regularizedProfile ρ u s) (z, t) + s * legendreModelSlope a b t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => approxProfile ρ u a b C δ₀ k (z, t))
        ((1 - s) * partialY (regularizedProfile ρ u s) (z, t) +
          s * (0 + legendreModelSlope a b t)) t :=
      ((hasDerivAt_slice (hcR t)).const_mul (1 - s)).add
        (((hasDerivAt_const t (approxConst a b C)).add
          (hasDerivAt_legendreModelProfile a b t)).const_mul s)
    rw [zero_add] at h1
    exact (hasDerivAt_slice (hcF t)).unique h1
  have h2 : HasDerivAt (fun t : ℝ => partialY (approxProfile ρ u a b C δ₀ k) (z, t))
      ((1 - s) * partialYY (regularizedProfile ρ u s) (z, y) + s * legendreModelCurv a b y) y := by
    have h3 := ((hasDerivAt_partialY_slice (hcR y)).const_mul (1 - s)).add
      ((hasDerivAt_legendreModelSlope a b y).const_mul s)
    exact h3.congr_of_eventuallyEq (Eventually.of_forall fun t => hY t)
  exact (hasDerivAt_partialY_slice (hcF y)).unique h2

theorem partialYY_approxProfile_pos {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (k : ℕ)
    (y : ℝ) : 0 < partialYY (approxProfile ρ u a b C δ₀ k) (z, y) := by
  rw [h.partialYY_approxProfile hρ hBc hδ₀ hz k y]
  have hs := approxScale_pos hδ₀ k
  have hs1 := approxScale_le hδ₀.le k
  have hR := h.partialYY_regularizedProfile_nonneg hρ hBc hs (mem_innerSet_approxScale hδ₀ hz k) y
  have hψ := legendreModelCurv_pos h.lt y
  have h1 : 0 ≤ (1 - approxScale δ₀ k) * partialYY (regularizedProfile ρ u (approxScale δ₀ k))
      (z, y) := mul_nonneg (by linarith) hR
  have h2 := mul_pos hs hψ
  linarith

/-- **`F_k` satisfies the hypotheses of the smooth case** on `B'_{2δ₀}`. -/
theorem isSmoothLegendreData_approxProfile {z₀ : ComplexModel N} (hz₀ : z₀ ∈ B) (k : ℕ) :
    IsSmoothLegendreData (approxDomain B δ₀ : Set (ComplexModel N))
      (approxProfile ρ u a b C δ₀ k) a b :=
  IsSmoothLegendreData.of_bounds (approxDomain B δ₀).isOpen
    (h.contDiffOn_approxProfile hρ hBc hδ₀ hz₀ k) h.lt
    (fun _ hz y => h.partialYY_approxProfile_pos hρ hBc hδ₀ hδ₀' hz k y)
    (fun _ hz => ⟨C, approxConst a b C + (b - a) / 2, fun y =>
      h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k y⟩)

/-- **`u_k(z, τ) = F_k(z, log |τ|²)` is psh on `B'_{2δ₀} × ℂ*`.** -/
theorem plurisubharmonicOn_approxProfile {z₀ : ComplexModel N} (hz₀ : z₀ ∈ B) (k : ℕ) :
    PlurisubharmonicOn (fun p : ComplexModel N × ℂ =>
      logRadialFunction (approxProfile ρ u a b C δ₀ k) p.1 p.2)
      ((approxDomain B δ₀ : Set (ComplexModel N)) ×ˢ puncturedPlane) := by
  have hs := approxScale_pos hδ₀ k
  have hs1 := approxScale_le hδ₀.le k
  set s := approxScale δ₀ k
  have hR := plurisubharmonicOn_radialRegularization hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hz₀) hs
  have h1 := hR.const_mul (show (0 : ℝ) < 1 - s by linarith)
  have h2 := ((plurisubharmonicOn_modelProfile_last (N := N) h.lt (approxConst a b C)).mono
    (subset_univ (innerDomain (stripDomain B) s))).const_mul hs
  have h3 := plurisubharmonicOn_comp_stripModelEquiv_symm (h1.add h2)
  have hsub : (approxDomain B δ₀ : Set (ComplexModel N)) ×ˢ (univ : Set ℂ) ⊆
      (stripModelEquiv N).symm ⁻¹' innerDomain (stripDomain B) s :=
    fun p hp => stripModelEquiv_symm_mem_innerDomain (mem_innerSet_approxScale hδ₀ hp.1 k) p.2
  have h4 : PlurisubharmonicOn (fun p : ComplexModel N × ℂ =>
      ((approxProfile ρ u a b C δ₀ k (p.1, p.2.re) : ℝ) : EReal))
      ((approxDomain B δ₀ : Set (ComplexModel N)) ×ˢ univ) := by
    refine plurisubharmonicOn_congr_of_eqOn ((approxDomain B δ₀).isOpen.prod isOpen_univ)
      (h3.mono hsub) fun p _ => ?_
    simp only [approxProfile, regularizedProfile, EReal.coe_add, EReal.coe_mul]
    rw [stripModelEquiv_symm_apply_last, ← radialRegularization_expPullback_re h.circleInvariant]
  exact plurisubharmonicOn_descend_of_re (approxDomain B δ₀).isOpen h4

/-- **Monotonicity**: `F_l ≤ F_k` for `k ≤ l`. -/
theorem approxProfile_anti {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) {k l : ℕ}
    (hkl : k ≤ l) (y : ℝ) :
    approxProfile ρ u a b C δ₀ l (z, y) ≤ approxProfile ρ u a b C δ₀ k (z, y) := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hsk := approxScale_pos hδ₀ k
  have hsl := approxScale_pos hδ₀ l
  have hsk1 := approxScale_le hδ₀.le k
  have hlk : approxScale δ₀ l ≤ approxScale δ₀ k := approxScale_antitone hδ₀.le hkl
  have hmono := radialRegularization_mono hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) hsl hlk
    (stripModelEquiv_symm_mem_innerDomain (mem_innerSet_approxScale hδ₀ hz k) (y : ℂ))
  have hR2 := h.regularizedProfile_upper hρ hBc hsk (by linarith)
    (mem_innerSet_two_mul_approxScale hδ₀ hz k) y
  have hψ := (legendreModelProfile_bounds h.lt.le y).1
  simp only [approxProfile]
  change (1 - approxScale δ₀ l) * regularizedProfile ρ u (approxScale δ₀ l) (z, y) + _ ≤
    (1 - approxScale δ₀ k) * regularizedProfile ρ u (approxScale δ₀ k) (z, y) + _
  have hmono' : regularizedProfile ρ u (approxScale δ₀ l) (z, y) ≤
      regularizedProfile ρ u (approxScale δ₀ k) (z, y) := hmono
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - approxScale δ₀ l by linarith)
      (show 0 ≤ regularizedProfile ρ u (approxScale δ₀ k) (z, y) -
        regularizedProfile ρ u (approxScale δ₀ l) (z, y) by linarith),
    mul_nonneg (show (0 : ℝ) ≤ approxScale δ₀ k - approxScale δ₀ l by linarith)
      (show 0 ≤ approxConst a b C + legendreModelProfile a b y -
        regularizedProfile ρ u (approxScale δ₀ k) (z, y) by linarith)]

omit hρ hBc hδ₀ hδ₀' in
/-- The real values `Ũ(z, y) = u(z, e^{y/2})`. -/
theorem expPullback_symm_eq_coe {z : ComplexModel N} (hzB : z ∈ B) (y : ℝ) :
    expPullback u ((stripModelEquiv N).symm (z, (y : ℂ))) =
      (((expPullback u ((stripModelEquiv N).symm (z, (y : ℂ)))).toReal : ℝ) : EReal) :=
  (EReal.coe_toReal (h.expPullback_ne_top (stripModelEquiv_symm_mem_stripDomain hzB _))
    (h.expPullback_ne_bot (stripModelEquiv_symm_mem_stripDomain hzB _))).symm

/-- `Ũ ≤ F_k`. -/
theorem expPullback_le_approxProfile {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (k : ℕ)
    (y : ℝ) :
    (expPullback u ((stripModelEquiv N).symm (z, (y : ℂ)))).toReal ≤
      approxProfile ρ u a b C δ₀ k (z, y) := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hs := approxScale_pos hδ₀ k
  have hs1 := approxScale_le hδ₀.le k
  have h1 := le_radialRegularization hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) hs
    (stripModelEquiv_symm_mem_innerDomain (mem_innerSet_approxScale hδ₀ hz k) (y : ℂ))
  rw [h.expPullback_symm_eq_coe hzB y, EReal.coe_le_coe_iff] at h1
  have hR2 := h.regularizedProfile_upper hρ hBc hs (by linarith)
    (mem_innerSet_two_mul_approxScale hδ₀ hz k) y
  have hψ := (legendreModelProfile_bounds h.lt.le y).1
  have h1' : (expPullback u ((stripModelEquiv N).symm (z, (y : ℂ)))).toReal ≤
      regularizedProfile ρ u (approxScale δ₀ k) (z, y) := h1
  simp only [approxProfile]
  nlinarith [mul_nonneg hs.le (show 0 ≤ approxConst a b C + legendreModelProfile a b y -
        regularizedProfile ρ u (approxScale δ₀ k) (z, y) by linarith)]

omit hδ₀' in
/-- **Convergence**: `F_k(z, y) → Ũ(z, y)`. -/
theorem tendsto_approxProfile {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (y : ℝ) :
    Tendsto (fun k => approxProfile ρ u a b C δ₀ k (z, y)) atTop
      (𝓝 (expPullback u ((stripModelEquiv N).symm (z, (y : ℂ)))).toReal) := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hR := tendsto_radialRegularization_seq hρ (isOpen_stripDomain h.isOpen)
    (isPreconnected_stripDomain hBc) h.plurisubharmonicOn_expPullback'
    (h.exists_expPullback_ne_bot hzB) (approxScale_pos hδ₀) (tendsto_approxScale δ₀)
    (stripModelEquiv_symm_mem_stripDomain hzB (y : ℂ))
  rw [h.expPullback_symm_eq_coe hzB y, EReal.tendsto_coe] at hR
  have hs := tendsto_approxScale δ₀
  have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub hs).mul hR
  have h2 := hs.mul (tendsto_const_nhds (x := approxConst a b C + legendreModelProfile a b y))
  have h3 := h1.add h2
  simp only [sub_zero, one_mul, zero_mul, add_zero] at h3
  exact h3

/-! ### The smooth partial Legendre transforms of the approximants -/

/-- `-C ≤ (û_k)_λ ≤ c + (b - a)/2` on `B'_{2δ₀}` for `λ ∈ (a, b)`. -/
theorem legendreValue_approxProfile_bounds {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀)
    (k : ℕ) {lam : ℝ} (hlam : lam ∈ Ioo a b) :
    -C ≤ legendreValue (approxProfile ρ u a b C δ₀ k) z lam ∧
      legendreValue (approxProfile ρ u a b C δ₀ k) z lam ≤ approxConst a b C + (b - a) / 2 := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB k
  constructor
  · set Y := legendreArg (approxProfile ρ u a b C δ₀ k) z lam
    have h1 := (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k Y).1
    have h2 := mul_le_max_of_mem_Icc (y := Y) ⟨hlam.1.le, hlam.2.le⟩
    simp only [legendreValue]
    linarith
  · have h1 := hD.legendreValue_le hz hlam 0
    have h2 := (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k 0).2
    simp only [mul_zero, max_self, add_zero, sub_zero] at h1 h2
    linarith

/-- `(û_l)_λ ≤ (û_k)_λ` for `k ≤ l`. -/
theorem legendreValue_approxProfile_anti {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀)
    {lam : ℝ} (hlam : lam ∈ Ioo a b) {k l : ℕ} (hkl : k ≤ l) :
    legendreValue (approxProfile ρ u a b C δ₀ l) z lam ≤
      legendreValue (approxProfile ρ u a b C δ₀ k) z lam := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB l
  have h1 := hD.legendreValue_le hz hlam (legendreArg (approxProfile ρ u a b C δ₀ k) z lam)
  have h2 := h.approxProfile_anti hρ hBc hδ₀ hδ₀' hz hkl
    (legendreArg (approxProfile ρ u a b C δ₀ k) z lam)
  simp only [legendreValue] at h1 ⊢
  linarith

omit hρ hBc hδ₀ hδ₀' in
theorem partialLegendre_ne_bot_of_mem {z : ComplexModel N} (hzB : z ∈ B) {lam : ℝ}
    (hlam : lam ∈ Icc a b) : partialLegendre u lam z ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h.lower lam hlam z hzB)

omit hρ hBc hδ₀ hδ₀' in
theorem partialLegendre_ne_top_of_mem {z : ComplexModel N} (hzB : z ∈ B) {lam : ℝ}
    (hlam : lam ∈ Icc a b) : partialLegendre u lam z ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) (h.upper lam hlam z hzB)

/-- **The transforms decrease to `û_λ`**: `(û_k)_λ(z) → û_λ(z)` for `λ ∈ (a, b)`. -/
theorem tendsto_legendreValue_approxProfile {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀)
    {lam : ℝ} (hlam : lam ∈ Ioo a b) :
    Tendsto (fun k => legendreValue (approxProfile ρ u a b C δ₀ k) z lam) atTop
      (𝓝 (partialLegendre u lam z).toReal) := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  set lv : ℕ → ℝ := fun k => legendreValue (approxProfile ρ u a b C δ₀ k) z lam with hlv
  have hanti : Antitone lv := fun k l hkl =>
    h.legendreValue_approxProfile_anti hρ hBc hδ₀ hδ₀' hz hlam hkl
  have hbdd : BddBelow (range lv) :=
    ⟨-C, by rintro _ ⟨k, rfl⟩; exact (h.legendreValue_approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k
      hlam).1⟩
  have hT := tendsto_atTop_ciInf hanti hbdd
  suffices hL : ⨅ k, lv k = (partialLegendre u lam z).toReal by rwa [hL] at hT
  have hfin : partialLegendre u lam z = (((partialLegendre u lam z).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (h.partialLegendre_ne_top_of_mem hzB ⟨hlam.1.le, hlam.2.le⟩)
      (h.partialLegendre_ne_bot_of_mem hzB ⟨hlam.1.le, hlam.2.le⟩)).symm
  have hreal : ∀ t : ℝ, u z (Complex.exp ((t : ℂ) / 2)) =
      (((expPullback u ((stripModelEquiv N).symm (z, (t : ℂ)))).toReal : ℝ) : EReal) := by
    intro t
    rw [← h.expPullback_symm_eq_coe hzB t, expPullback_symm]
  have hinf := partialLegendre_eq_iInf_real h.circleInvariant lam z
  apply le_antisymm
  · -- `inf_k (û_k)_λ ≤ Ũ(z, t) - λ t` for every `t`
    have hle : ∀ t : ℝ, ⨅ k, lv k ≤
        (expPullback u ((stripModelEquiv N).symm (z, (t : ℂ)))).toReal - lam * t := by
      intro t
      have hlim := (h.tendsto_approxProfile hρ hBc hδ₀ hz t).sub_const (lam * t)
      refine ge_of_tendsto' hlim fun k => ?_
      have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB k
      exact (ciInf_le hbdd k).trans (hD.legendreValue_le hz hlam t)
    have h1 : ((⨅ k, lv k : ℝ) : EReal) ≤ partialLegendre u lam z := by
      rw [hinf]
      refine le_iInf fun t => ?_
      rw [hreal t, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hle t
    rw [hfin, EReal.coe_le_coe_iff] at h1
    exact h1
  · -- `û_λ ≤ (û_k)_λ` for every `k`
    refine le_ciInf fun k => ?_
    have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB k
    set Y := legendreArg (approxProfile ρ u a b C δ₀ k) z lam
    have h1 : partialLegendre u lam z ≤ ((lv k : ℝ) : EReal) := by
      rw [hinf]
      refine (iInf_le _ Y).trans ?_
      rw [hreal Y, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := h.expPullback_le_approxProfile hρ hBc hδ₀ hδ₀' hz k Y
      simp only [hlv, legendreValue, Y]
      linarith
    rw [hfin, EReal.coe_le_coe_iff] at h1
    exact h1

/-- **Slope bound at `+∞`, uniform in `k`**: `Y_k(z, λ) < L` when `λ < b - K/L`. -/
theorem legendreArg_approxProfile_lt {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀) (k : ℕ)
    {L : ℝ} (hL : 0 < L) {lam : ℝ} (hlam : lam ∈ Ioo a b)
    (hlt : lam < b - approxSlack a b C / L) :
    legendreArg (approxProfile ρ u a b C δ₀ k) z lam < L := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB k
  by_contra hge
  push Not at hge
  have h1 := chord_lower (f := fun t => approxProfile ρ u a b C δ₀ k (z, t))
    (f' := fun t => partialY (approxProfile ρ u a b C δ₀ k) (z, t))
    (fun t => hasDerivAt_slice (hD.contDiffAt_two hz t)) (hD.strictMono_partialY hz).monotone
    (fun y => (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k y).1)
    (fun y => (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k y).2) hL hge
  rw [hD.partialY_legendreArg hz hlam] at h1
  simp only [approxSlack] at hlt
  linarith

/-- **Slope bound at `-∞`, uniform in `k`**: `-L < Y_k(z, λ)` when `a + K/L < λ`. -/
theorem neg_lt_legendreArg_approxProfile {z : ComplexModel N} (hz : z ∈ approxDomain B δ₀)
    (k : ℕ) {L : ℝ} (hL : 0 < L) {lam : ℝ} (hlam : lam ∈ Ioo a b)
    (hgt : a + approxSlack a b C / L < lam) :
    -L < legendreArg (approxProfile ρ u a b C δ₀ k) z lam := by
  have hzB : z ∈ B := innerSet_subset (by linarith) hz
  have hD := h.isSmoothLegendreData_approxProfile hρ hBc hδ₀ hδ₀' hzB k
  by_contra hge
  push Not at hge
  have h1 := chord_upper (f := fun t => approxProfile ρ u a b C δ₀ k (z, t))
    (f' := fun t => partialY (approxProfile ρ u a b C δ₀ k) (z, t))
    (fun t => hasDerivAt_slice (hD.contDiffAt_two hz t)) (hD.strictMono_partialY hz).monotone
    (fun y => (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k y).1)
    (fun y => (h.approxProfile_bounds hρ hBc hδ₀ hδ₀' hz k y).2) hL hge
  rw [hD.partialY_legendreArg hz hlam] at h1
  simp only [approxSlack] at hgt
  linarith

end IsBoundedLegendreData

end Approximants

end SGPT.Okounkov.TranscendentalWN
