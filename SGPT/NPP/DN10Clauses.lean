import SGPT.NPP.DN10QPart
import SGPT.NPP.DN10Radial
import SGPT.NPP.DN11Joint

/-!
# The clauses `H ≥ u`, convexity in `log t` and the slope bounds (the `ClauseEstimate`)

Lane DN10, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`): "`H_u(x, eˢ)` is a strictly convex
nondecreasing function of `s` which tends to `u(x)`; in particular `λ_u ≥ 0`" (statement), Step 5
("we choose `K ≥ C_q + 1` [...] `(r∂_r)²H_u = 4r²∂_w∂_w̄H_u > 0`"), Step 7 (`H_u ≥ u`), and the slope
bounds behind `eq:chern-initial-joint-bound` / `eq:chern-improved-joint-bound`
(`λ_u ≤ C_u`; under `H_u(x, t) ≤ u(x) + L t` for `t ≤ C₁ r`, `λ_u(t) ≤ C(1 + L) r` for `t ≤ 2r`).

With `p = u + q` plurisubharmonic (poles allowed) and `H = Ψ_u + K₀ t² = Ψ_p - Ψ_q + K₀ t²`
(the splitting `localSmoothing_toReal_split`):

* in a frame `L` normalizing `α_z`, `Ψ_f(z, t) = ∫ f(Φ(z, t L s)) χ(|s|²) ds`
  (`localSmoothing_eq_frame`), so `Ψ_p(z, ·)` is a radial mean of the plurisubharmonic function
  `s ↦ p(Φ(z, L s))` (TN `plurisubharmonicOn_comp_holomorphic`): `Ψ_p(z, t) ≥ p(z)`, nondecreasing,
  convex in `log t` (`radial_package`, from the `radial_psh`);
* the `q`-part contributes `O(t²)` to `H`, its slope and its second log-derivative
  (`exists_qRadial`); `K₀ ≥ C_q + 1` absorbs them;
* `λ_H(t) ≤ λ_H(r₁) ≤ C_u` by monotonicity of the slope and continuity in `z` (the joint
  smoothness `contDiffOn_localSmoothing_toReal`);
* under the linear bound, convexity gives `λ_p(2r) ≤ Ψ_p(2er) - Ψ_p(2r) ≤ 2eLr`.

**Main result**: `clauseEstimate : SGPT.NPP.DN9.ClauseEstimate N`.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN10

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NPP.DN5 SGPT.Analysis.KahlerNormal

variable {N : ℕ}

local notation "E" => ComplexModel N

/-! ### The smoothing in a normalizing frame -/

/-- **The smoothing in a frame normalizing `α_z`**:
`Ψ_f(z, t) = ∫ f(Φ(z, t L s)) χ(|s|²) ds`. -/
theorem localSmoothing_eq_frame (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) {z : E}
    {L : E ≃L[ℂ] E} (hL : ∀ u v, α z ![L u, L v] = flatForm N ![u, v]) (f : E → ℝ) (t : ℝ) :
    localSmoothing Φ α f z t = ∫ s, f (Φ z (t • L s)) * DN3.kernel N s := by
  have hw : ∀ s, localWeight α z ((L.restrictScalars ℝ) s) = DN3.kernel N s :=
    fun s => localWeight_frame hL s
  have hden : ∫ ξ, DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ]) =
      |LinearMap.det (L.restrictScalars ℝ).toLinearEquiv.toLinearMap| := by
    change ∫ ξ, localWeight α z ξ = _
    rw [integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)]
    simp_rw [hw, DN3.integral_kernel, mul_one]
  unfold localSmoothing
  rw [hden, integral_eq_abs_det_mul_integral_comp (L.restrictScalars ℝ)
    (fun ξ => f (Φ z (t • ξ)) * DN3.chi N (Real.pi * α z ![ξ, Complex.I • ξ]))]
  have : ∀ s, f (Φ z (t • (L.restrictScalars ℝ) s)) *
      DN3.chi N (Real.pi * α z ![(L.restrictScalars ℝ) s, Complex.I • (L.restrictScalars ℝ) s]) =
      f (Φ z (t • L s)) * DN3.kernel N s := fun s => by
    change f (Φ z (t • L s)) * localWeight α z ((L.restrictScalars ℝ) s) = _
    rw [hw s]
  simp_rw [this]
  exact mul_div_cancel_left₀ _ (abs_det_pos (L.restrictScalars ℝ)).ne'

/-- **A uniform radius for normalizing frames** on the compact `K`: there is `R₀ > 0` such that
for every `z ∈ K` some frame `L` normalizing `α_z` maps `R₀ · B(0, 2)` into the tube where `Φ`
is a local fibre map with values in `U`. -/
theorem exists_frame_radius {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O)
    {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U K : Set E} (hU : IsOpen U) (hα : ContinuousOn α U)
    (h11 : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : E)) ∈ O) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ z ∈ K, ∃ L : E ≃L[ℂ] E, (∀ u v, α z ![L u, L v] = flatForm N ![u, v]) ∧
      ∀ s : E, ‖s‖ < 2 → (z, L ((R₀ : ℂ) • s)) ∈ O ∧ Φ z (L ((R₀ : ℂ) • s)) ∈ U := by
  obtain ⟨δ, hδ, htube⟩ := exists_tube hΦ hU hK hKU hKO
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul hα (fun z hz => (h11 z hz).2) hK hKU
  have hpm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  set R₀ := min 1 (δ ^ 2 * (Real.pi * m) / 4) with hR₀
  have hR₀0 : 0 < R₀ := lt_min one_pos (by positivity)
  refine ⟨R₀, hR₀0, fun z hz => ?_⟩
  obtain ⟨L, hL⟩ := exists_normalizing_linear (h11 z (hKU hz)).1 (h11 z (hKU hz)).2
  refine ⟨L, hL, fun s hs => ?_⟩
  set ξ := L ((R₀ : ℂ) • s) with hξ
  have hnorm : m * ‖ξ‖ ^ 2 ≤ Real.pi⁻¹ * (R₀ ^ 2 * ‖s‖ ^ 2) := by
    have h1 := hmK z hz ξ
    have h2 : α z ![ξ, Complex.I • ξ] = Real.pi⁻¹ * ‖(R₀ : ℂ) • s‖ ^ 2 := by
      rw [hξ, ← L.map_smul Complex.I, hL, flatForm_apply_I_smul_self]
    rw [h2, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₀0, mul_pow] at h1
    exact h1
  have hs2 : ‖s‖ ^ 2 < 4 := by nlinarith [norm_nonneg s]
  have hR₀1 : R₀ ≤ 1 := min_le_left _ _
  have hR₀2 : R₀ ≤ δ ^ 2 * (Real.pi * m) / 4 := min_le_right _ _
  have hξ2 : ‖ξ‖ ^ 2 < δ ^ 2 := by
    have h3 : Real.pi * m * ‖ξ‖ ^ 2 ≤ R₀ ^ 2 * ‖s‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hnorm Real.pi_pos.le
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul] at this
      linarith
    have h4 : R₀ ^ 2 * ‖s‖ ^ 2 < 4 * R₀ := by
      have hR2 : R₀ ^ 2 ≤ R₀ := by nlinarith
      calc R₀ ^ 2 * ‖s‖ ^ 2 ≤ R₀ * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_right hR2 (by positivity)
        _ < R₀ * 4 := mul_lt_mul_of_pos_left hs2 hR₀0
        _ = 4 * R₀ := by ring
    have h5 : 4 * R₀ ≤ δ ^ 2 * (Real.pi * m) := by linarith
    by_contra hcon
    push Not at hcon
    nlinarith
  have hξδ : ‖ξ‖ < δ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg ξ]
  have h := htube z z hz (by simpa using hδ) ξ hξδ
  exact ⟨h.1, h.2.1⟩

/-- **The radial package at a centre**: for `p` plurisubharmonic on `U` (poles allowed), the
smoothing `t ↦ Ψ_p(z, t)` satisfies `p(z) ≤ Ψ_p(z, t)` (`0 < t ≤ R₀`), is nondecreasing on
`(0, R₀]` and convex in `log t` on `t ≤ R₀`. -/
theorem radial_package {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O)
    (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) {U : Set E} {p : E → EReal} (hp : PlurisubharmonicOn p U)
    {z : E} (hzO : (z, (0 : E)) ∈ O) {L : E ≃L[ℂ] E}
    (hL : ∀ u v, α z ![L u, L v] = flatForm N ![u, v]) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hmaps : ∀ s : E, ‖s‖ < 2 → (z, L ((R₀ : ℂ) • s)) ∈ O ∧ Φ z (L ((R₀ : ℂ) • s)) ∈ U) :
    (∀ t : ℝ, 0 < t → t ≤ R₀ →
      p z ≤ ((localSmoothing Φ α (fun y => (p y).toReal) z t : ℝ) : EReal)) ∧
    MonotoneOn (localSmoothing Φ α (fun y => (p y).toReal) z) (Ioc 0 R₀) ∧
    ConvexOn ℝ (Iic (Real.log R₀))
      (fun s => localSmoothing Φ α (fun y => (p y).toReal) z (Real.exp s)) := by
  obtain ⟨F, hFdef⟩ : ∃ F : E → E, F = fun s => Φ z (L ((R₀ : ℂ) • s)) := ⟨_, rfl⟩
  have hF : DifferentiableOn ℂ F (ball 0 2) := by
    rw [hFdef]
    intro s hs
    have hs' : ‖s‖ < 2 := by simpa using hs
    have h1 : DifferentiableAt ℂ (Φ z) (L ((R₀ : ℂ) • s)) :=
      hΦ.holo (z, L ((R₀ : ℂ) • s)) (hmaps s hs').1
    have h2 : DifferentiableAt ℂ (fun s : E => L ((R₀ : ℂ) • s)) s :=
      (L : E →L[ℂ] E).differentiableAt.comp s (differentiableAt_id.const_smul (R₀ : ℂ))
    exact (h1.comp s h2).differentiableWithinAt
  have hG : PlurisubharmonicOn (fun s => p (F s)) (ball 0 2) :=
    Pending.HolomorphicPullback.plurisubharmonicOn_comp_holomorphic isOpen_ball hF
      (fun s hs => by rw [hFdef]; exact (hmaps s (by simpa using hs)).2) hp
  obtain ⟨h1, h2, h3⟩ := radial_psh (n := N) (by norm_num : (1 : ℝ) < 2) hG
  have hid : ∀ t : ℝ, localSmoothing Φ α (fun y => (p y).toReal) z t =
      ∫ y, (p (F ((t / R₀) • y))).toReal * DN3.kernel N y := by
    intro t
    rw [localSmoothing_eq_frame Φ α hL]
    congr 1
    funext y
    have : L ((R₀ : ℂ) • ((t / R₀) • y)) = t • L y := by
      rw [← Complex.coe_smul (t / R₀) y, map_smul, map_smul, smul_smul, ← Complex.ofReal_mul,
        mul_div_cancel₀ t hR₀.ne', Complex.coe_smul]
    rw [hFdef]
    dsimp only
    rw [this]
  have hG0 : p (F 0) = p z := by
    rw [hFdef]
    dsimp only
    rw [smul_zero, map_zero, hΦ.map_zero z hzO]
  refine ⟨fun t ht0 htR => ?_, fun r hr s hs hrs => ?_, ?_⟩
  · rw [hid t, ← hG0]
    exact h1 (t / R₀) (div_pos ht0 hR₀) ((div_le_one hR₀).mpr htR)
  · rw [hid r, hid s]
    exact h2 ⟨div_pos hr.1 hR₀, (div_le_one hR₀).mpr hr.2⟩
      ⟨div_pos hs.1 hR₀, (div_le_one hR₀).mpr hs.2⟩ (div_le_div_of_nonneg_right hrs hR₀.le)
  · have hPM : ∀ s : ℝ, localSmoothing Φ α (fun y => (p y).toReal) z (Real.exp s) =
        ∫ y, (p (F (Real.exp (s - Real.log R₀) • y))).toReal * DN3.kernel N y := by
      intro s
      rw [hid, Real.exp_sub, Real.exp_log hR₀]
    refine ⟨convex_Iic _, fun x hx y hy a b ha hb hab => ?_⟩
    simp only [hPM, smul_eq_mul]
    have hx' : x - Real.log R₀ ∈ Iic (0 : ℝ) := by simp only [mem_Iic] at hx ⊢; linarith
    have hy' : y - Real.log R₀ ∈ Iic (0 : ℝ) := by simp only [mem_Iic] at hy ⊢; linarith
    have h := h3.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at h
    have he : a * x + b * y - Real.log R₀ = a * (x - Real.log R₀) + b * (y - Real.log R₀) := by
      have : a * Real.log R₀ + b * Real.log R₀ = Real.log R₀ := by rw [← add_mul, hab, one_mul]
      linarith
    rw [he]
    exact h

/-- `d/ds f(eˢ)` at `s = log t` is `t f'(t)`. -/
theorem deriv_comp_exp_log {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hf : DifferentiableAt ℝ f t) :
    deriv (fun s => f (Real.exp s)) (Real.log t) = t * deriv f t := by
  have h1 : HasDerivAt f (deriv f t) (Real.exp (Real.log t)) := by
    rw [Real.exp_log ht]; exact hf.hasDerivAt
  have h2 := h1.comp (Real.log t) (Real.hasDerivAt_exp (Real.log t))
  have h3 : deriv (fun s => f (Real.exp s)) (Real.log t) = deriv f t * Real.exp (Real.log t) :=
    h2.deriv
  rw [h3, Real.exp_log ht, mul_comm]

theorem hasDerivAt_const_mul_exp_two (K₀ s : ℝ) :
    HasDerivAt (fun s => K₀ * Real.exp (2 * s)) (K₀ * (2 * Real.exp (2 * s))) s := by
  have h := ((Real.hasDerivAt_exp (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).const_mul K₀
  exact h.congr_deriv (by ring)

theorem exp_two_mul_log {t : ℝ} (ht : 0 < t) : Real.exp (2 * Real.log t) = t ^ 2 := by
  rw [mul_comm, Real.exp_mul, Real.rpow_two, Real.exp_log ht]

/-! ### the interface `ClauseEstimate` -/

/-- **the interface `ClauseEstimate`**: for `u` with `u + q` plurisubharmonic and locally
nondegenerate, `H = localCorrected Φ α u K₀` satisfies `H ≥ u`, is nondecreasing and strictly
convex in `log t`, its slope is bounded, and under the linear bound `H(z, t) ≤ u(z) + L t`
(`t ≤ C₁ r`) its slope is at most `C'(1 + L) r` for `t ≤ 2r`. -/
theorem clauseEstimate : DN9.ClauseEstimate N := by
  intro Φ O α U K q u hdata hq hpsh hne
  obtain ⟨hΦ, hU, hα, h11, hK, hKU, hKO⟩ := hdata
  -- the plurisubharmonic potential `p = u + q`
  have hne_p : ∀ x ∈ U, ∀ V : Set E, IsOpen V → x ∈ V → ∃ y ∈ V, u y + (q y : EReal) ≠ ⊥ := by
    intro x hx V hV hxV
    obtain ⟨y, hyV, hy⟩ := hne x hx V hV hxV
    exact ⟨y, hyV, EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩⟩
  obtain ⟨P, hPdef⟩ : ∃ P : E → ℝ → ℝ,
      P = fun z t => localSmoothing Φ α (fun y => (u y + (q y : EReal)).toReal) z t := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : E → ℝ → ℝ, Q = fun z t => localSmoothing Φ α q z t := ⟨_, rfl⟩
  have hPz' : ∀ z, P z = localSmoothing Φ α (fun y => (u y + (q y : EReal)).toReal) z :=
    fun z => by rw [hPdef]
  have hQz' : ∀ z, Q z = localSmoothing Φ α q z := fun z => by rw [hQdef]
  -- the `q`-part
  obtain ⟨Vq, rq, Cq, hVqo, hKVq, hVqU, hrq, hCq, hsq, hqrad⟩ :=
    exists_qRadial hΦ hU hα h11 hK hKU hKO hq
  -- regularity of `Ψ_p`
  obtain ⟨Vp, rp, hVpo, hKVp, hrp, hSp⟩ := DN11.contDiffOn_localSmoothing_toReal hΦ hU hα h11 hK
    hKU hKO hU hKU hpsh hne_p
  -- the splitting `Ψ_p = Ψ_u + Ψ_q`
  obtain ⟨Vy, ry, hVyo, hKVy, hry, hsplit⟩ := DN11.localSmoothing_toReal_split hΦ hU hα h11 hK
    hKU hKO hU hKU hpsh hne_p (g := q) hq.continuousOn (f := u) (fun y _ => rfl)
  -- uniform frames
  obtain ⟨R₀, hR₀, hframe⟩ := exists_frame_radius hΦ hU hα.continuousOn h11 hK hKU hKO
  -- radii
  set r₃ := min (min rp ry) rq with hr₃
  set r₄ := min R₀ r₃ with hr₄
  set r₁ := min r₄ 1 / 2 with hr₁
  have hr₃0 : 0 < r₃ := lt_min (lt_min hrp hry) hrq
  have hr₄0 : 0 < r₄ := lt_min hR₀ hr₃0
  have hr₁0 : 0 < r₁ := by rw [hr₁]; exact half_pos (lt_min hr₄0 one_pos)
  have hr₁4 : r₁ < r₄ := by
    rw [hr₁]; have := min_le_left r₄ 1; linarith
  have hr₁1 : r₁ ≤ 1 / 2 := by
    rw [hr₁]; have := min_le_right r₄ 1; linarith
  have hr₄R : r₄ ≤ R₀ := min_le_left _ _
  have hr₄3 : r₄ ≤ r₃ := min_le_right _ _
  have hr₃p : r₃ ≤ rp := (min_le_left _ _).trans (min_le_left _ _)
  have hr₃y : r₃ ≤ ry := (min_le_left _ _).trans (min_le_right _ _)
  have hr₃q : r₃ ≤ rq := min_le_right _ _
  -- smoothness of `Ψ_p` in `t`
  have hPsm : ∀ z ∈ K, ContDiffOn ℝ ∞ (P z) (Ioo 0 rp) := by
    intro z hz
    rw [hPdef]
    exact hSp.comp (contDiffOn_const.prodMk contDiffOn_id) fun t ht => ⟨hKVp hz, ht⟩
  -- the slope of `Ψ_p` at `r₁` is bounded on `K`
  have hD : IsOpen (Vp ×ˢ Ioo (0 : ℝ) rp) := hVpo.prod isOpen_Ioo
  set SP : E × ℝ → ℝ := fun x => P x.1 x.2 with hSPdef
  have hSPs : ContDiffOn ℝ ∞ SP (Vp ×ˢ Ioo (0 : ℝ) rp) := by rw [hSPdef, hPdef]; exact hSp
  have hdSP : ∀ z ∈ K, deriv (P z) r₁ = fderiv ℝ SP (z, r₁) (0, 1) := by
    intro z hz
    have hmem : ((z, r₁) : E × ℝ) ∈ Vp ×ˢ Ioo (0 : ℝ) rp :=
      ⟨hKVp hz, hr₁0, by linarith⟩
    have h1 : HasFDerivAt SP (fderiv ℝ SP (z, r₁)) (z, r₁) :=
      ((hSPs.differentiableOn (by norm_num)) _ hmem).differentiableAt (hD.mem_nhds hmem)
        |>.hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => ((z, t) : E × ℝ)) ((0 : E), (1 : ℝ)) r₁ :=
      (hasDerivAt_const r₁ z).prodMk (hasDerivAt_id r₁)
    exact (h1.comp_hasDerivAt r₁ h2).deriv
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ K, |deriv (P z) r₁| ≤ B := by
    have hc : ContinuousOn (fun z : E => fderiv ℝ SP (z, r₁) (0, 1)) K := by
      have h1 : ContinuousOn (fderiv ℝ SP) (Vp ×ˢ Ioo (0 : ℝ) rp) :=
        hSPs.continuousOn_fderiv_of_isOpen hD (by norm_cast)
      have h2 : ContinuousOn (fun z : E => fderiv ℝ SP (z, r₁)) K :=
        h1.comp (continuous_id.prodMk continuous_const).continuousOn
          fun z hz => ⟨hKVp hz, hr₁0, by linarith⟩
      exact h2.clm_apply continuousOn_const
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
    exact ⟨B, fun z hz => by rw [hdSP z hz, ← Real.norm_eq_abs]; exact hB z hz⟩
  refine ⟨r₁, Cq + 1, hr₁0, by linarith, fun K₀ hK₀ => ?_⟩
  have hK₀0 : 0 ≤ K₀ := by linarith
  refine ⟨max 0 (r₁ * B + Cq * r₁ ^ 2 + 2 * K₀ * r₁ ^ 2), 2 * Real.exp 1 + 4 * (Cq + 2 * K₀),
    2 * Real.exp 1, le_max_left _ _, by positivity,
    by linarith [Real.add_one_le_exp (1 : ℝ)], fun z hz => ?_⟩
  -- the data at the centre `z`
  obtain ⟨L, hL, hmaps⟩ := hframe z hz
  obtain ⟨hP1, hP2, hP3⟩ := radial_package hΦ α hpsh (hKO z hz) hL hR₀ hmaps
  have hP1' : ∀ t, 0 < t → t ≤ R₀ → u z + (q z : EReal) ≤ ((P z t : ℝ) : EReal) := by
    intro t ht htR
    rw [hPz' z]
    exact hP1 t ht htR
  have hP2' : MonotoneOn (P z) (Ioc 0 R₀) := by rw [hPz' z]; exact hP2
  have hP3' : ConvexOn ℝ (Iic (Real.log R₀)) (fun s => P z (Real.exp s)) := by
    rw [hPz' z]; exact hP3
  obtain ⟨hQ0, hQd, hQslope, q₁, q₂, hq12⟩ := hqrad z hz
  rw [← hQz' z] at hQ0 hQd hQslope hq12
  -- `H = Ψ_p - Ψ_q + K₀ t²` for `0 < t < r_y`
  have hHeq : ∀ t ∈ Ioo (0 : ℝ) ry, localCorrected Φ α u K₀ z t = P z t - Q z t + K₀ * t ^ 2 := by
    intro t ht
    have h := hsplit z (hKVy hz) t ht
    simp only [localCorrected, hPdef, hQdef]
    linarith
  -- the functions of `s = log t`
  set fP : ℝ → ℝ := fun s => P z (Real.exp s) with hfP
  set fH : ℝ → ℝ := fun s => localCorrected Φ α u K₀ z (Real.exp s) with hfH
  have hexp : ∀ s, s < Real.log r₄ → Real.exp s < r₄ := fun s hs =>
    (Real.lt_log_iff_exp_lt hr₄0).mp hs
  have hfPsm : ContDiffOn ℝ ∞ fP (Iio (Real.log rp)) :=
    (hPsm z hz).comp Real.contDiff_exp.contDiffOn fun s hs =>
      ⟨Real.exp_pos s, (Real.lt_log_iff_exp_lt hrp).mp hs⟩
  have hfPd : ∀ s, s < Real.log rp → HasDerivAt fP (deriv fP s) s := fun s hs =>
    ((hfPsm.differentiableOn (by norm_num)) s hs).differentiableAt
      (isOpen_Iio.mem_nhds hs) |>.hasDerivAt
  have hdfPsm : ContDiffOn ℝ ∞ (deriv fP) (Iio (Real.log rp)) :=
    hfPsm.deriv_of_isOpen isOpen_Iio (by norm_cast)
  have hfPdd : ∀ s, s < Real.log rp → HasDerivAt (deriv fP) (deriv (deriv fP) s) s :=
    fun s hs => ((hdfPsm.differentiableOn (by norm_num)) s hs).differentiableAt
      (isOpen_Iio.mem_nhds hs) |>.hasDerivAt
  have hlog4p : Real.log r₄ ≤ Real.log rp := Real.log_le_log hr₄0 (hr₄3.trans hr₃p)
  -- `H` in `log t`
  have hfHeq : ∀ s, s < Real.log r₄ →
      fH =ᶠ[𝓝 s] fun s' => fP s' - Q z (Real.exp s') + K₀ * Real.exp (2 * s') := by
    intro s hs
    filter_upwards [isOpen_Iio.mem_nhds hs] with s' hs'
    have h1 : Real.exp s' < ry := by
      have := hexp s' hs'; linarith [hr₄3, hr₃y]
    simp only [hfH, hfP]
    rw [hHeq _ ⟨Real.exp_pos s', h1⟩]
    congr 1
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hqd : ∀ s, s < Real.log r₄ → Real.exp s ≤ rq := fun s hs =>
    ((hexp s hs).trans_le (hr₄3.trans hr₃q)).le
  have hfHd : ∀ s, s < Real.log r₄ →
      HasDerivAt fH (deriv fP s - q₁ s + K₀ * (2 * Real.exp (2 * s))) s := by
    intro s hs
    have h := ((hfPd s (hs.trans_le hlog4p)).sub (hq12 s (hqd s hs)).1).add
      (hasDerivAt_const_mul_exp_two K₀ s)
    exact h.congr_of_eventuallyEq (hfHeq s hs)
  have hfHdd : ∀ s, s < Real.log r₄ →
      deriv (deriv fH) s = deriv (deriv fP) s - q₂ s + K₀ * (2 * (2 * Real.exp (2 * s))) := by
    intro s hs
    have hev : deriv fH =ᶠ[𝓝 s] fun s' => deriv fP s' - q₁ s' + K₀ * (2 * Real.exp (2 * s')) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with s' hs'
      exact (hfHd s' hs').deriv
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun s => K₀ * (2 * Real.exp (2 * s)))
        (K₀ * (2 * (2 * Real.exp (2 * s)))) s := by
      have := (hasDerivAt_const_mul_exp_two (2 * K₀) s)
      exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
        (Eventually.of_forall fun s' => by ring)
    exact (((hfPdd s (hs.trans_le hlog4p)).sub (hq12 s (hqd s hs)).2.1).add h2).deriv
  -- signs of the `p`-part on `s < log r₄`
  have hS : ∀ s, s < Real.log r₄ → s ≤ Real.log R₀ := fun s hs =>
    (hs.trans_le (Real.log_le_log hr₄0 hr₄R)).le
  have hfPmono : MonotoneOn fP (Iio (Real.log r₄)) := by
    intro x hx y hy hxy
    exact hP2' ⟨Real.exp_pos x, (Real.exp_le_exp.mpr (hS x hx)).trans (Real.exp_log hR₀).le⟩
      ⟨Real.exp_pos y, (Real.exp_le_exp.mpr (hS y hy)).trans (Real.exp_log hR₀).le⟩
      (Real.exp_le_exp.mpr hxy)
  have hfPconv : ConvexOn ℝ (Iio (Real.log r₄)) fP :=
    hP3'.subset (fun s hs => hS s hs) (convex_Iio _)
  have hdP0 : ∀ s, s < Real.log r₄ → 0 ≤ deriv fP s := fun s hs =>
    deriv_nonneg_of_monotoneOn hfPmono (isOpen_Iio.mem_nhds hs)
  have hdPmono : MonotoneOn (deriv fP) (Iio (Real.log r₄)) :=
    hfPconv.monotoneOn_deriv fun s hs => (hfPd s (lt_of_lt_of_le hs hlog4p)).differentiableAt
  have hddP0 : ∀ s, s < Real.log r₄ → 0 ≤ deriv (deriv fP) s := fun s hs =>
    deriv_nonneg_of_monotoneOn hdPmono (isOpen_Iio.mem_nhds hs)
  have he2 : ∀ s, 0 < Real.exp (2 * s) := fun s => Real.exp_pos _
  -- the second log-derivative of `H` is positive
  have hHdd_pos : ∀ s, s < Real.log r₄ → 0 < deriv (deriv fH) s := by
    intro s hs
    rw [hfHdd s hs]
    have h1 := hddP0 s hs
    have h2 := (hq12 s (hqd s hs)).2.2.2
    have h3 := (abs_le.mp h2).2
    nlinarith [he2 s]
  have hlog14 : Real.log r₁ < Real.log r₄ := Real.log_lt_log hr₁0 hr₁4
  -- the slope of `H` in `log t` is nondecreasing on `s ≤ log r₁`
  have hdHmono : MonotoneOn (deriv fH) (Iic (Real.log r₁)) := by
    have hdiff : ∀ s ∈ Iic (Real.log r₁), HasDerivAt (deriv fH) (deriv (deriv fH) s) s := by
      intro s hs
      have hs4 : s < Real.log r₄ := lt_of_le_of_lt hs hlog14
      have hev : deriv fH =ᶠ[𝓝 s] fun s' => deriv fP s' - q₁ s' + K₀ * (2 * Real.exp (2 * s')) := by
        filter_upwards [isOpen_Iio.mem_nhds hs4] with s' hs'
        exact (hfHd s' hs').deriv
      have h2 : HasDerivAt (fun s => K₀ * (2 * Real.exp (2 * s)))
          (K₀ * (2 * (2 * Real.exp (2 * s)))) s := by
        have := (hasDerivAt_const_mul_exp_two (2 * K₀) s)
        exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
          (Eventually.of_forall fun s' => by ring)
      have h := (((hfPdd s (hs4.trans_le hlog4p)).sub (hq12 s (hqd s hs4)).2.1).add h2)
      have h' := h.congr_of_eventuallyEq hev
      rw [h'.deriv]
      exact h'
    refine monotoneOn_of_deriv_nonneg (convex_Iic _)
      (fun s hs => (hdiff s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hdiff s (interior_subset (s := Iic (Real.log r₁)) hs)).differentiableAt
        |>.differentiableWithinAt)
      fun s hs => (hHdd_pos s (lt_of_le_of_lt
        (mem_Iic.mp (interior_subset (s := Iic (Real.log r₁)) hs)) hlog14)).le
  -- `t H'(t) = (d/ds) H(eˢ)` at `s = log t`
  have hHdiff : ∀ t, 0 < t → t < r₄ → DifferentiableAt ℝ (localCorrected Φ α u K₀ z) t := by
    intro t ht0 ht4
    have hev : localCorrected Φ α u K₀ z =ᶠ[𝓝 t] fun t' => P z t' - Q z t' + K₀ * t' ^ 2 := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (0 : ℝ) ry from
        ⟨ht0, by linarith [hr₄3, hr₃y]⟩)] with t' ht'
      exact hHeq t' ht'
    have h1 : DifferentiableAt ℝ (P z) t :=
      ((hPsm z hz).differentiableOn (by norm_num) t ⟨ht0, by linarith [hr₄3, hr₃p]⟩)
        |>.differentiableAt (isOpen_Ioo.mem_nhds ⟨ht0, by linarith [hr₄3, hr₃p]⟩)
    have h2 : DifferentiableAt ℝ (Q z) t :=
      hQd t (by rw [abs_of_pos ht0]; linarith [hr₄3, hr₃q])
    exact ((h1.sub h2).add ((differentiableAt_id.pow 2).const_mul K₀)).congr_of_eventuallyEq hev
  have hconv : ∀ t, 0 < t → t < r₄ →
      t * deriv (localCorrected Φ α u K₀ z) t = deriv fH (Real.log t) := fun t ht0 ht4 =>
    (deriv_comp_exp_log ht0 (hHdiff t ht0 ht4)).symm
  have hdPlog : ∀ t, 0 < t → t < r₄ → deriv fP (Real.log t) = t * deriv (P z) t := by
    intro t ht0 ht4
    exact deriv_comp_exp_log ht0 ((hPsm z hz).differentiableOn (by norm_num) t
      ⟨ht0, by linarith [hr₄3, hr₃p]⟩ |>.differentiableAt
        (isOpen_Ioo.mem_nhds ⟨ht0, by linarith [hr₄3, hr₃p]⟩))
  -- `u z ≠ ⊤`
  have hutop : u z ≠ ⊤ := by
    intro htop
    obtain ⟨V, -, hzV, hD'⟩ := hpsh z (hKU hz)
    apply hD'.ne_top z hzV
    rw [htop, EReal.top_add_coe]
  refine ⟨fun t ht0 htr => ?_, fun s hs => ?_, fun t ht0 htr => ?_, ?_⟩
  · -- clause (a): `u ≤ H`
    by_cases hbot : u z = ⊥
    · rw [hbot]; exact bot_le
    have hua : u z = (((u z).toReal : ℝ) : EReal) := (EReal.coe_toReal hutop hbot).symm
    set a := (u z).toReal with ha
    have htR : t ≤ R₀ := by linarith [hr₁4, hr₄R]
    have h1 := hP1' t ht0 htR
    rw [hua, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have h2 := hQ0 t (by rw [abs_of_pos ht0]; linarith [hr₁4, hr₄3, hr₃q])
    have h3 := hHeq t ⟨ht0, by linarith [hr₁4, hr₄3, hr₃y]⟩
    rw [hua, EReal.coe_le_coe_iff, h3]
    have h4 := (abs_le.mp h2).2
    nlinarith [sq_nonneg t]
  · -- clause (b): monotone and strictly convex in `log t`
    have hs4 : s < Real.log r₄ := hs.trans hlog14
    refine ⟨?_, hHdd_pos s hs4⟩
    rw [(hfHd s hs4).deriv]
    have h1 := hdP0 s hs4
    have h2 := (abs_le.mp (hq12 s (hqd s hs4)).2.2.1).2
    nlinarith [he2 s]
  · -- clause (c): the slope is bounded
    have ht4 : t < r₄ := htr.trans hr₁4
    rw [hconv t ht0 ht4]
    have hle : deriv fH (Real.log t) ≤ deriv fH (Real.log r₁) :=
      hdHmono (mem_Iic.mpr (Real.log_le_log ht0 htr.le)) (mem_Iic.mpr le_rfl)
        (Real.log_le_log ht0 htr.le)
    refine hle.trans (le_trans ?_ (le_max_right _ _))
    rw [(hfHd _ hlog14).deriv, hdPlog r₁ hr₁0 hr₁4, exp_two_mul_log hr₁0]
    have h1 := hB z hz
    have h2 := (abs_le.mp (hq12 _ (hqd _ hlog14)).2.2.1).1
    rw [exp_two_mul_log hr₁0] at h2
    have h3 : r₁ * deriv (P z) r₁ ≤ r₁ * B :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) hr₁0.le
    nlinarith
  · -- clause (d): the improved slope bound under the linear hypothesis
    intro a Lc r hua hL0 hr0 hC₁r hlin t ht0 ht2r
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2r : 2 * r ≤ 2 * Real.exp 1 * r := by nlinarith
    have h2r1 : 2 * r < r₁ := lt_of_le_of_lt h2r hC₁r
    have hr1 : r ≤ 1 := by linarith
    have ht4 : t < r₄ := by linarith
    have h2r4 : 2 * r < r₄ := by linarith
    have hC4 : 2 * Real.exp 1 * r < r₄ := by linarith
    -- `p(z) = a + q(z)`
    have hpz : ∀ t', 0 < t' → t' ≤ R₀ → a + q z ≤ P z t' := by
      intro t' ht' htR
      have := hP1' t' ht' htR
      rw [hua, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    -- `Ψ_p(z, t') ≤ p(z) + L t'` for `t' ≤ C₁ r`
    have hPlin : ∀ t', 0 < t' → t' ≤ 2 * Real.exp 1 * r → P z t' ≤ a + q z + Lc * t' := by
      intro t' ht' htC
      have h1 := hlin t' ht' htC
      have h2 := hHeq t' ⟨ht', by linarith [hr₄3, hr₃y]⟩
      have h3 := hQ0 t' (by rw [abs_of_pos ht']; linarith [hr₄3, hr₃q])
      have h4 := (abs_le.mp h3).2
      nlinarith [sq_nonneg t']
    -- convexity: `λ_p(2r) ≤ Ψ_p(2er) - Ψ_p(2r) ≤ 2eLr`
    have hlog2r : Real.log (2 * r) < Real.log r₄ := Real.log_lt_log (by positivity) h2r4
    have hlog2r1 : Real.log (2 * r) + 1 < Real.log r₄ := by
      have : Real.exp (Real.log (2 * r) + 1) = 2 * Real.exp 1 * r := by
        rw [Real.exp_add, Real.exp_log (by positivity)]; ring
      rw [Real.lt_log_iff_exp_lt hr₄0, this]; exact hC4
    have hslope := hfPconv.deriv_le_slope hlog2r hlog2r1 (by linarith)
      (hfPd _ (hlog2r.trans_le hlog4p)).differentiableAt
    rw [slope_def_field] at hslope
    have hfP2 : fP (Real.log (2 * r)) = P z (2 * r) := by
      simp only [hfP, Real.exp_log (show (0 : ℝ) < 2 * r by positivity)]
    have hfP2e : fP (Real.log (2 * r) + 1) = P z (2 * Real.exp 1 * r) := by
      simp only [hfP, Real.exp_add, Real.exp_log (show (0 : ℝ) < 2 * r by positivity)]
      ring_nf
    rw [hfP2, hfP2e, add_sub_cancel_left, div_one] at hslope
    have hA := hPlin (2 * Real.exp 1 * r) (by positivity) le_rfl
    have hB' := hpz (2 * r) (by positivity) (by linarith [hr₄R])
    have hlam2r : deriv fP (Real.log (2 * r)) ≤ Lc * (2 * Real.exp 1 * r) := by linarith
    -- monotonicity of `λ_p`
    have hlamt : deriv fP (Real.log t) ≤ deriv fP (Real.log (2 * r)) :=
      hdPmono (show Real.log t < Real.log r₄ from Real.log_lt_log ht0 ht4) hlog2r
        (Real.log_le_log ht0 ht2r)
    rw [hconv t ht0 ht4, (hfHd _ (Real.log_lt_log ht0 ht4)).deriv, exp_two_mul_log ht0]
    have hq := (abs_le.mp (hq12 _ (hqd _ (Real.log_lt_log ht0 ht4))).2.2.1).1
    rw [exp_two_mul_log ht0] at hq
    have ht2 : t ^ 2 ≤ 4 * r := by
      have h1 : t ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ ht0.le ht2r 2
      have h2 : (2 * r) ^ 2 = 4 * r * r := by ring
      have h3 : 4 * r * r ≤ 4 * r * 1 := mul_le_mul_of_nonneg_left hr1 (by positivity)
      linarith
    have F3 : Cq * t ^ 2 ≤ Cq * (4 * r) := mul_le_mul_of_nonneg_left ht2 hCq
    have F4 : K₀ * t ^ 2 ≤ K₀ * (4 * r) := mul_le_mul_of_nonneg_left ht2 hK₀0
    have F5 : 0 ≤ Real.exp 1 * r := mul_nonneg (Real.exp_pos 1).le hr0.le
    have F6 : 0 ≤ Cq * (Lc * r) := mul_nonneg hCq (mul_nonneg hL0 hr0.le)
    have F7 : 0 ≤ K₀ * (Lc * r) := mul_nonneg hK₀0 (mul_nonneg hL0 hr0.le)
    have F8 := hlamt.trans hlam2r
    have e1 : (2 * Real.exp 1 + 4 * (Cq + 2 * K₀)) * (1 + Lc) * r =
        2 * (Real.exp 1 * r) + 2 * Real.exp 1 * Lc * r + 4 * Cq * r + 8 * K₀ * r +
          4 * (Cq * (Lc * r)) + 8 * (K₀ * (Lc * r)) := by ring
    rw [e1]
    linarith

end SGPT.NPP.DN10
