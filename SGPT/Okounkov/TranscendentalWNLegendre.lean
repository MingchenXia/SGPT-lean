import SGPT.Okounkov.TranscendentalWNLegendreStatement
import SGPT.Okounkov.TranscendentalWNLegendreUSC
import SGPT.Foundations.Analysis.Pending.KiselmanMinimumPrincipleInterface
import SGPT.Foundations.Analysis.Pending.SubgeodesicInfimumThetaPsh
import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity
import Mathlib.Analysis.Convex.Deriv

/-!
# The partial Legendre transform: Kiselman's principle, concavity and duality (package WN-LEG)

Blueprint node `tok-wn:legendre` (chapter `claude-tok-wn`, supplement `claude-tok-wn-leg`);
source WN21 §3 (Definition 3.1 and the discussion after it, after Kiselman 1978), proved for
`π_M^* θ`-plurisubharmonic functions on `M × ℂ*` as WN21 asserts ("everything we established for
psh-functions works equally well for `θ`-psh functions, e.g. using a local potential for `θ`").

Let `u` be circle-invariant and plurisubharmonic on `W × ℂ*` (resp. `π_M^* θ`-psh on `M × ℂ*`),
and `û_λ(z) = inf_{τ ∈ ℂ*} (u(z, τ) - λ log |τ|²)` (`partialLegendre`).

* **Convexity of slices** (`slice_dichotomy`): for fixed `z`, `y ↦ u(z, e^{y/2})` is either
  identically `-∞` or real-valued and convex on `ℝ`.  The input is TN's local maximum principle
  for imaginary-translation-invariant psh functions
  (`PlurisubharmonicOn.comp_re_no_finite_strict_interior_max`, `comp_re_le_chord`).
* **Kiselman's minimum principle on lines** (`plurisubharmonicOn_iInf_real_slices`): if `Ψ` is
  psh on `W × ℂ` and depends on the second variable only through its real part, then
  `z ↦ inf_{t ∈ ℝ} Ψ(z, t)` is psh on `W`.  It is the decreasing limit of TN's strip version
  (`Pending.KiselmanMinimumPrinciple.plurisubharmonicOn_iInf_slices`, Demailly I.7.5) on the
  windows `(-k-1, k+1)`, rescaled affinely to the unit strip.  (This is the convex-slice case
  `Ω = W × ℂ`, `E = ℝ` of the corrected `prop:Kis`, `psh-deep-2:kiselman-corrected`.)
* **`û_λ` is (`θ`-)psh** (`plurisubharmonicOn_partialLegendre`,
  `thetaPlurisubharmonic_partialLegendre`): pull `u - λ log |τ|²` back by the holomorphic
  covering `(z, ζ) ↦ (z, e^{ζ/2})`; the result is psh on `W × ℂ`, depends only on `Re ζ` and
  its real slices are `t ↦ u(z, e^{t/2}) - λ t`, whose infimum is `û_λ(z)`.
* **Concavity** (`isConcaveFamilyAt_partialLegendre`): `λ ↦ û_λ(z)` is concave, as an infimum
  of affine functions of `λ`.
* **Legendre duality** (`partialLegendre_duality`, `partialLegendre_duality_of_thetaPsh`):
  `u(z, τ) = sup_{λ ∈ ℝ} (û_λ(z) + λ log |τ|²)` for `τ ≠ 0`, the one-dimensional
  Fenchel–Moreau theorem for the convex slice (a real convex function on `ℝ` has a subgradient
  at every point, `ConvexOn.rightDeriv_le_slope_of_mem_interior`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.FiniteGeodesicMaximality

/-! ### `EReal` bookkeeping -/

/-- `(x - c) + c = x` for a real `c`, including `x = ⊥, ⊤`. -/
theorem ereal_sub_add_cancel (x : EReal) (c : ℝ) : x - (c : EReal) + (c : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | coe r => rw [← EReal.coe_sub, ← EReal.coe_add]; simp
  | top => simp

/-- `(x + c) - c = x` for a real `c`, including `x = ⊥, ⊤`. -/
theorem ereal_add_sub_cancel (x : EReal) (c : ℝ) : x + (c : EReal) - (c : EReal) = x := by
  induction x using EReal.rec with
  | bot => simp
  | coe r => rw [← EReal.coe_add, ← EReal.coe_sub]; simp
  | top => simp

/-- `x - c = x + (-c)` for a real `c`. -/
theorem ereal_sub_coe_eq_add_neg (x : EReal) (c : ℝ) :
    x - (c : EReal) = x + ((-c : ℝ) : EReal) := by
  rw [EReal.coe_neg]; rfl

/-- `(x + c) - d = (x - d) + c` for real `c`, `d`. -/
theorem ereal_add_sub_comm (x : EReal) (c d : ℝ) :
    x + (c : EReal) - (d : EReal) = x - (d : EReal) + (c : EReal) := by
  rw [ereal_sub_coe_eq_add_neg, ereal_sub_coe_eq_add_neg, add_right_comm]

/-! ### `log |τ|²` and the exponential -/

theorem logNormSq_exp_half (t : ℝ) : logNormSq (Complex.exp ((t : ℂ) / 2)) = t := by
  have hre : ((t : ℂ) / 2).re = t / 2 := by simp
  rw [logNormSq, Complex.norm_exp, hre, ← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (t / 2) = t by ring, Real.log_exp]

theorem norm_exp_half (ζ : ℂ) : ‖Complex.exp (ζ / 2)‖ = Real.exp (ζ.re / 2) := by
  rw [Complex.norm_exp]; simp

theorem norm_exp_half_logNormSq {τ : ℂ} (hτ : τ ≠ 0) :
    ‖Complex.exp ((logNormSq τ : ℂ) / 2)‖ = ‖τ‖ := by
  rw [norm_exp_half]
  have hpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  simp only [Complex.ofReal_re, logNormSq]
  rw [Real.log_pow, show ((2 : ℕ) : ℝ) * Real.log ‖τ‖ / 2 = Real.log ‖τ‖ by push_cast; ring,
    Real.exp_log hpos]

/-- With circle invariance, `û_λ(x) = inf_{t ∈ ℝ} (u(x, e^{t/2}) - λ t)`. -/
theorem partialLegendre_eq_iInf_real {X : Type*} {u : X → ℂ → EReal}
    (hinv : IsCircleInvariant u) (lam : ℝ) (x : X) :
    partialLegendre u lam x =
      ⨅ t : ℝ, u x (Complex.exp ((t : ℂ) / 2)) - ((lam * t : ℝ) : EReal) := by
  apply le_antisymm
  · refine le_iInf fun t => ?_
    refine (iInf_le _ (⟨Complex.exp ((t : ℂ) / 2), Complex.exp_ne_zero _⟩ : puncturedPlane)).trans ?_
    simp only [logNormSq_exp_half, le_refl]
  · refine le_iInf fun τ => ?_
    refine (iInf_le _ (logNormSq τ)).trans ?_
    rw [hinv x _ τ (norm_exp_half_logNormSq τ.2)]

/-- With circle invariance, `u(x, τ) = u(x, e^{log|τ|²/2})` for `τ ≠ 0`. -/
theorem eq_exp_half_logNormSq {X : Type*} {u : X → ℂ → EReal} (hinv : IsCircleInvariant u)
    (x : X) {τ : ℂ} (hτ : τ ≠ 0) :
    u x τ = u x (Complex.exp ((logNormSq τ : ℂ) / 2)) :=
  hinv x _ _ (norm_exp_half_logNormSq hτ).symm

/-! ### Imaginary-translation-invariant subharmonic functions of one variable -/

section OneVariable

variable {v : ℝ → EReal}

/-- **Quasi-convexity**: if `ζ ↦ v(Re ζ)` is psh on `ℂ`, and `v(a) < C`, `v(b) < C` for a real
`C`, then `v(t) < C` for `t ∈ [a, b]`.  (TN's argument for the strip, on the whole line.) -/
theorem lt_of_plurisubharmonicOn_comp_re (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ)
    {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) {C : ℝ} (ha : v a < C) (hb : v b < C) :
    v t < C := by
  have hv' : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) (Complex.re ⁻¹' univ) := by
    simpa using hv
  rcases eq_or_lt_of_le hat with rfl | hat'
  · exact ha
  rcases eq_or_lt_of_le htb with rfl | htb'
  · exact hb
  by_contra hcon
  have hcon' : (C : EReal) ≤ v t := not_lt.mp hcon
  have husc : UpperSemicontinuousOn v (Icc a b) := by
    have hmap : MapsTo (fun s : ℝ => (s : ℂ)) (Icc a b) (univ : Set ℂ) := fun _ _ => trivial
    have := hv.upperSemicontinuousOn.comp Complex.continuous_ofReal.continuousOn hmap
    simpa [Function.comp_def] using this
  obtain ⟨x, hx, hmax⟩ :=
    husc.exists_isMaxOn ⟨a, left_mem_Icc.mpr (hat'.trans htb').le⟩ isCompact_Icc
  have htx : v t ≤ v x := hmax ⟨hat'.le, htb'.le⟩
  have hxtop : v x ≠ ⊤ := by
    have h := (hv (x : ℂ) (mem_univ _)).ne_top
    simpa using h
  have hCx : (C : EReal) ≤ v x := hcon'.trans htx
  have hax : v a < v x := ha.trans_le hCx
  have hbx : v b < v x := hb.trans_le hCx
  have hxbot : v x ≠ ⊥ := ne_bot_of_gt hax
  have hxI : x ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
    · rintro rfl; exact lt_irrefl _ hax
    · rintro rfl; exact lt_irrefl _ hbx
  have hxcoe : v x = (((v x).toReal : ℝ) : EReal) := (EReal.coe_toReal hxtop hxbot).symm
  exact hv'.comp_re_no_finite_strict_interior_max (subset_univ _) hxI
    (fun y hy => (hmax hy).trans hxcoe.le) hxcoe (lt_of_lt_of_eq hax hxcoe)
    (lt_of_lt_of_eq hbx hxcoe)

/-- Adding a real affine function of `Re ζ` keeps `ζ ↦ v(Re ζ)` psh. -/
theorem plurisubharmonicOn_comp_re_add_affine
    (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) (p q : ℝ) :
    PlurisubharmonicOn
      (fun ζ : ℂ => (fun s : ℝ => v s + ((p * s + q : ℝ) : EReal)) ζ.re) univ :=
  hv.add (plurisubharmonicOn_coe_affine_re p q univ)

/-- The reflection `s ↦ -s` keeps `ζ ↦ v(Re ζ)` psh. -/
theorem plurisubharmonicOn_comp_re_neg
    (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) :
    PlurisubharmonicOn (fun ζ : ℂ => (fun s : ℝ => v (-s)) ζ.re) univ := by
  have h := hv.comp_continuousLinearMap (-(ContinuousLinearMap.id ℂ ℂ))
  simpa using h

/-- **A pole propagates**: if `ζ ↦ v(Re ζ)` is psh on `ℂ` and `v(t₀) = -∞`, then `v ≡ -∞`. -/
theorem eq_bot_of_plurisubharmonicOn_comp_re
    (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) {t₀ : ℝ} (h0 : v t₀ = ⊥) (t : ℝ) :
    v t = ⊥ := by
  wlog hlt : t₀ < t generalizing v t₀ t
  · rcases eq_or_lt_of_le (not_lt.mp hlt) with heq | hgt
    · rw [heq, h0]
    · have h := this (v := fun s => v (-s)) (plurisubharmonicOn_comp_re_neg hv) (t₀ := -t₀)
        (by simpa using h0) (-t) (by linarith)
      simpa using h
  have hne : ∀ s : ℝ, v s ≠ ⊤ := by
    intro s
    have h := (hv (s : ℂ) (mem_univ _)).ne_top
    simpa using h
  obtain ⟨B, hB⟩ : ∃ B : ℝ, v (t + 1) < B := by
    obtain ⟨B, hB, -⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr (hne (t + 1)))
    exact ⟨B, hB⟩
  by_contra hbot
  set r : ℝ := (v t).toReal
  have hr : v t = (r : EReal) := (EReal.coe_toReal (hne t) hbot).symm
  set d : ℝ := t + 1 - t₀ with hd
  have hdpos : 0 < d := by linarith
  set θ : ℝ := (t - t₀) / d
  have hθ1 : θ < 1 := (div_lt_one hdpos).mpr (by linarith)
  -- the affine function through `(t₀, -L)` and `(t + 1, B)`
  set L : ℝ := (B * θ - r) / (1 - θ) + 1
  set p : ℝ := (B + L) / d
  set q : ℝ := -L - p * t₀
  have hw := lt_of_plurisubharmonicOn_comp_re (v := fun s => v s + ((-p * s + -q : ℝ) : EReal))
    (plurisubharmonicOn_comp_re_add_affine hv (-p) (-q))
    (a := t₀) (b := t + 1) (t := t) hlt.le (by linarith) (C := 0)
    (by simp only [h0, EReal.bot_add]; exact EReal.bot_lt_coe 0) (by
      show v (t + 1) + ((-p * (t + 1) + -q : ℝ) : EReal) < ((0 : ℝ) : EReal)
      have e : -p * (t + 1) + -q = -B := by
        simp only [q, p]; field_simp; ring
      rw [e]
      induction hvb : v (t + 1) using EReal.rec with
      | bot => simp
      | coe x =>
          rw [hvb] at hB
          have hx : x < B := EReal.coe_lt_coe_iff.mp hB
          rw [← EReal.coe_add]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
      | top => exact absurd hvb (hne _))
  rw [hr, ← EReal.coe_add] at hw
  have hw' : r + (-p * t + -q) < 0 := EReal.coe_lt_coe_iff.mp hw
  have hℓ : p * t + q = B * θ - (1 - θ) * L := by
    simp only [q, p, θ]; field_simp; ring
  have hL : (1 - θ) * L = B * θ - r + (1 - θ) := by
    simp only [L]
    have : 1 - θ ≠ 0 := by linarith
    field_simp
  nlinarith

/-- **Convexity of the finite slice**: if `ζ ↦ v(Re ζ)` is psh on `ℂ` and `v` never takes the
value `-∞`, then `t ↦ v(t)` is a real convex function. -/
theorem convexOn_toReal_of_plurisubharmonicOn_comp_re
    (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) (hfin : ∀ t, v t ≠ ⊥) :
    ConvexOn ℝ univ (fun t => (v t).toReal) := by
  have hv' : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) (Complex.re ⁻¹' univ) := by
    simpa using hv
  have hne : ∀ s : ℝ, v s ≠ ⊤ := by
    intro s
    have h := (hv (s : ℂ) (mem_univ _)).ne_top
    simpa using h
  have hco : ∀ s, v s = (((v s).toReal : ℝ) : EReal) :=
    fun s => (EReal.coe_toReal (hne s) (hfin s)).symm
  -- the chord inequality for `x < y`
  have key : ∀ x y : ℝ, x < y → ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      (v (a * x + b * y)).toReal ≤ a * (v x).toReal + b * (v y).toReal := by
    intro x y hxy a b ha hb hab
    set t := a * x + b * y
    have et1 : t - x = b * (y - x) := by simp only [t]; linear_combination x * hab
    have et2 : y - t = a * (y - x) := by simp only [t]; linear_combination (-y) * hab
    have hxt : x < t := by nlinarith [mul_pos hb (sub_pos.mpr hxy)]
    have hty : t < y := by nlinarith [mul_pos ha (sub_pos.mpr hxy)]
    have h := hv'.comp_re_le_chord hxt hty (subset_univ _) (hne x) (hfin x) (hne t) (hfin t)
      (hne y) (hfin y)
    have hyx : y - x ≠ 0 := by linarith
    have e1 : (y - t) / (y - x) = a := by
      rw [et2, mul_div_assoc, div_self hyx, mul_one]
    have e2 : (t - x) / (y - x) = b := by
      rw [et1, mul_div_assoc, div_self hyx, mul_one]
    rw [e1, e2, hco x, hco y, hco t, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
    exact EReal.coe_le_coe_iff.mp h
  refine convexOn_iff_forall_pos.mpr ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact key x y hxy a b ha hb hab
  · rw [← add_mul, hab, one_mul, ← add_mul, hab, one_mul]
  · have h := key y x hyx b a hb ha (by linarith)
    rw [add_comm (a * x), add_comm (a * (v x).toReal)]
    exact h

/-- **The slice dichotomy**: if `ζ ↦ v(Re ζ)` is psh on `ℂ`, then either `v ≡ -∞`, or `v` is
real-valued and `t ↦ v(t)` is convex. -/
theorem slice_dichotomy (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) :
    (∀ t, v t = ⊥) ∨ ((∀ t, v t ≠ ⊥) ∧ (∀ t, v t ≠ ⊤) ∧
      ConvexOn ℝ univ (fun t => (v t).toReal)) := by
  by_cases h : ∃ t₀, v t₀ = ⊥
  · obtain ⟨t₀, h0⟩ := h
    exact Or.inl (eq_bot_of_plurisubharmonicOn_comp_re hv h0)
  · simp only [not_exists] at h
    have hne : ∀ s : ℝ, v s ≠ ⊤ := by
      intro s
      have h := (hv (s : ℂ) (mem_univ _)).ne_top
      simpa using h
    exact Or.inr ⟨h, hne, convexOn_toReal_of_plurisubharmonicOn_comp_re hv h⟩

/-- A real convex function on `ℝ` has a subgradient at every point. -/
theorem exists_subgradient_of_convexOn {f : ℝ → ℝ} (hf : ConvexOn ℝ univ f) (y : ℝ) :
    ∃ lam : ℝ, ∀ t, f y + lam * (t - y) ≤ f t := by
  refine ⟨derivWithin f (Ioi y) y, fun t => ?_⟩
  have hy : y ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy y t with hyt | rfl | hty
  · have h := hf.rightDeriv_le_slope_of_mem_interior hy (mem_univ t) hyt
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h1 := hf.slope_le_leftDeriv_of_mem_interior (mem_univ t) hy hty
    have h2 := hf.leftDeriv_le_rightDeriv_of_mem_interior hy
    have h := h1.trans h2
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- **One-dimensional Legendre duality** (Fenchel–Moreau): if `ζ ↦ v(Re ζ)` is psh on `ℂ`, then
`v(y) = sup_λ (inf_t (v(t) - λ t) + λ y)` for every `y`. -/
theorem legendre_duality_slice (hv : PlurisubharmonicOn (fun ζ : ℂ => v ζ.re) univ) (y : ℝ) :
    v y = ⨆ lam : ℝ, (⨅ t : ℝ, v t - ((lam * t : ℝ) : EReal)) + ((lam * y : ℝ) : EReal) := by
  apply le_antisymm
  · rcases slice_dichotomy hv with hbot | ⟨hfin, hne, hconv⟩
    · rw [hbot y]; exact bot_le
    obtain ⟨lam, hlam⟩ := exists_subgradient_of_convexOn hconv y
    refine le_trans ?_ (le_iSup _ lam)
    have hco : ∀ s, v s = (((v s).toReal : ℝ) : EReal) :=
      fun s => (EReal.coe_toReal (hne s) (hfin s)).symm
    have hinf : (((v y).toReal - lam * y : ℝ) : EReal) ≤
        ⨅ t : ℝ, v t - ((lam * t : ℝ) : EReal) := by
      refine le_iInf fun t => ?_
      rw [hco t, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hlam t
      linarith
    calc v y = (((v y).toReal - lam * y : ℝ) : EReal) + ((lam * y : ℝ) : EReal) := by
          rw [← EReal.coe_add, sub_add_cancel, ← hco y]
      _ ≤ _ := add_le_add hinf le_rfl
  · refine iSup_le fun lam => ?_
    calc (⨅ t : ℝ, v t - ((lam * t : ℝ) : EReal)) + ((lam * y : ℝ) : EReal)
        ≤ (v y - ((lam * y : ℝ) : EReal)) + ((lam * y : ℝ) : EReal) :=
          add_le_add (iInf_le (fun t : ℝ => v t - ((lam * t : ℝ) : EReal)) y) le_rfl
      _ = v y := ereal_sub_add_cancel _ _

end OneVariable

/-! ### Kiselman's minimum principle on lines -/

section Kiselman

variable {m : ℕ}

/-- Affine reindexing: `inf_{0<s<1} f(2Rs - R) = inf_{-R<t<R} f(t)` for `R > 0`. -/
theorem iInf_window_eq (f : ℝ → EReal) {R : ℝ} (hR : 0 < R) :
    (⨅ s : Ioo (0 : ℝ) 1, f (2 * R * s - R)) = ⨅ t : Ioo (-R) R, f t := by
  apply le_antisymm
  · refine le_iInf fun t => ?_
    have hs : (t.1 + R) / (2 * R) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith [t.2.1]) (by linarith)
      · rw [div_lt_one (by linarith)]; linarith [t.2.2]
    refine (iInf_le _ ⟨_, hs⟩).trans (le_of_eq ?_)
    congr 1
    field_simp
    ring
  · refine le_iInf fun s => ?_
    have ht : 2 * R * s.1 - R ∈ Ioo (-R) R := by
      constructor <;> nlinarith [s.2.1, s.2.2]
    exact iInf_le (fun t : Ioo (-R) R => f t) ⟨_, ht⟩

/-- **Kiselman's minimum principle, line version.**  If `Ψ` is psh on `W × ℂ` and depends on the
second variable only through its real part, then `y ↦ inf_{t ∈ ℝ} Ψ(y, t)` is psh on `W`
(the value `-∞` is allowed). -/
theorem plurisubharmonicOn_iInf_real_slices {W : Set (ComplexModel m)} (hW : IsOpen W)
    {Ψ : ComplexModel m × ℂ → EReal} (hΨ : PlurisubharmonicOn Ψ (W ×ˢ univ))
    (hinv : ∀ (y : ComplexModel m) (τ σ : ℂ), τ.re = σ.re → Ψ (y, τ) = Ψ (y, σ)) :
    PlurisubharmonicOn (fun y => ⨅ t : ℝ, Ψ (y, (t : ℂ))) W := by
  -- the windows `(-k-1, k+1)`
  set g : ℕ → ComplexModel m → EReal := fun k y => ⨅ t : Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1),
    Ψ (y, ((t : ℝ) : ℂ)) with hg
  have hgpsh : ∀ k, PlurisubharmonicOn (g k) W := by
    intro k
    set R : ℝ := (k : ℝ) + 1 with hRdef
    have hR : 0 < R := by positivity
    let L : ComplexModel m × ℂ →L[ℂ] ComplexModel m × ℂ :=
      (ContinuousLinearMap.fst ℂ (ComplexModel m) ℂ).prod
        ((2 * R : ℂ) • ContinuousLinearMap.snd ℂ (ComplexModel m) ℂ)
    let b : ComplexModel m × ℂ := (0, -(R : ℂ))
    have hLb : ∀ p : ComplexModel m × ℂ, b + L p = (p.1, 2 * (R : ℂ) * p.2 - R) := by
      intro p
      refine Prod.ext ?_ ?_
      · simp [b, L]
      · simp [b, L]; ring
    have h1 := hΨ.comp_affine L b
    have h2 : PlurisubharmonicOn (fun p => Ψ (b + L p)) (W ×ˢ complexTimeStrip) := by
      refine h1.mono fun p hp => ?_
      simp only [mem_preimage, hLb]
      exact ⟨hp.1, mem_univ _⟩
    have hinv2 : ∀ (y : ComplexModel m) (τ σ : ℂ), τ.re = σ.re →
        Ψ (b + L (y, τ)) = Ψ (b + L (y, σ)) := by
      intro y τ σ h
      rw [hLb, hLb]
      apply hinv
      simp [h]
    have hk := KiselmanMinimumPrinciple.plurisubharmonicOn_iInf_slices hW h2 hinv2
    have hfun : (fun y => ⨅ t : ↥(Ioo (0 : ℝ) 1), Ψ (b + L (y, ((t : ℝ) : ℂ)))) = g k := by
      funext y
      simp only [hg, hLb]
      rw [← iInf_window_eq (fun t : ℝ => Ψ (y, (t : ℂ))) hR]
      apply iInf_congr
      intro s
      congr 2
      push_cast
      ring
    rwa [hfun] at hk
  have hanti : ∀ y ∈ W, Antitone (fun k => g k y) := by
    intro y _ i j hij
    refine le_iInf fun t => ?_
    have hcast : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
    have ht : (t : ℝ) ∈ Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1) :=
      ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
    exact iInf_le (fun s : Ioo (-((j : ℝ) + 1)) ((j : ℝ) + 1) => Ψ (y, ((s : ℝ) : ℂ))) ⟨_, ht⟩
  have hlim := DiscPshOn.plurisubharmonicOn_iInf_of_antitone hW
    (fun k => (hgpsh k).discPshOn) hanti
  have hfun : (fun y => ⨅ k, g k y) = fun y => ⨅ t : ℝ, Ψ (y, (t : ℂ)) := by
    funext y
    apply le_antisymm
    · refine le_iInf fun t => ?_
      obtain ⟨k, hk⟩ := exists_nat_gt |t|
      have ht : t ∈ Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1) := by
        constructor
        · linarith [neg_abs_le t]
        · linarith [le_abs_self t]
      exact (iInf_le (fun k => g k y) k).trans
        (iInf_le (fun s : Ioo (-((k : ℝ) + 1)) ((k : ℝ) + 1) => Ψ (y, ((s : ℝ) : ℂ))) ⟨t, ht⟩)
    · refine le_iInf fun k => le_iInf fun t => ?_
      exact iInf_le (fun s : ℝ => Ψ (y, (s : ℂ))) t
  rwa [hfun] at hlim

end Kiselman

/-! ### The partial Legendre transform is plurisubharmonic (local form) -/

section Local

variable {m : ℕ}

/-- **Pull-back by `(z, ζ) ↦ (z, e^{ζ/2})`**: if `(z, τ) ↦ u(z, τ)` is psh on `W × ℂ*`, then
`(z, ζ) ↦ u(z, e^{ζ/2})` is psh on `W × ℂ`. -/
theorem plurisubharmonicOn_comp_exp_half {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane)) :
    PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 (Complex.exp (p.2 / 2)))
      (W ×ˢ univ) := by
  have hF : DifferentiableOn ℂ (fun p : ComplexModel m × ℂ => (p.1, Complex.exp (p.2 / 2)))
      (W ×ˢ univ) := by
    refine DifferentiableOn.prodMk differentiableOn_fst ?_
    have hd : Differentiable ℂ (fun p : ComplexModel m × ℂ => p.2 / 2) := by fun_prop
    exact (Complex.differentiable_exp.comp hd).differentiableOn
  have hmaps : MapsTo (fun p : ComplexModel m × ℂ => (p.1, Complex.exp (p.2 / 2)))
      (W ×ˢ univ) (W ×ˢ puncturedPlane) :=
    fun p hp => ⟨hp.1, Complex.exp_ne_zero _⟩
  exact plurisubharmonicOn_comp_holomorphic_strip (hW.prod isOpen_univ) hF hmaps hu

/-- The function `(z, ζ) ↦ u(z, e^{ζ/2}) - λ Re ζ` whose real slices give `û_λ`. -/
def logLegendreFunction (u : ComplexModel m → ℂ → EReal) (lam : ℝ) :
    ComplexModel m × ℂ → EReal :=
  fun p => u p.1 (Complex.exp (p.2 / 2)) - ((lam * p.2.re : ℝ) : EReal)

theorem plurisubharmonicOn_logLegendreFunction {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane))
    (lam : ℝ) :
    PlurisubharmonicOn (logLegendreFunction u lam) (W ×ˢ univ) := by
  have h1 := plurisubharmonicOn_comp_exp_half hW hu
  have h2 : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => ((-lam * p.2.re + 0 : ℝ) : EReal))
      (W ×ˢ univ) := by
    have := (plurisubharmonicOn_coe_affine_re (-lam) 0 univ).comp_continuousLinearMap
      (ContinuousLinearMap.snd ℂ (ComplexModel m) ℂ)
    exact this.mono fun _ _ => mem_univ _
  have h := h1.add h2
  have hfun : (fun p : ComplexModel m × ℂ =>
      u p.1 (Complex.exp (p.2 / 2)) + ((-lam * p.2.re + 0 : ℝ) : EReal)) =
      logLegendreFunction u lam := by
    funext p
    simp only [logLegendreFunction, add_zero, neg_mul]
    rw [ereal_sub_coe_eq_add_neg]
  rwa [hfun] at h

theorem logLegendreFunction_re_invariant {u : ComplexModel m → ℂ → EReal}
    (hinv : IsCircleInvariant u) (lam : ℝ) (y : ComplexModel m) (τ σ : ℂ) (h : τ.re = σ.re) :
    logLegendreFunction u lam (y, τ) = logLegendreFunction u lam (y, σ) := by
  simp only [logLegendreFunction]
  rw [hinv y _ (Complex.exp (σ / 2)) (by rw [norm_exp_half, norm_exp_half, h]), h]

/-- **`û_λ` is psh** (`tok-wn:legendre`, Kiselman): for `u` circle-invariant and psh on
`W × ℂ*`, every partial Legendre transform `û_λ` is psh on `W` (possibly `≡ -∞`). -/
theorem plurisubharmonicOn_partialLegendre {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane))
    (hinv : IsCircleInvariant u) (lam : ℝ) :
    PlurisubharmonicOn (partialLegendre u lam) W := by
  have h := plurisubharmonicOn_iInf_real_slices hW (plurisubharmonicOn_logLegendreFunction hW hu lam)
    (logLegendreFunction_re_invariant hinv lam)
  have hfun : (fun y => ⨅ t : ℝ, logLegendreFunction u lam (y, (t : ℂ))) = partialLegendre u lam := by
    funext y
    rw [partialLegendre_eq_iInf_real hinv]
    simp only [logLegendreFunction, Complex.ofReal_re]
  rwa [hfun] at h

/-- The log-coordinate slice of a psh `u` on `W × ℂ*` at `z ∈ W`. -/
theorem plurisubharmonicOn_slice_comp_re {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane))
    (hinv : IsCircleInvariant u) {z : ComplexModel m} (hz : z ∈ W) :
    PlurisubharmonicOn
      (fun ζ : ℂ => (fun t : ℝ => u z (Complex.exp ((t : ℂ) / 2))) ζ.re) univ := by
  have h1 := (plurisubharmonicOn_comp_exp_half hW hu).comp_affine
    (ContinuousLinearMap.inr ℂ (ComplexModel m) ℂ) ((z, 0) : ComplexModel m × ℂ)
  have h2 : PlurisubharmonicOn (fun ζ : ℂ => u z (Complex.exp (ζ / 2))) univ := by
    have h3 := h1.mono (V := univ) fun ζ _ => by simp [hz]
    simpa using h3
  refine fun ζ _ => (h2 ζ (mem_univ _)).congr (Eventually.of_forall fun ξ => ?_)
  exact hinv z _ _ (by rw [norm_exp_half, norm_exp_half]; simp)

/-- **Legendre duality** (local form): `u(z, τ) = sup_λ (û_λ(z) + λ log |τ|²)` for `z ∈ W`,
`τ ≠ 0`. -/
theorem partialLegendre_duality {W : Set (ComplexModel m)} (hW : IsOpen W)
    {u : ComplexModel m → ℂ → EReal}
    (hu : PlurisubharmonicOn (fun p : ComplexModel m × ℂ => u p.1 p.2) (W ×ˢ puncturedPlane))
    (hinv : IsCircleInvariant u) {z : ComplexModel m} (hz : z ∈ W) {τ : ℂ} (hτ : τ ≠ 0) :
    u z τ = ⨆ lam : ℝ, partialLegendre u lam z + ((lam * logNormSq τ : ℝ) : EReal) := by
  have h := legendre_duality_slice (v := fun t : ℝ => u z (Complex.exp ((t : ℂ) / 2)))
    (plurisubharmonicOn_slice_comp_re hW hu hinv hz) (logNormSq τ)
  rw [← eq_exp_half_logNormSq hinv z hτ] at h
  rw [h]
  simp only [partialLegendre_eq_iInf_real hinv]

end Local

/-! ### Concavity in `λ` -/

/-- The chord identity behind concavity, in `EReal`. -/
theorem ereal_chord_sub_le (x : EReal) (c₁ c₂ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : EReal) * (x - (c₁ : EReal)) + ((1 - t : ℝ) : EReal) * (x - (c₂ : EReal)) ≤
      x - ((t * c₁ + (1 - t) * c₂ : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot =>
      simp only [EReal.bot_sub]
      rcases eq_or_lt_of_le ht0 with h0 | hpos
      · subst h0
        simp
      · rw [EReal.coe_mul_bot_of_pos hpos, EReal.bot_add]
  | coe r =>
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      nlinarith
  | top => rw [EReal.top_sub_coe]; exact le_top

/-- **Concavity** (`tok-wn:legendre`): `λ ↦ û_λ(x)` is concave, for every `u` and `x`. -/
theorem isConcaveFamilyAt_partialLegendre {X : Type*} (u : X → ℂ → EReal) (I : Set ℝ) (x : X) :
    IsConcaveFamilyAt (fun lam => partialLegendre u lam) I x := by
  intro l₁ _ l₂ _ t ht0 ht1
  refine le_iInf fun τ => ?_
  have h1 : partialLegendre u l₁ x ≤ u x τ - ((l₁ * logNormSq τ : ℝ) : EReal) := iInf_le _ τ
  have h2 : partialLegendre u l₂ x ≤ u x τ - ((l₂ * logNormSq τ : ℝ) : EReal) := iInf_le _ τ
  have ht0' : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast ht0
  have ht1' : (0 : EReal) ≤ ((1 - t : ℝ) : EReal) := by exact_mod_cast (by linarith : 0 ≤ 1 - t)
  calc (t : EReal) * partialLegendre u l₁ x + ((1 - t : ℝ) : EReal) * partialLegendre u l₂ x
      ≤ (t : EReal) * (u x τ - ((l₁ * logNormSq τ : ℝ) : EReal)) +
          ((1 - t : ℝ) : EReal) * (u x τ - ((l₂ * logNormSq τ : ℝ) : EReal)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ht0') (mul_le_mul_of_nonneg_left h2 ht1')
    _ ≤ u x τ - ((t * (l₁ * logNormSq τ) + (1 - t) * (l₂ * logNormSq τ) : ℝ) : EReal) :=
        ereal_chord_sub_le _ _ _ t ht0 ht1
    _ = u x τ - (((t * l₁ + (1 - t) * l₂) * logNormSq τ : ℝ) : EReal) := by
        congr 2; ring

/-! ### The manifold form: `π_M^* θ`-psh functions on `M × ℂ*` -/

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

instance : Nonempty puncturedPlane := ⟨⟨1, one_ne_zero⟩⟩

omit [IsComplexManifold n M] in
/-- In a chart, the partial Legendre transform of the corrected complexification is the chart
expression of `û_λ` plus the local potential. -/
theorem partialLegendre_stripChartFunction (u : M → ℂ → EReal) (e : ComplexChart n M)
    (ρ : ComplexModel n → ℝ) (lam : ℝ) (z : ComplexModel n) :
    partialLegendre (fun z' τ => stripChartFunction u e ρ (z', τ)) lam z =
      chartFunction (partialLegendre u lam) e z + (ρ z : EReal) := by
  simp only [partialLegendre, stripChartFunction, chartFunction]
  rw [SubgeodesicInfimumThetaPsh.iInf_add_coe]
  exact iInf_congr fun τ => ereal_add_sub_comm _ _ _

omit [IsComplexManifold n M] in
theorem isCircleInvariant_stripChartFunction {u : M → ℂ → EReal} (hinv : IsCircleInvariant u)
    (e : ComplexChart n M) (ρ : ComplexModel n → ℝ) :
    IsCircleInvariant (fun z' τ => stripChartFunction u e ρ (z', τ)) := by
  intro z τ σ h
  simp only [stripChartFunction]
  rw [hinv _ τ σ h]

/-- **`û_λ` is `θ`-psh** (`tok-wn:legendre`, Kiselman's minimum principle): if
`u ∈ PSH(M × ℂ*, π_M^* θ)` is circle-invariant, then `û_λ` satisfies the `θ`-psh criterion
`ThetaPlurisubharmonic θ` for every `λ` (it may be `≡ -∞`). -/
theorem thetaPlurisubharmonic_partialLegendre {θ : SmoothRealForm n M 2} {u : M → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u) (lam : ℝ) :
    ThetaPlurisubharmonic θ (partialLegendre u lam) := by
  intro e z hz
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e z hz
  refine ⟨W, ρ, hzW, hρ, ?_⟩
  have h := plurisubharmonicOn_partialLegendre hρ.1 (u := fun z' τ => stripChartFunction u e ρ (z', τ))
    hpsh (isCircleInvariant_stripChartFunction hinv e ρ) lam
  have hfun : partialLegendre (fun z' τ => stripChartFunction u e ρ (z', τ)) lam =
      fun y => chartFunction (partialLegendre u lam) e y + (ρ y : EReal) :=
    funext (partialLegendre_stripChartFunction u e ρ lam)
  rwa [hfun] at h

/-- **`û_λ ∈ PSH(M, θ) ∪ {-∞}`**: on a connected manifold, `û_λ` is either identically `-∞` or a
genuine `θ`-psh potential (`IsThetaPshPotential`, which excludes local `-∞`). -/
theorem partialLegendre_eq_bot_or_isThetaPshPotential [ConnectedSpace M]
    {θ : SmoothRealForm n M 2} {u : M → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u) (lam : ℝ) :
    (∀ x, partialLegendre u lam x = ⊥) ∨ IsThetaPshPotential θ (partialLegendre u lam) := by
  by_cases h : ∃ x, partialLegendre u lam x ≠ ⊥
  · have : Nonempty M := ⟨h.choose⟩
    exact Or.inr (ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
      (thetaPlurisubharmonic_partialLegendre hu hinv lam) h)
  · simp only [ne_eq, not_exists, not_not] at h
    exact Or.inl h

/-- The log-coordinate slice of `u` at a point `x` of `M`, read in the chart at `x`: it is psh
after adding the constant `ρ(e x)`, hence psh. -/
theorem plurisubharmonicOn_manifold_slice {θ : SmoothRealForm n M 2} {u : M → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u) (x : M) :
    PlurisubharmonicOn
      (fun ζ : ℂ => (fun t : ℝ => u x (Complex.exp ((t : ℂ) / 2))) ζ.re) univ := by
  set e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu e (e.val x) hz
  have h := plurisubharmonicOn_slice_comp_re hρ.1 (u := fun z' τ => stripChartFunction u e ρ (z', τ))
    hpsh (isCircleInvariant_stripChartFunction hinv e ρ) hzW
  have hc : PlurisubharmonicOn (fun _ : ℂ => (((-ρ (e.val x)) : ℝ) : EReal)) univ :=
    fun ζ _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) ζ
  have h2 := h.add hc
  have hfun : (fun ζ : ℂ => (fun t : ℝ => stripChartFunction u e ρ (e.val x,
      Complex.exp ((t : ℂ) / 2))) ζ.re + (((-ρ (e.val x)) : ℝ) : EReal)) =
      fun ζ : ℂ => (fun t : ℝ => u x (Complex.exp ((t : ℂ) / 2))) ζ.re := by
    funext ζ
    simp only [stripChartFunction, e.val.left_inv hx]
    rw [← ereal_sub_coe_eq_add_neg, ereal_add_sub_cancel]
  rwa [hfun] at h2

/-- **Legendre duality** (`tok-wn:legendre`, manifold form): for `u ∈ PSH(M × ℂ*, π_M^* θ)`
circle-invariant, `u(x, τ) = sup_{λ ∈ ℝ} (û_λ(x) + λ log |τ|²)` for every `x` and `τ ≠ 0`. -/
theorem partialLegendre_duality_of_thetaPsh {θ : SmoothRealForm n M 2} {u : M → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u) (x : M) {τ : ℂ}
    (hτ : τ ≠ 0) :
    u x τ = ⨆ lam : ℝ, partialLegendre u lam x + ((lam * logNormSq τ : ℝ) : EReal) := by
  have h := legendre_duality_slice (v := fun t : ℝ => u x (Complex.exp ((t : ℂ) / 2)))
    (plurisubharmonicOn_manifold_slice hu hinv x) (logNormSq τ)
  rw [← eq_exp_half_logNormSq hinv x hτ] at h
  rw [h]
  simp only [partialLegendre_eq_iInf_real hinv]

/-- **Convexity of slices** (`tok-wn:legendre`, manifold form): for fixed `x`, the function
`y ↦ u(x, e^{y/2})` is identically `-∞` or real-valued and convex on `ℝ`. -/
theorem slice_dichotomy_of_thetaPsh {θ : SmoothRealForm n M 2} {u : M → ℂ → EReal}
    (hu : IsPullbackThetaPshPunctured θ u) (hinv : IsCircleInvariant u) (x : M) :
    (∀ y : ℝ, u x (Complex.exp ((y : ℂ) / 2)) = ⊥) ∨
      ((∀ y : ℝ, u x (Complex.exp ((y : ℂ) / 2)) ≠ ⊥) ∧
        (∀ y : ℝ, u x (Complex.exp ((y : ℂ) / 2)) ≠ ⊤) ∧
        ConvexOn ℝ univ (fun y : ℝ => (u x (Complex.exp ((y : ℂ) / 2))).toReal)) :=
  slice_dichotomy (plurisubharmonicOn_manifold_slice hu hinv x)

end Manifold

end SGPT.Okounkov.TranscendentalWN
