import SGPT.NPP.DN5LocalKernel
import SGPT.NPP.DN3RadialConvex
import SGPT.NPP.DN9Interface
import SGPT.NPP.DN10Taylor

/-!
# The smoothing of the smooth local potential `q` (the `q`-part)

Lane DN10, `thm:DNT23_C11bar` (`chapter_npp.tex`), via FPT `lem:chern-joint-smoothing`
(`chapters/inputs/q10-big-envelope-regularity.tex`, Step 5, paragraph "It remains to subtract the
smoothing of the smooth function `q`").

FPT: "Since `q` is smooth, `Ψ_q(z, w)` is smooth also at `w = 0`, where it equals `q(z)`.  By
rotation invariance, the terms of degree one and the terms in `w²` and `w̄²` of its Taylor
expansion in `w` vanish, so `Ψ_q(z, w) - q(z)` is `|w|²` times a smooth function of `z`, up to an
error `O(|w|³)` whose derivatives lose one power of `|w|` for each derivative in `w`.  Hence
`α[v]² - D Ψ_q[v, η]² ≥ -C r²|v|² - C r|v||η| - C_q|η|²`."

* `localSmoothingC Φ α f z w` — the chart-level smoothing `SGPT.NPP.DN5.localSmoothing` with a
  complex radius `w` (same formula with `w • ξ`); `localSmoothingC_ofReal`.
* `localWeight_rotate`, `localSmoothingC_rotate`, `localSmoothingC_eq_norm` — rotation invariance:
  `Ψ_f(z, w) = Ψ_f(z, |w|)` (for any real two-form `α`).
* `exists_smoothDomain` — `(z, w) ↦ Ψ_f(z, w)` is `C^∞` on a neighbourhood `V × B(0, ρ)` of
  `K × {0}`, for every `f` smooth on `U` (differentiation under the integral sign; the weight has
  uniformly compact support).
* `exists_qPart` — with `E(z, w) = Ψ_q(z, w) - q(z)` (even in `w`, zero at `w = 0`) and lane DN10's
  `exists_even_taylor_bounds`: `|E| ≤ C|w|²`, `|∂_w E[b]| ≤ C|w||b|`,
  `|D²E[(a, b)]²| ≤ C(|w|²|a|² + |w||a||b| + |b|²)` on `K × B̄(0, r)`.
* `qPartEstimate` — **the interface `SGPT.NPP.DN9.QPartEstimate`**.
* `exists_qRadial` — the radial bounds used for the clauses: `|Ψ_q(z, t) - q(z)| ≤ C t²` and the
  first two derivatives of `s ↦ Ψ_q(z, eˢ)` are `O(e^{2s})`.
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

/-! ### The smoothing with a complex radius -/

/-- The chart-level smoothing with a complex radius `w`:
`Ψ_f(z, w) = (∫ f(Φ(z, w ξ)) χ(π α_z(ξ, iξ)) dξ) / ∫ χ(π α_z(ξ, iξ)) dξ`. -/
def localSmoothingC (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ) (z : E) (w : ℂ) :
    ℝ :=
  (∫ ξ, f (Φ z (w • ξ)) * localWeight α z ξ) / ∫ ξ, localWeight α z ξ

theorem localSmoothingC_ofReal (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ)
    (z : E) (t : ℝ) : localSmoothingC Φ α f z (t : ℂ) = localSmoothing Φ α f z t := by
  simp only [localSmoothingC, localSmoothing, localWeight, Complex.coe_smul]

theorem twoForm_self (β : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) : β ![u, u] = 0 := by
  have := twoForm_swap β u u
  linarith

/-- `α(c ξ, i c ξ) = α(ξ, i ξ)` for `|c| = 1` (any real two-form). -/
theorem twoForm_rotate (β : E [⋀^Fin 2]→L[ℝ] ℝ) {c : ℂ} (hc : ‖c‖ = 1) (ξ : E) :
    β ![c • ξ, Complex.I • (c • ξ)] = β ![ξ, Complex.I • ξ] := by
  have hcξ : c • ξ = c.re • ξ + c.im • (Complex.I • ξ) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hII : Complex.I • Complex.I • ξ = -ξ := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have hIcξ : Complex.I • (c • ξ) = c.re • (Complex.I • ξ) + (-c.im) • ξ := by
    rw [hcξ, smul_add, smul_comm Complex.I c.re, smul_comm Complex.I c.im, hII, smul_neg,
      neg_smul]
  have hn : c.re ^ 2 + c.im ^ 2 = 1 := by
    have h := Complex.sq_norm c
    rw [hc, Complex.normSq_apply] at h
    nlinarith [h]
  have hs := twoForm_swap β ξ (Complex.I • ξ)
  rw [hIcξ, hcξ]
  simp only [twoForm_add_left, twoForm_add_right, twoForm_smul_left, twoForm_smul_right,
    twoForm_self]
  rw [hs]
  linear_combination (β ![ξ, Complex.I • ξ]) * hn

theorem localWeight_rotate (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) {c : ℂ} (hc : ‖c‖ = 1) (z ξ : E) :
    localWeight α z (c • ξ) = localWeight α z ξ := by
  simp only [localWeight, twoForm_rotate (α z) hc ξ]

/-- Rotations preserve the Lebesgue measure. -/
theorem integral_rotate' (f : E → ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ∫ ζ, f (a • ζ) = ∫ ζ, f ζ :=
  (DN3.unitRotation (n := N) a ha).measurePreserving.integral_comp
    (DN3.unitRotation a ha).toHomeomorph.measurableEmbedding f

/-- **Rotation invariance**: `Ψ_f(z, c w) = Ψ_f(z, w)` for `|c| = 1`. -/
theorem localSmoothingC_rotate (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ)
    (z : E) {c : ℂ} (hc : ‖c‖ = 1) (w : ℂ) :
    localSmoothingC Φ α f z (c * w) = localSmoothingC Φ α f z w := by
  simp only [localSmoothingC]
  congr 1
  have h := integral_rotate' (fun ζ => f (Φ z (w • ζ)) * localWeight α z ζ) c hc
  simp only [localWeight_rotate α hc, smul_smul] at h
  rw [← h]
  congr 1
  funext ζ
  rw [mul_comm w c]

/-- `Ψ_f(z, w) = Ψ_f(z, |w|)`. -/
theorem localSmoothingC_eq_norm (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ)
    (z : E) (w : ℂ) : localSmoothingC Φ α f z w = localSmoothing Φ α f z ‖w‖ := by
  rw [← localSmoothingC_ofReal]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hc : ‖(w / (‖w‖ : ℂ))‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]
  have e : (w / (‖w‖ : ℂ)) * (‖w‖ : ℂ) = w := by
    rw [div_mul_cancel₀]
    exact_mod_cast hn
  conv_lhs => rw [← e]
  exact localSmoothingC_rotate Φ α f z hc _

theorem localSmoothingC_neg (Φ : E → E → E) (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ)
    (z : E) (w : ℂ) : localSmoothingC Φ α f z (-w) = localSmoothingC Φ α f z w := by
  have := localSmoothingC_rotate Φ α f z (c := -1) (by simp) w
  simpa using this

theorem localSmoothingC_zero {Φ : E → E → E} (α : E → E [⋀^Fin 2]→L[ℝ] ℝ) (f : E → ℝ) {z : E}
    (hΦ0 : Φ z 0 = z) (hpos : 0 < ∫ ξ, localWeight α z ξ) :
    localSmoothingC Φ α f z 0 = f z := by
  simp only [localSmoothingC, zero_smul, hΦ0]
  rw [integral_const_mul, mul_div_assoc, div_self hpos.ne', mul_one]

/-! ### Joint smoothness near the zero section -/

/-- Differentiation under the integral sign for an integrand with a uniform compact support
(the argument of `SGPT.NPP.DNTBig.contDiffOn_integral_of_actual_parameter_uniform_compact_support`,
restated here). -/
theorem contDiffOn_integral_of_compact_support {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {A : Set P} {C : Set E} (hA : IsOpen A) (hC : IsCompact C)
    {G : P × E → ℝ} (hG : ContDiffOn ℝ ∞ G (A ×ˢ univ))
    (hZero : ∀ a ∈ A, ∀ v ∉ C, G (a, v) = 0) :
    ContDiffOn ℝ ∞ (fun a => ∫ v, G (a, v)) A := by
  let k : P → E → ℝ := fun a v => G (a, -v)
  have hk : ContDiffOn ℝ ∞ (Function.uncurry k) (A ×ˢ univ) :=
    hG.comp (contDiffOn_fst.prodMk contDiffOn_snd.neg) (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hzero (a : P) (v : E) (ha : a ∈ A) (hv : v ∉ -C) : k a v = 0 := by
    exact hZero a ha (-v) (by simpa only [Set.mem_neg, neg_neg] using hv)
  have H := contDiffOn_convolution_right_with_param_comp (ContinuousLinearMap.mul ℝ ℝ)
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : P => (0 : E)) A)
    hA hC.neg hzero (show LocallyIntegrable (fun _ : E => (1 : ℝ)) volume from
      locallyIntegrable_const (1 : ℝ)) hk
  simpa only [convolution_def, ContinuousLinearMap.mul_apply', one_mul, zero_sub, k, neg_neg]
    using H

/-- A uniform tube around `K × {0}` on which `Φ` is defined with values in `U`. -/
theorem exists_tube {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : E)) ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z k : E, k ∈ K → dist z k < δ → ∀ ξ : E, ‖ξ‖ < δ →
      (z, ξ) ∈ O ∧ Φ z ξ ∈ U ∧ z ∈ U := by
  set G : Set (E × E) := (O ∩ (fun q : E × E => Φ q.1 q.2) ⁻¹' U) ∩ Prod.fst ⁻¹' U with hG
  have hGo : IsOpen G :=
    (hΦ.contDiffOn.continuousOn.isOpen_inter_preimage hΦ.isOpen hU).inter
      (hU.preimage continuous_fst)
  have hKG : K ×ˢ ({0} : Set E) ⊆ G := by
    rintro ⟨k, ξ⟩ ⟨hk, hξ⟩
    simp only [mem_singleton_iff] at hξ
    subst hξ
    refine ⟨⟨hKO k hk, ?_⟩, hKU hk⟩
    simp only [mem_preimage]
    rw [hΦ.map_zero k (hKO k hk)]
    exact hKU hk
  obtain ⟨δ, hδ, hsub⟩ := (hK.prod isCompact_singleton).exists_thickening_subset_open hGo hKG
  refine ⟨δ, hδ, fun z k hk hzk ξ hξ => ?_⟩
  have hmem : (z, ξ) ∈ thickening δ (K ×ˢ ({0} : Set E)) := by
    rw [mem_thickening_iff]
    refine ⟨(k, 0), ⟨hk, rfl⟩, ?_⟩
    rw [Prod.dist_eq, dist_zero_right]
    exact max_lt hzk hξ
  have h := hsub hmem
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The support of the weight is bounded uniformly on a compact set of positivity. -/
theorem exists_localWeight_support_bound' {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U C : Set E}
    (hα : ContinuousOn α U) (hpos : ∀ z ∈ U, IsStrictlyPositive (α z)) (hC : IsCompact C)
    (hCU : C ⊆ U) : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ C, ∀ ξ, localWeight α z ξ ≠ 0 → ‖ξ‖ ≤ M := by
  obtain ⟨m, hm, hmK⟩ := exists_pos_le_apply_I_smul hα hpos hC hCU
  refine ⟨1 + (Real.pi * m)⁻¹, by positivity, ?_⟩
  intro z hz ξ hξ
  have hlt : Real.pi * α z ![ξ, Complex.I • ξ] < 1 := by
    by_contra h
    exact hξ (DN3.chi_eq_zero_of_le N (not_lt.mp h))
  have hle := hmK z hz ξ
  have hpm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have h2 : Real.pi * m * ‖ξ‖ ^ 2 < 1 := by nlinarith [Real.pi_pos]
  have h3 : ‖ξ‖ ^ 2 ≤ (Real.pi * m)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hpm]
    linarith
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

/-- **Joint smoothness of `(z, w) ↦ Ψ_f(z, w)` near `K × {0}`**, uniformly in `f`: there are an
open `V ⊇ K` and `ρ > 0` such that `Ψ_f` is `C^∞` on `V × B(0, ρ)` for every `f` smooth on `U`. -/
theorem exists_smoothDomain {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O)
    {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U K : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (h11 : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : E)) ∈ O) :
    ∃ (V : Set E) (ρ : ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < ρ ∧ (∀ z ∈ V, (z, (0 : E)) ∈ O) ∧
      (∀ z ∈ V, 0 < ∫ ξ, localWeight α z ξ) ∧
      ∀ f : E → ℝ, ContDiffOn ℝ ∞ f U →
        ContDiffOn ℝ ∞ (fun p : E × ℂ => localSmoothingC Φ α f p.1 p.2) (V ×ˢ ball 0 ρ) := by
  obtain ⟨δ, hδ, htube⟩ := exists_tube hΦ hU hK hKU hKO
  set ε := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  set V := thickening ε K with hV
  have hVo : IsOpen V := isOpen_thickening
  have hKV : K ⊆ V := self_subset_thickening hε0 K
  have hCc : IsCompact (cthickening ε K) := hK.cthickening
  have hCmem : ∀ z ∈ cthickening ε K, ∃ k ∈ K, dist z k < δ := by
    intro z hz
    rw [hK.cthickening_eq_biUnion_closedBall hε0.le] at hz
    simp only [mem_iUnion, mem_closedBall] at hz
    obtain ⟨k, hk, hzk⟩ := hz
    exact ⟨k, hk, by linarith⟩
  have hCU : cthickening ε K ⊆ U := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := hCmem z hz
    exact (htube z k hk hzk 0 (by simpa using hδ)).2.2
  have hVC : V ⊆ cthickening ε K := thickening_subset_cthickening ε K
  have hVU : V ⊆ U := hVC.trans hCU
  obtain ⟨M, hM, hMsupp⟩ := exists_localWeight_support_bound' hα.continuousOn
    (fun z hz => (h11 z hz).2) hCc hCU
  set ρ := δ / (2 * (M + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hVO : ∀ z ∈ V, (z, (0 : E)) ∈ O := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := hCmem z (hVC hz)
    exact (htube z k hk hzk 0 (by simpa using hδ)).1
  have hpos : ∀ z ∈ V, 0 < ∫ ξ, localWeight α z ξ := fun z hz =>
    integral_localWeight_pos (h11 z (hVU hz)).1 (h11 z (hVU hz)).2
  have hw0 : ∀ z ∈ V, ∀ ξ, M < ‖ξ‖ → localWeight α z ξ = 0 := by
    intro z hz ξ hξ
    by_contra h
    exact absurd (hMsupp z (hVC hz) ξ h) (not_le.mpr hξ)
  -- smoothness of the weight on `V × univ`
  have hk : ContDiffOn ℝ ∞ (fun x : E × E => localWeight α x.1 x.2) (V ×ˢ univ) :=
    (contDiffOn_localWeight hα).mono (prod_mono hVU subset_rfl)
  have hD : IsOpen (V ×ˢ ball (0 : ℂ) ρ) := hVo.prod isOpen_ball
  -- the denominator
  have hden : ContDiffOn ℝ ∞ (fun p : E × ℂ => ∫ ξ, localWeight α p.1 ξ) (V ×ˢ ball 0 ρ) := by
    refine contDiffOn_integral_of_compact_support (C := closedBall 0 M) hD
      (isCompact_closedBall 0 M) (G := fun x : (E × ℂ) × E => localWeight α x.1.1 x.2) ?_ ?_
    · exact hk.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
        (fun x hx => ⟨hx.1.1, mem_univ _⟩)
    · intro a ha v hv
      exact hw0 a.1 ha.1 v (by simpa [mem_closedBall, dist_zero_right] using hv)
  refine ⟨V, ρ, hVo, hKV, hVU, hρ0, hVO, hpos, fun f hf => ?_⟩
  -- the numerator
  have hnum : ContDiffOn ℝ ∞ (fun p : E × ℂ => ∫ ξ, f (Φ p.1 (p.2 • ξ)) * localWeight α p.1 ξ)
      (V ×ˢ ball 0 ρ) := by
    refine contDiffOn_integral_of_compact_support (C := closedBall 0 M) hD
      (isCompact_closedBall 0 M)
      (G := fun x : (E × ℂ) × E => f (Φ x.1.1 (x.1.2 • x.2)) * localWeight α x.1.1 x.2) ?_ ?_
    · refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
      by_cases hx2 : ‖x.2‖ < M + 1
      · refine ⟨{y | ‖y.2‖ < M + 1}, isOpen_lt (continuous_norm.comp continuous_snd)
          continuous_const, hx2, ?_⟩
        have hmaps : ∀ y ∈ (V ×ˢ ball (0 : ℂ) ρ) ×ˢ (univ : Set E) ∩ {y | ‖y.2‖ < M + 1},
            ((y.1.1, y.1.2 • y.2) : E × E) ∈ O ∧ Φ y.1.1 (y.1.2 • y.2) ∈ U := by
          rintro y ⟨⟨⟨hy1, hy2⟩, -⟩, hy3⟩
          obtain ⟨k, hk, hzk⟩ := hCmem y.1.1 (hVC hy1)
          have hy2' : ‖y.1.2‖ < ρ := by simpa [mem_ball, dist_zero_right] using hy2
          have hs : ‖y.1.2 • y.2‖ < δ := by
            rw [norm_smul]
            calc ‖y.1.2‖ * ‖y.2‖ ≤ ρ * (M + 1) :=
                  mul_le_mul hy2'.le (show ‖y.2‖ < M + 1 from hy3).le (norm_nonneg _) hρ0.le
              _ = δ / 2 := by rw [hρ]; field_simp
              _ < δ := by linarith
          exact ⟨(htube _ k hk hzk _ hs).1, (htube _ k hk hzk _ hs).2.1⟩
        have hg : ContDiff ℝ ∞ (fun y : (E × ℂ) × E => ((y.1.1, y.1.2 • y.2) : E × E)) :=
          (contDiff_fst.comp contDiff_fst).prodMk ((contDiff_snd.comp contDiff_fst).smul
            contDiff_snd)
        have hΦc : ContDiffOn ℝ ∞ (fun y : (E × ℂ) × E => Φ y.1.1 (y.1.2 • y.2))
            ((V ×ˢ ball (0 : ℂ) ρ) ×ˢ (univ : Set E) ∩ {y | ‖y.2‖ < M + 1}) :=
          hΦ.contDiffOn.comp hg.contDiffOn fun y hy => (hmaps y hy).1
        have hfc : ContDiffOn ℝ ∞ (fun y : (E × ℂ) × E => f (Φ y.1.1 (y.1.2 • y.2)))
            ((V ×ˢ ball (0 : ℂ) ρ) ×ˢ (univ : Set E) ∩ {y | ‖y.2‖ < M + 1}) :=
          hf.comp hΦc fun y hy => (hmaps y hy).2
        have hkc : ContDiffOn ℝ ∞ (fun y : (E × ℂ) × E => localWeight α y.1.1 y.2)
            ((V ×ˢ ball (0 : ℂ) ρ) ×ˢ (univ : Set E) ∩ {y | ‖y.2‖ < M + 1}) :=
          hk.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
            (fun y hy => ⟨hy.1.1.1, mem_univ _⟩)
        exact hfc.mul hkc
      · refine ⟨{y | M < ‖y.2‖}, isOpen_lt continuous_const
          (continuous_norm.comp continuous_snd), by
            change M < ‖x.2‖; linarith [not_lt.mp hx2], ?_⟩
        refine (contDiffOn_const (c := (0 : ℝ))).congr fun y hy => ?_
        rw [hw0 y.1.1 hy.1.1.1 y.2 hy.2, mul_zero]
    · intro a ha v hv
      rw [hw0 a.1 ha.1 v (by simpa [mem_closedBall, dist_zero_right] using hv), mul_zero]
  exact hnum.div hden fun p hp => (hpos p.1 hp.1).ne'

/-! ### The `q`-part -/

/-- **The `q`-part** (FPT Step 5): for `q` smooth on `U`, `E(z, w) = Ψ_q(z, w) - q(z)` satisfies,
for `z ∈ K` and `|w| ≤ r`, `|E| ≤ C|w|²`, `|∂_w E[b]| ≤ C|w||b|` and
`|D²E(z, w)[(a, b), (a, b)]| ≤ C(|w|²|a|² + |w||a||b| + |b|²)`. -/
theorem exists_qPart {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O)
    {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U K : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (h11 : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : E)) ∈ O) {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) :
    ∃ (V : Set E) (r C : ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < r ∧ 0 ≤ C ∧
      ContDiffOn ℝ ∞ (fun x : E × ℂ => localSmoothingC Φ α q x.1 x.2 - q x.1)
        (V ×ˢ ball 0 (2 * r)) ∧
      ∀ z ∈ K, ∀ w : ℂ, ‖w‖ ≤ r →
        |localSmoothingC Φ α q z w - q z| ≤ C * ‖w‖ ^ 2 ∧
        (∀ b : ℂ, |fderiv ℝ (fun x : E × ℂ => localSmoothingC Φ α q x.1 x.2 - q x.1) (z, w)
          (0, b)| ≤ C * ‖w‖ * ‖b‖) ∧
        ∀ (a : E) (b : ℂ), |fderiv ℝ (fderiv ℝ (fun x : E × ℂ =>
            localSmoothingC Φ α q x.1 x.2 - q x.1)) (z, w) (a, b) (a, b)| ≤
          C * (‖w‖ ^ 2 * ‖a‖ ^ 2 + ‖w‖ * ‖a‖ * ‖b‖ + ‖b‖ ^ 2) := by
  obtain ⟨V, ρ, hVo, hKV, hVU, hρ, hVO, hpos, hsmooth⟩ :=
    exists_smoothDomain hΦ hU hα h11 hK hKU hKO
  set F : E × ℂ → ℝ := fun x => localSmoothingC Φ α q x.1 x.2 - q x.1 with hF
  have hFs : ContDiffOn ℝ ∞ F (V ×ˢ ball 0 ρ) :=
    (hsmooth q hq).sub ((hq.mono hVU).comp contDiffOn_fst fun x hx => hx.1)
  have hF0 : ∀ z ∈ V, F (z, 0) = 0 := by
    intro z hz
    simp only [hF]
    rw [localSmoothingC_zero α q (hΦ.map_zero z (hVO z hz)) (hpos z hz), sub_self]
  have hFe : ∀ z ∈ V, ∀ y ∈ ball (0 : ℂ) ρ, F (z, -y) = F (z, y) := by
    intro z _ y _
    simp only [hF, localSmoothingC_neg]
  obtain ⟨C, hC, hbd⟩ := exists_even_taylor_bounds (P := E) (Q := ℂ) hVo
    (hFs.of_le (by norm_cast)) hF0 hFe hK hKV (half_pos hρ).le (half_lt_self hρ)
  refine ⟨V, ρ / 2, C, hVo, hKV, hVU, half_pos hρ, hC, ?_, fun z hz w hw => ?_⟩
  · rw [mul_div_cancel₀ ρ two_ne_zero]
    exact hFs
  · have hw' : w ∈ closedBall (0 : ℂ) (ρ / 2) := by simpa [mem_closedBall, dist_zero_right] using hw
    exact hbd z hz w hw'

/-- **the interface `QPartEstimate`.** -/
theorem qPartEstimate : DN9.QPartEstimate N := by
  intro Φ O α U K q hdata hq
  obtain ⟨hΦ, hU, hα, h11, hK, hKU, hKO⟩ := hdata
  obtain ⟨V, r, C, hVo, hKV, hVU, hr, hC, hs, hbd⟩ := exists_qPart hΦ hU hα h11 hK hKU hKO hq
  set F : E × ℂ → ℝ := fun x => localSmoothingC Φ α q x.1 x.2 - q x.1 with hF
  have hFeq : ∀ x : E × ℂ, localSmoothingC Φ α q x.1 x.2 = F x + q x.1 := fun x => by
    simp [hF]
  have hsC : ContDiffOn ℝ ∞ (fun x : E × ℂ => localSmoothingC Φ α q x.1 x.2)
      (V ×ˢ ball 0 (2 * r)) :=
    hs.add ((hq.mono hVU).comp contDiffOn_fst fun x hx => hx.1) |>.congr fun x _ => hFeq x
  have hD : IsOpen (V ×ˢ ball (0 : ℂ) (2 * r)) := hVo.prod isOpen_ball
  refine ⟨V, r, C, hVo, hKV, hr, hC, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · -- joint smoothness in `(z, t)`
    have hg : ContDiff ℝ ∞ (fun x : E × ℝ => ((x.1, (x.2 : ℂ)) : E × ℂ)) :=
      contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
    refine ((hsC.comp hg.contDiffOn fun x hx => ⟨hx.1, ?_⟩).of_le (by norm_cast)).congr
      fun x _ => (localSmoothingC_ofReal Φ α q x.1 x.2).symm
    have h1 : 0 < x.2 := hx.2.1
    have h2 : x.2 < r := hx.2.2
    simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos h1]
    linarith
  · -- the slope
    intro t ht0 htr
    have hzt : ((z, (t : ℂ)) : E × ℂ) ∈ V ×ˢ ball 0 (2 * r) := by
      refine ⟨hKV hz, ?_⟩
      simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      linarith
    have hdF : HasFDerivAt F (fderiv ℝ F (z, (t : ℂ))) (z, (t : ℂ)) :=
      ((hs.differentiableOn (by norm_num)) _ hzt).differentiableAt
        (hD.mem_nhds hzt) |>.hasFDerivAt
    have hγ : HasDerivAt (fun s : ℝ => ((z, (s : ℂ)) : E × ℂ)) ((0 : E), (1 : ℂ)) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).ofReal_comp)
    have hder : HasDerivAt (localSmoothing Φ α q z) (fderiv ℝ F (z, (t : ℂ)) (0, 1)) t := by
      have h := (hdF.comp_hasDerivAt t hγ).add_const (q z)
      refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp only [Function.comp, hF]
      rw [← localSmoothingC_ofReal]
      ring
    rw [hder.deriv]
    have hb := (hbd z hz (t : ℂ) (by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact htr.le)).2.1 1
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, norm_one, mul_one] at hb
    rw [abs_mul, abs_of_pos ht0]
    calc t * |fderiv ℝ F (z, (t : ℂ)) (0, 1)| ≤ t * (C * t) := by gcongr
      _ = C * t ^ 2 := by ring
  · -- the Levi form
    intro w hw0 hwr v η
    have hwr' : ‖w‖ ≤ r := hwr.le
    have hfun : (fun x : E × ℂ => localSmoothing Φ α q x.1 ‖x.2‖ - q x.1) = F := by
      funext x
      simp only [hF, localSmoothingC_eq_norm]
    rw [hfun]
    have h2 := (hbd z hz w hwr').2.2
    have hA := h2 v η
    have hB := h2 (Complex.I • v) (Complex.I • η)
    have hIv : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    have hIη : ‖Complex.I • η‖ = ‖η‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    rw [hIv, hIη] at hB
    have hsm : Complex.I • ((v, η) : E × ℂ) = (Complex.I • v, Complex.I • η) := rfl
    simp only [leviForm, realHessian_eq_fderiv, hsm]
    have hT : 0 ≤ ‖w‖ ^ 2 * ‖v‖ ^ 2 + ‖w‖ * ‖v‖ * ‖η‖ + ‖η‖ ^ 2 := by positivity
    have := abs_le.mp hA
    have := abs_le.mp hB
    nlinarith [mul_nonneg hC hT]

/-- **Radial bounds for the `q`-part** (for the clauses `H ≥ u` and convexity): for `z ∈ K`,
`Q(t) = Ψ_q(z, t)` satisfies `|Q(t) - q(z)| ≤ C t²` (`|t| ≤ r`), `Q` is differentiable with
`|t Q'(t)| ≤ C t²`, and `s ↦ Q(eˢ)` has derivatives `q₁, q₂` with `|q₁(s)|, |q₂(s)| ≤ C e^{2s}`
(`eˢ ≤ r`). -/
theorem exists_qRadial {Φ : E → E → E} {O : Set (E × E)} (hΦ : IsLocalFibreMap Φ O)
    {α : E → E [⋀^Fin 2]→L[ℝ] ℝ} {U K : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (h11 : ∀ z ∈ U, IsOneOne (α z) ∧ IsStrictlyPositive (α z)) (hK : IsCompact K)
    (hKU : K ⊆ U) (hKO : ∀ z ∈ K, (z, (0 : E)) ∈ O) {q : E → ℝ} (hq : ContDiffOn ℝ ∞ q U) :
    ∃ (V : Set E) (r C : ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < r ∧ 0 ≤ C ∧
      ContDiffOn ℝ ∞ (fun x : E × ℂ => localSmoothingC Φ α q x.1 x.2) (V ×ˢ ball 0 (2 * r)) ∧
      ∀ z ∈ K,
        (∀ t : ℝ, |t| ≤ r → |localSmoothing Φ α q z t - q z| ≤ C * t ^ 2) ∧
        (∀ t : ℝ, |t| < 2 * r → DifferentiableAt ℝ (localSmoothing Φ α q z) t) ∧
        (∀ t : ℝ, |t| ≤ r → |t * deriv (localSmoothing Φ α q z) t| ≤ C * t ^ 2) ∧
        ∃ q₁ q₂ : ℝ → ℝ, ∀ s : ℝ, Real.exp s ≤ r →
          HasDerivAt (fun s => localSmoothing Φ α q z (Real.exp s)) (q₁ s) s ∧
          HasDerivAt q₁ (q₂ s) s ∧ |q₁ s| ≤ C * Real.exp (2 * s) ∧
          |q₂ s| ≤ 2 * C * Real.exp (2 * s) := by
  obtain ⟨V, r, C, hVo, hKV, hVU, hr, hC, hs, hbd⟩ := exists_qPart hΦ hU hα h11 hK hKU hKO hq
  set F : E × ℂ → ℝ := fun x => localSmoothingC Φ α q x.1 x.2 - q x.1 with hF
  have hFeq : ∀ x : E × ℂ, localSmoothingC Φ α q x.1 x.2 = F x + q x.1 := fun x => by
    simp [hF]
  have hsC : ContDiffOn ℝ ∞ (fun x : E × ℂ => localSmoothingC Φ α q x.1 x.2)
      (V ×ˢ ball 0 (2 * r)) :=
    hs.add ((hq.mono hVU).comp contDiffOn_fst fun x hx => hx.1) |>.congr fun x _ => hFeq x
  have hD : IsOpen (V ×ˢ ball (0 : ℂ) (2 * r)) := hVo.prod isOpen_ball
  have hdF : ∀ x ∈ V ×ˢ ball (0 : ℂ) (2 * r), HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hs.differentiableOn (by norm_num)) _ hx).differentiableAt (hD.mem_nhds hx) |>.hasFDerivAt
  have hs1 : ContDiffOn ℝ ∞ (fderiv ℝ F) (V ×ˢ ball (0 : ℂ) (2 * r)) :=
    hs.fderiv_of_isOpen hD (by norm_cast)
  have hddF : ∀ x ∈ V ×ˢ ball (0 : ℂ) (2 * r),
      HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x := fun x hx =>
    ((hs1.differentiableOn (by norm_num)) _ hx).differentiableAt (hD.mem_nhds hx) |>.hasFDerivAt
  have hQ : ∀ z t, localSmoothing Φ α q z t = F (z, (t : ℂ)) + q z := fun z t => by
    rw [← localSmoothingC_ofReal]; exact hFeq (z, (t : ℂ))
  refine ⟨V, r, C, hVo, hKV, hVU, hr, hC, hsC, fun z hz => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro t ht
    have h := (hbd z hz (t : ℂ) (by simpa [Complex.norm_real] using ht)).1
    rw [localSmoothingC_ofReal] at h
    simpa [Complex.norm_real, sq_abs] using h
  · intro t ht
    have hzt : ((z, (t : ℂ)) : E × ℂ) ∈ V ×ˢ ball 0 (2 * r) :=
      ⟨hKV hz, by simpa [mem_ball, dist_zero_right, Complex.norm_real] using ht⟩
    have hγ : HasDerivAt (fun s : ℝ => ((z, (s : ℂ)) : E × ℂ)) ((0 : E), (1 : ℂ)) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).ofReal_comp)
    have h := ((hdF _ hzt).comp_hasDerivAt t hγ).add_const (q z)
    exact (h.congr_of_eventuallyEq (Eventually.of_forall fun s => hQ z s)).differentiableAt
  · intro t ht
    have hzt : ((z, (t : ℂ)) : E × ℂ) ∈ V ×ˢ ball 0 (2 * r) :=
      ⟨hKV hz, by
        simp only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; linarith⟩
    have hγ : HasDerivAt (fun s : ℝ => ((z, (s : ℂ)) : E × ℂ)) ((0 : E), (1 : ℂ)) t :=
      (hasDerivAt_const t z).prodMk ((hasDerivAt_id t).ofReal_comp)
    have hder : HasDerivAt (localSmoothing Φ α q z) (fderiv ℝ F (z, (t : ℂ)) (0, 1)) t := by
      have h := ((hdF _ hzt).comp_hasDerivAt t hγ).add_const (q z)
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => hQ z s)
    rw [hder.deriv]
    have hb := (hbd z hz (t : ℂ) (by simpa [Complex.norm_real] using ht)).2.1 1
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one] at hb
    rw [abs_mul]
    calc |t| * |fderiv ℝ F (z, (t : ℂ)) (0, 1)| ≤ |t| * (C * |t|) := by gcongr
      _ = C * t ^ 2 := by rw [← sq_abs t]; ring
  · -- derivatives in `s = log t`
    set γ : ℝ → E × ℂ := fun s => (z, ((Real.exp s : ℝ) : ℂ)) with hγdef
    set γ' : ℝ → E × ℂ := fun s => ((0 : E), ((Real.exp s : ℝ) : ℂ)) with hγ'def
    have hγ : ∀ s, HasDerivAt γ (γ' s) s := fun s =>
      (hasDerivAt_const s z).prodMk ((Real.hasDerivAt_exp s).ofReal_comp)
    have hγ' : ∀ s, HasDerivAt γ' (γ' s) s := fun s =>
      (hasDerivAt_const s (0 : E)).prodMk ((Real.hasDerivAt_exp s).ofReal_comp)
    have hmem : ∀ s, Real.exp s ≤ r → γ s ∈ V ×ˢ ball (0 : ℂ) (2 * r) := fun s hs =>
      ⟨hKV hz, by
        simp only [hγdef, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos s)]; linarith⟩
    refine ⟨fun s => fderiv ℝ F (γ s) (γ' s),
      fun s => fderiv ℝ (fderiv ℝ F) (γ s) (γ' s) (γ' s) + fderiv ℝ F (γ s) (γ' s),
      fun s hs => ⟨?_, ?_, ?_, ?_⟩⟩
    · have h := ((hdF _ (hmem s hs)).comp_hasDerivAt s (hγ s)).add_const (q z)
      exact h.congr_of_eventuallyEq (Eventually.of_forall fun s' => hQ z _)
    · exact ((hddF _ (hmem s hs)).comp_hasDerivAt s (hγ s)).clm_apply (hγ' s)
    · have hw : ‖((Real.exp s : ℝ) : ℂ)‖ ≤ r := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]; exact hs
      have hb := (hbd z hz _ hw).2.1 ((Real.exp s : ℝ) : ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)] at hb
      calc |fderiv ℝ F (γ s) (γ' s)| ≤ C * Real.exp s * Real.exp s := hb
        _ = C * Real.exp (2 * s) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    · have hw : ‖((Real.exp s : ℝ) : ℂ)‖ ≤ r := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]; exact hs
      have hb1 := (hbd z hz _ hw).2.1 ((Real.exp s : ℝ) : ℂ)
      have hb2 := (hbd z hz _ hw).2.2 0 ((Real.exp s : ℝ) : ℂ)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s), norm_zero,
        mul_zero, zero_mul, add_zero] at hb1 hb2
      have hb2' : |fderiv ℝ (fderiv ℝ F) (γ s) (γ' s) (γ' s)| ≤ C * Real.exp s ^ 2 := by
        convert hb2 using 2; ring
      have he : Real.exp s * Real.exp s = Real.exp (2 * s) := by
        rw [← Real.exp_add]; ring_nf
      calc |fderiv ℝ (fderiv ℝ F) (γ s) (γ' s) (γ' s) + fderiv ℝ F (γ s) (γ' s)|
          ≤ |fderiv ℝ (fderiv ℝ F) (γ s) (γ' s) (γ' s)| + |fderiv ℝ F (γ s) (γ' s)| :=
            abs_add_le _ _
        _ ≤ C * Real.exp s ^ 2 + C * Real.exp s * Real.exp s := add_le_add hb2' hb1
        _ = 2 * C * Real.exp (2 * s) := by rw [sq, mul_assoc, he]; ring

end SGPT.NPP.DN10
