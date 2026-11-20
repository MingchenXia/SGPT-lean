import SGPT.Envelopes.TosC11dLineCalc
import SGPT.Envelopes.TosC11dLineMax
import SGPT.Envelopes.TosC11dAlgebra

/-!
# The two inequalities along each real direction at the maximum point

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:frame`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 3, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).

At the centre `0` of normal coordinates (`NormalAt ψ`), let `b` be an orthonormal eigenbasis of the
real Hessian `H₀ = D²a(0)` with top eigenvalue `λ = μ_{i₁} > 0`, and suppose that
`(∇²a(x)(Y, Y)/g(x)(Y, Y)) e^{w(x)} ≤ λ e^{w(0)}` near `0`, where
`w = η(s) - A a`, `η(y) = -(τ/2) log(1 + S - y)`.  With the perturbation `B₀ = projForm b_{i₁}`
(which lowers the other eigenvalues by one), `line_max` along the line `t ↦ t v` gives
(`NormalAt.frame_ineq`):

* the critical point equation
  `(D³a(0)(v, b, b) - K₁(v)(b, b))/λ + η' s'_v - A Da(0) v = 0`, and
* the second-order inequality
  `(D⁴a(0)(v, v, b, b) - K₂(v)(b, b) + 2 Σ_{α ≠ i₁} (D³a(0)(v, b, b_α) - K₁(v)(b, b_α))²/(λ - λ_α)
   - λ D²g(0)(v, v)(b, b))/λ - (D³a(0)(v, b, b) - K₁(v)(b, b))²/λ² + η'' s'_v² + η' s''_v
   - A D²a(0)(v, v) ≤ 0`,

with the Koszul error terms `K₁(v) = kosForm(D²g(0) v, ∇a(0))`,
`K₂(v) = kosForm(D³g(0)(v, v), ∇a(0)) + 2 kosForm(D²g(0) v, (D²a(0) v)^♯)`, `λ_α = μ_α - 1`,
`s'_v = 2 D²a(0)(v, ∇a(0))` and `s''_v = 2 D³a(0)(v, v, ∇a(0)) + 2‖D²a(0) v‖² - D²g(0)(v, v)(∇a(0), ∇a(0))`.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ} {ψ a : ComplexModel n → ℝ}

/-- Derivatives of the gradient weight `η(y) = -(τ/2) log(1 + S - y)` for `y < 1 + S`. -/
theorem eta_deriv {τ S y : ℝ} (hy : y < 1 + S) :
    HasDerivAt (fun y => -(τ / 2) * Real.log (1 + S - y)) (τ / 2 / (1 + S - y)) y ∧
      HasDerivAt (fun y => τ / 2 / (1 + S - y)) (τ / 2 / (1 + S - y) ^ 2) y := by
  have hpos : 0 < 1 + S - y := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 + S - x) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub (1 + S)
  refine ⟨?_, ?_⟩
  · have h := (hlin.log hpos.ne').const_mul (-(τ / 2))
    refine h.congr_deriv ?_
    field_simp
  · have h := (hlin.inv hpos.ne').const_mul (τ / 2)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · simp [div_eq_mul_inv]
    · field_simp

/-- A `Koszul` form of a symmetric derivative is symmetric. -/
theorem kosForm_symm {P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hP : ∀ U Y Z, P U Y Z = P U Z Y) (G Y Z : ComplexModel n) :
    kosForm P G Y Z = kosForm P G Z Y := by
  rw [kosForm_apply, kosForm_apply, hP G Y Z]; ring

/-- The second derivative of the metric is symmetric in its last two arguments. -/
theorem fderiv_fderiv_metricOf_symm (hψ : ContDiff ℝ ∞ ψ) (v U Y Z : ComplexModel n) :
    fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v U Y Z = fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v U Z Y := by
  rw [fderiv_fderiv_metricOf hψ, leviBil_apply, leviBil_apply, d4_symm₃₄ hψ,
    d4_symm₃₄ hψ 0 v U (Complex.I • Y)]

/-- The eigenbasis of `D²a(0) - projForm b_{i₁}`. -/
theorem bilinOpL_sub_projForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (μ : ι → ℝ)
    (hb : ∀ i, bilinOpL H (b i) = μ i • b i) (i₁ i : ι) :
    bilinOpL (H - projForm (b i₁)) (b i) =
      (if i = i₁ then μ i₁ else μ i - 1) • b i := by
  rw [map_sub, sub_apply, hb]
  have hP : bilinOpL (projForm (b i₁)) (b i) = (if i = i₁ then 0 else 1 : ℝ) • b i := by
    refine ext_inner_right ℝ fun y => ?_
    rw [inner_bilinOpL, projForm_apply, inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    by_cases h : i = i₁
    · subst h
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, if_pos rfl]
      simp [real_inner_comm]
    · rw [if_neg h, b.orthonormal.2 h]
      simp [real_inner_comm]
  rw [hP]
  by_cases h : i = i₁
  · subst h; simp
  · simp only [if_neg h, one_smul]; rw [sub_smul, one_smul]

/-- **The two inequalities along a real direction `v`** at the maximum point. -/
theorem NormalAt.frame_ineq (hN : NormalAt ψ) (ha : ContDiff ℝ ∞ a) {w : ComplexModel n → ℝ}
    {τ S A : ℝ} (hs0 : sFun ψ a 0 ≤ S)
    (hw : ∀ᶠ x in 𝓝 (0 : ComplexModel n),
      w x = -(τ / 2) * Real.log (1 + S - sFun ψ a x) - A * a x)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ (ComplexModel n))
    (μ : ι → ℝ) (i₁ : ι) (hb : ∀ i, bilinOpL (fderiv ℝ (fderiv ℝ a) 0) (b i) = μ i • b i)
    (htop : ∀ i, μ i ≤ μ i₁) (hlam : 0 < μ i₁)
    (hmax : ∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ Y, Y ≠ 0 →
      quot ψ a x Y * Real.exp (w x) ≤ μ i₁ * Real.exp (w 0))
    (v : ComplexModel n) :
    (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v (b i₁) (b i₁) -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) (b i₁) (b i₁)) / μ i₁ +
      (τ / 2 / (1 + S - sFun ψ a 0) * (2 * fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0)) -
        A * fderiv ℝ a 0 v) = 0 ∧
    (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 v v (b i₁) (b i₁) -
        (kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁) +
          2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v)
            (b i₁) (b i₁)) +
        2 * ∑ i ∈ Finset.univ.erase i₁,
          (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v (b i₁) (b i) -
            kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) (b i₁) (b i)) ^ 2 /
            (μ i₁ - (μ i - 1)) -
        μ i₁ * fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (b i₁) (b i₁)) / μ i₁ -
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v (b i₁) (b i₁) -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) (b i₁) (b i₁)) ^ 2 /
        μ i₁ ^ 2 +
      (τ / 2 / (1 + S - sFun ψ a 0) ^ 2 * (2 * fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0)) ^ 2 +
        τ / 2 / (1 + S - sFun ψ a 0) *
          (2 * fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v (grad ψ a 0) +
            2 * ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2 -
            fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0)) -
        A * fderiv ℝ (fderiv ℝ a) 0 v v) ≤ 0 := by
  have hψ := hN.smooth
  have hg : ContDiff ℝ ∞ (metricOf ψ) := contDiff_metricOf hψ
  have hg2 : ContDiffAt ℝ 2 (metricOf ψ) 0 :=
    hg.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ι → ℝ, ∀ i, lam i = if i = i₁ then μ i₁ else μ i - 1 :=
    ⟨_, fun _ => rfl⟩
  -- the curves along the line
  obtain ⟨hcov, hcov'⟩ := hN.cov_line ha v
  obtain ⟨hgl, hgl'⟩ := line_deriv_two hg2 v
  obtain ⟨hsl, hsl0, hsl'⟩ := hN.sFun_line ha v
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => cov ψ a (t • v) - projForm (b i₁))
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) (t • v) v -
        (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) (t • v) v) (grad ψ a (t • v)) +
          kosB (fderiv ℝ (metricOf ψ) (t • v)) (fderiv ℝ (grad ψ a) (t • v) v))) t :=
    hcov.mono fun t ht => ht.sub_const _
  -- the weight along the line
  have hsc : ContinuousAt (fun t : ℝ => sFun ψ a (t • v)) 0 := hsl.self_of_nhds.continuousAt
  have hslt : ∀ᶠ t in 𝓝 (0 : ℝ), sFun ψ a (t • v) < 1 + S := by
    have h0 : sFun ψ a ((0 : ℝ) • v) < 1 + S := by rw [zero_smul]; linarith
    exact hsc.eventually (gt_mem_nhds h0)
  have hwl := eventually_line hw v
  have hW : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => w (t • v))
      (τ / 2 / (1 + S - sFun ψ a (t • v)) *
          (fderiv ℝ (fderiv ℝ a) (t • v) v (grad ψ a (t • v)) +
            fderiv ℝ a (t • v) (fderiv ℝ (grad ψ a) (t • v) v)) -
        A * fderiv ℝ a (t • v) v) t := by
    filter_upwards [hsl, hslt, hwl.eventually_nhds] with t ht hlt hwt
    have he := (eta_deriv (τ := τ) hlt).1
    have h1 := he.comp t ht
    have h2 : HasDerivAt (fun t => a (t • v)) (fderiv ℝ a (t • v) v) t :=
      hasDerivAt_line ((ha.differentiable (by simp)) _)
    exact (h1.sub (h2.const_mul A)).congr_of_eventuallyEq (hwt.mono fun s hs => hs)
  have hlt0 : sFun ψ a ((0 : ℝ) • v) < 1 + S := by rw [zero_smul]; linarith
  have hs0d : HasDerivAt (fun t : ℝ => sFun ψ a (t • v))
      (2 * fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0)) 0 := by
    have := hsl.self_of_nhds
    rwa [hsl0] at this
  have h1 := ((eta_deriv (τ := τ) hlt0).2).comp (0 : ℝ) hs0d
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ a (t • v) v)
      (fderiv ℝ (fderiv ℝ a) 0 v v) 0 := by
    have := (hasDerivAt_line (t := 0) (v := v)
      ((differentiable_fderiv_iter ha).1 _)).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using this
  have hW' := (h1.mul hsl').sub (h3.const_mul A)
  -- symmetries at `0`
  have hcov0 : cov ψ a ((0 : ℝ) • v) = fderiv ℝ (fderiv ℝ a) 0 := by
    rw [zero_smul, hN.cov_zero]
  have hsym0 : ∀ x y, (cov ψ a ((0 : ℝ) • v) - projForm (b i₁)) x y =
      (cov ψ a ((0 : ℝ) • v) - projForm (b i₁)) y x := by
    intro x y
    rw [hcov0, sub_apply, sub_apply, sub_apply, sub_apply, d2_symm ha, projForm_symm]
  have hm'0 : fderiv ℝ (fderiv ℝ (fderiv ℝ a)) ((0 : ℝ) • v) v -
      (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) ((0 : ℝ) • v) v) (grad ψ a ((0 : ℝ) • v)) +
        kosB (fderiv ℝ (metricOf ψ) ((0 : ℝ) • v)) (fderiv ℝ (grad ψ a) ((0 : ℝ) • v) v)) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) := by
    rw [zero_smul, hN.fderiv_zero, map_zero, zero_apply, add_zero, kosB_apply]
  have hsym1 : ∀ x y, (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) ((0 : ℝ) • v) v -
      (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) ((0 : ℝ) • v) v) (grad ψ a ((0 : ℝ) • v)) +
        kosB (fderiv ℝ (metricOf ψ) ((0 : ℝ) • v)) (fderiv ℝ (grad ψ a) ((0 : ℝ) • v) v))) x y =
      (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) ((0 : ℝ) • v) v -
      (kosB (fderiv ℝ (fderiv ℝ (metricOf ψ)) ((0 : ℝ) • v) v) (grad ψ a ((0 : ℝ) • v)) +
        kosB (fderiv ℝ (metricOf ψ) ((0 : ℝ) • v)) (fderiv ℝ (grad ψ a) ((0 : ℝ) • v) v))) y x := by
    intro x y
    rw [hm'0, sub_apply, sub_apply, sub_apply, sub_apply, d3_symm₂₃ ha,
      kosForm_symm (fderiv_fderiv_metricOf_symm hψ v)]
  -- the eigenbasis of the perturbed Hessian
  have hb' : ∀ i, bilinOpL (cov ψ a ((0 : ℝ) • v) - projForm (b i₁)) (b i) = lam i • b i :=
    fun i => by rw [hcov0, hlamdef]; exact bilinOpL_sub_projForm b μ hb i₁ i
  have hlam1 : lam i₁ = μ i₁ := by simp [hlamdef]
  have hgap : ∀ i, i ≠ i₁ → lam i < lam i₁ := fun i hi => by
    rw [hlam1, hlamdef, if_neg hi]; linarith [htop i]
  -- the maximum hypothesis along the line
  have hb1 : ‖b i₁‖ = 1 := b.orthonormal.1 i₁
  have hmaxl : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ Y, Y ≠ 0 →
      (cov ψ a (t • v) - projForm (b i₁)) Y Y / metricOf ψ (t • v) Y Y * Real.exp (w (t • v)) ≤
        lam i₁ * Real.exp (w ((0 : ℝ) • v)) := by
    filter_upwards [eventually_line hmax v, eventually_line hN.pos v] with t ht hpt
    intro Y hY
    have h1 := ht Y hY
    rw [quot_eq hψ] at h1
    have hgp := hpt Y hY
    have hPY := projForm_nonneg hb1 Y
    have h2 : (cov ψ a (t • v) - projForm (b i₁)) Y Y / metricOf ψ (t • v) Y Y ≤
        cov ψ a (t • v) Y Y / metricOf ψ (t • v) Y Y := by
      rw [sub_apply, sub_apply]
      exact div_le_div_of_nonneg_right (by linarith) hgp.le
    rw [hlam1, zero_smul]
    exact (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le).trans h1
  have hg0 : ∀ x y, metricOf ψ ((0 : ℝ) • v) x y = ⟪x, y⟫ := fun x y => by
    rw [zero_smul]; exact hN.metric_zero x y
  have hg'0 : fderiv ℝ (metricOf ψ) ((0 : ℝ) • v) v = 0 := by
    rw [zero_smul, hN.fderiv_zero, zero_apply]
  obtain ⟨hC, hQ⟩ := line_max (m := fun t => cov ψ a (t • v) - projForm (b i₁)) hm hcov' hgl hgl'
    hg0 hg'0 hW hW' hsym0 hsym1 b lam hb' i₁ hgap (by rw [hlam1]; exact hlam) hmaxl
  beta_reduce at hC hQ
  simp only [hm'0, hlam1] at hC hQ
  simp only [hsl0] at hC hQ
  have hsum : ∑ i ∈ Finset.univ.erase i₁,
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0)) (b i₁) (b i)) ^ 2 /
        (μ i₁ - lam i) =
      ∑ i ∈ Finset.univ.erase i₁,
      ((fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0)) (b i₁) (b i)) ^ 2 /
        (μ i₁ - (μ i - 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hlamdef, if_neg (Finset.ne_of_mem_erase hi)]
  simp only [hsum] at hQ
  simp only [zero_smul, sub_apply, add_apply, kosB_apply, smul_apply, Function.comp_apply] at hC hQ
  refine ⟨by linarith, (le_of_eq ?_).trans hQ⟩
  ring
