import SGPT.Envelopes.TosC11dLinear
import SGPT.Envelopes.TosC11bBarrier

/-!
# The maximum principle along a line for the perturbed largest eigenvalue

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:line-max`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 2–3 (the local maximum of
`log λ₁(Φ) + η(s) - Aa` at `x₀`, differentiated along real lines), for SGPT `thm:Tos_C11`
(Tosatti, Chu–Zhou).

`line_max`: let `m(t)` (the perturbed covariant Hessian along a line), `g(t)` (the metric along the
line, `g(0) = ⟪·, ·⟫`, `g'(0) = 0`) and `w(t)` (the weight `η(s) - Aa` along the line) be twice
differentiable at `0`, let `(bᵢ)` be an orthonormal eigenbasis of `m(0)` with a simple top eigenvalue
`λ > 0` at `i₁`, and suppose `(m(t)(Y, Y)/g(t)(Y, Y)) e^{w(t)} ≤ λ e^{w(0)}` near `0` for all `Y ≠ 0`.
Then, with `b = b_{i₁}`,

* `m'(0)(b, b)/λ + w'(0) = 0` (the critical point equation), and
* `(m''(0)(b, b) + 2 Σ_{i ≠ i₁} m'(0)(b, bᵢ)²/(λ - λᵢ) - λ g''(0)(b, b))/λ - m'(0)(b, b)²/λ² + w''(0) ≤ 0`.

The proof applies the one-dimensional maximum principle to `log r + w` for the Rayleigh barrier `r`
of `TosC11b.rayleigh_quotient_metric`.
-/

set_option autoImplicit false
-- nested spaces of continuous linear maps need deeper pending instance synthesis, as in Mathlib's
-- own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bilinOpL_eq_id {B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hB : ∀ x y, B x y = ⟪x, y⟫) : bilinOpL B = 1 := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
  rw [inner_bilinOpL, hB, one_apply_eq_self]

/-- **The maximum principle along a line** for the Rayleigh barrier of the perturbed Hessian. -/
theorem line_max {m m' : ℝ → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {m₂ : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {gg gg' : ℝ → ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {gg₂ : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ} {w w' : ℝ → ℝ} {w₂ : ℝ}
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt m (m' t) t) (hm' : HasDerivAt m' m₂ 0)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt gg (gg' t) t) (hg' : HasDerivAt gg' gg₂ 0)
    (hg0 : ∀ x y, gg 0 x y = ⟪x, y⟫) (hg'0 : gg' 0 = 0)
    (hw : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt w (w' t) t) (hw' : HasDerivAt w' w₂ 0)
    (hsym0 : ∀ x y, m 0 x y = m 0 y x) (hsym1 : ∀ x y, m' 0 x y = m' 0 y x)
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (lam : ι → ℝ)
    (hb : ∀ i, bilinOpL (m 0) (b i) = lam i • b i) (i₁ : ι)
    (hgap : ∀ i, i ≠ i₁ → lam i < lam i₁) (hlam : 0 < lam i₁)
    (hmax : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ Y, Y ≠ 0 →
      m t Y Y / gg t Y Y * Real.exp (w t) ≤ lam i₁ * Real.exp (w 0)) :
    m' 0 (b i₁) (b i₁) / lam i₁ + w' 0 = 0 ∧
      (m₂ (b i₁) (b i₁) + 2 * ∑ i ∈ Finset.univ.erase i₁,
          (m' 0 (b i₁) (b i)) ^ 2 / (lam i₁ - lam i) - lam i₁ * gg₂ (b i₁) (b i₁)) / lam i₁ -
        (m' 0 (b i₁) (b i₁)) ^ 2 / lam i₁ ^ 2 + w₂ ≤ 0 := by
  -- the operator curves
  have hM : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => bilinOpL (m t)) (bilinOpL (m' t)) t :=
    hm.mono fun t ht => bilinOpL.hasFDerivAt.comp_hasDerivAt t ht
  have hM' : HasDerivAt (fun t => bilinOpL (m' t)) (bilinOpL m₂) 0 :=
    bilinOpL.hasFDerivAt.comp_hasDerivAt 0 hm'
  have hG : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => bilinOpL (gg t)) (bilinOpL (gg' t)) t :=
    hg.mono fun t ht => bilinOpL.hasFDerivAt.comp_hasDerivAt t ht
  have hG' : HasDerivAt (fun t => bilinOpL (gg' t)) (bilinOpL gg₂) 0 :=
    bilinOpL.hasFDerivAt.comp_hasDerivAt 0 hg'
  have hG0 : bilinOpL (gg 0) = 1 := bilinOpL_eq_id hg0
  have hG'0 : bilinOpL (gg' 0) = 0 := by rw [hg'0, map_zero]
  have hs0 : ∀ x z, ⟪bilinOpL (m 0) x, z⟫ = ⟪x, bilinOpL (m 0) z⟫ := fun x z => by
    rw [inner_bilinOpL, real_inner_comm, inner_bilinOpL, hsym0]
  have hs1 : ∀ x z, ⟪bilinOpL (m' 0) x, z⟫ = ⟪x, bilinOpL (m' 0) z⟫ := fun x z => by
    rw [inner_bilinOpL, real_inner_comm, inner_bilinOpL, hsym1]
  obtain ⟨hr0, r', hr', hr'0, hr''⟩ := TosC11b.rayleigh_quotient_metric hM hM' hG hG' hG0 hG'0
    hs0 hs1 b lam hb i₁ hgap
  set wv : ComplexModel n := ∑ i ∈ Finset.univ.erase i₁,
    (⟪bilinOpL (m' 0) (b i₁), b i⟫ / (lam i₁ - lam i)) • b i with hwv
  set r : ℝ → ℝ := fun t => ⟪bilinOpL (m t) (b i₁ + t • wv), b i₁ + t • wv⟫ /
    ⟪bilinOpL (gg t) (b i₁ + t • wv), b i₁ + t • wv⟫ with hrdef
  have hr_eq : ∀ t, r t = m t (b i₁ + t • wv) (b i₁ + t • wv) /
      gg t (b i₁ + t • wv) (b i₁ + t • wv) := fun t => by
    simp only [hrdef, inner_bilinOpL]
  -- the logarithm
  obtain ⟨hlog, hlog'⟩ := TosC11b.hasDerivAt_log_comp_second hr' hr'' (by rw [hr0]; exact hlam)
  -- the local maximum of `log r + w`
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), b i₁ + t • wv ≠ 0 := by
    have hc : Continuous fun t : ℝ => b i₁ + t • wv := continuous_const.add
      (continuous_id.smul continuous_const)
    have h0 : b i₁ + (0 : ℝ) • wv ≠ 0 := by
      rw [zero_smul, add_zero]; exact b.orthonormal.ne_zero i₁
    exact hc.continuousAt.eventually (isOpen_ne.mem_nhds h0)
  have hrpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < r t :=
    hr'.self_of_nhds.continuousAt.eventually (lt_mem_nhds (by rw [hr0]; exact hlam))
  have hloc : IsLocalMax (fun t => Real.log (r t) + w t) 0 := by
    filter_upwards [hne, hrpos, hmax] with t hyt hrt hmt
    have h1 := hmt _ hyt
    rw [← hr_eq] at h1
    have hpos1 : 0 < r t * Real.exp (w t) := mul_pos hrt (Real.exp_pos _)
    have h2 := Real.log_le_log hpos1 h1
    rw [Real.log_mul hrt.ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hlam.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    show Real.log (r t) + w t ≤ Real.log (r 0) + w 0
    rw [hr0]; exact h2
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (fun t => Real.log (r t) + w t)
      (r' t / r t + w' t) t := (hlog.and hw).mono fun t ht => ht.1.add ht.2
  have hq' := hlog'.add hw'
  obtain ⟨h1, h2⟩ := TosC11b.deriv_eq_zero_and_second_nonpos_of_isLocalMax hq hq' hloc
  rw [hr'0, hr0, inner_bilinOpL] at h1
  rw [hr'0, hr0] at h2
  simp only [inner_bilinOpL] at h2
  exact ⟨h1, h2⟩

end SGPT.Envelopes.TosC11d
