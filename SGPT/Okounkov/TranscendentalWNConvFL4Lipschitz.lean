import SGPT.Okounkov.TranscendentalWNConvFL4Statement
import SGPT.Okounkov.TranscendentalWNConvFLLipschitz

/-!
# WN21 Corollary 7.6 along fibre discs from Lemma 7.5

Blueprint `claude-tok-wn-fl4`, node `tok-wn-fl4:lipschitz`; source WN21 §7, Corollary 7.6 and the
paragraph after it (`references/wn21-restricted-volume`).

* `abs_sub_le_of_discLaplacian` (**the rescaled Lipschitz bound**, chart-free): if `|f + k| ≤ C` on
  the closed disc of radius `R = e^{-k/2}` and `f` is there the uniform limit of `C²` functions with
  `-C ≤ Δ u_j ≤ C e^k` on the open disc, then `|f(t) - f(0)| ≤ max(C, 1) A e^{k/2} |t|` for
  `|t| ≤ R/2`, with the universal constant `A ≥ 0` of WN-LIP (`lipschitzOfLaplacianStatement`).
  Proof: `h(w) = (f(R w) + k)/max(C, 1)` has `|h| ≤ 1` on the unit disc and `|∫ h Δφ| ≤ ∫ |φ|`
  (the `abs_integral_mul_laplacian_le_of_tendstoUniformlyOn`, from Green's identity for
  the approximants), so WN-LIP applies to `h` at `w = t / R`.
* `excLipschitz_of_excDiscLaplacian : ExcDiscLaplacianStatement F → ExcLipschitzStatement F`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Metric Laplacian Complex
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain

/-- **The rescaled Lipschitz bound** of a function with the bounds of WN21 Lemma 7.5 on the disc
of radius `e^{-k/2}`. -/
theorem abs_sub_le_of_discLaplacian : ∃ A : ℝ, 0 ≤ A ∧ ∀ (k : ℕ) (C : ℝ) (f : ℂ → ℝ)
    (u : ℕ → ℂ → ℝ), (∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) → |f t + k| ≤ C) →
    (∀ j, ContDiff ℝ 2 (u j)) →
    TendstoUniformlyOn u f atTop (closedBall 0 (Real.exp (-(k : ℝ) / 2))) →
    (∀ j, ∀ t ∈ ball (0 : ℂ) (Real.exp (-(k : ℝ) / 2)),
      -C ≤ Δ (u j) t ∧ Δ (u j) t ≤ C * Real.exp k) →
    ∀ t : ℂ, ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) / 2 →
      |f t - f 0| ≤ max C 1 * A * Real.exp ((k : ℝ) / 2) * ‖t‖ := by
  obtain ⟨A, hA⟩ := lipschitzOfLaplacianStatement
  refine ⟨|A|, abs_nonneg A, fun k C f uj hbd hu2 hconv hΔ t htR => ?_⟩
  set C₁ : ℝ := max C 1 with hC₁
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC₁ : C ≤ C₁ := le_max_left _ _
  set R : ℝ := Real.exp (-(k : ℝ) / 2) with hR
  have hR0 : 0 < R := Real.exp_pos _
  have hR2 : R ^ 2 = Real.exp (-(k : ℝ)) := by
    rw [hR, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hek : Real.exp (-(k : ℝ)) * Real.exp k = 1 := by
    rw [← Real.exp_add]
    simp
  have hΔ' : ∀ j, ∀ t ∈ ball (0 : ℂ) R, |R ^ 2 * Δ (uj j) t| ≤ C₁ := by
    intro j t ht
    obtain ⟨h1, h2⟩ := hΔ j t ht
    have hCnn : 0 ≤ C := by
      have := h1.trans h2
      have hpos : 0 < Real.exp (k : ℝ) := Real.exp_pos _
      by_contra hneg
      push Not at hneg
      nlinarith
    have hek1 : Real.exp (-(k : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
    rw [hR2, abs_le]
    have hpos : 0 < Real.exp (-(k : ℝ)) := Real.exp_pos _
    constructor
    · have : -C ≤ Real.exp (-(k : ℝ)) * Δ (uj j) t := by
        have h3 : Real.exp (-(k : ℝ)) * (-C) ≤ Real.exp (-(k : ℝ)) * Δ (uj j) t :=
          mul_le_mul_of_nonneg_left h1 hpos.le
        nlinarith
      linarith
    · have h3 : Real.exp (-(k : ℝ)) * Δ (uj j) t ≤ Real.exp (-(k : ℝ)) * (C * Real.exp k) :=
        mul_le_mul_of_nonneg_left h2 hpos.le
      have h4 : Real.exp (-(k : ℝ)) * (C * Real.exp k) = C := by
        rw [mul_comm C, ← mul_assoc, hek, one_mul]
      linarith
  -- the rescaled function
  set hfun : ℂ → ℝ := fun w => (f (R • w) + k) / C₁ with hhfun
  have hmaps : MapsTo (fun w : ℂ => R • w) (closedBall 0 1) (closedBall 0 R) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR0.le] at *
    nlinarith
  have hfc : ContinuousOn f (closedBall 0 R) := hconv.continuousOn
    (Frequently.of_forall fun j => (hu2 j).continuous.continuousOn)
  have hcont : ContinuousOn hfun (closedBall 0 1) :=
    ((hfc.comp (continuous_const_smul R).continuousOn hmaps).add continuousOn_const).div_const C₁
  have hbound : ∀ w ∈ closedBall (0 : ℂ) 1, |hfun w| ≤ 1 := by
    intro w hw
    have h1 := hbd (R • w) (by simpa using hmaps hw)
    rw [hhfun, abs_div, abs_of_pos hC₁0, div_le_one hC₁0]
    exact h1.trans hCC₁
  have hlap := abs_integral_mul_laplacian_le_of_tendstoUniformlyOn (a := (k : ℝ)) hR0 hC₁0 hu2
    hconv hΔ'
  have hlip := hA hfun hcont hbound (fun φ hφ hφc hφs => hlap φ hφ hφc hφs) (R⁻¹ • t) (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), inv_mul_le_iff₀ hR0]
    linarith)
  have hRt : R • (R⁻¹ • t) = t := by rw [smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
  simp only [hhfun, hRt, smul_zero] at hlip
  rw [← sub_div, abs_div, abs_of_pos hC₁0, div_le_iff₀ hC₁0] at hlip
  have hsub : f t + k - (f 0 + k) = f t - f 0 := by ring
  rw [hsub] at hlip
  have hnorm : ‖R⁻¹ • t‖ = Real.exp ((k : ℝ) / 2) * ‖t‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), hR, ← Real.exp_neg]
    congr 2
    ring
  rw [hnorm] at hlip
  have hA' : A * (Real.exp ((k : ℝ) / 2) * ‖t‖) ≤ |A| * (Real.exp ((k : ℝ) / 2) * ‖t‖) :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  calc |f t - f 0| ≤ A * (Real.exp ((k : ℝ) / 2) * ‖t‖) * C₁ := hlip
    _ ≤ |A| * (Real.exp ((k : ℝ) / 2) * ‖t‖) * C₁ := mul_le_mul_of_nonneg_right hA' hC₁0.le
    _ = C₁ * |A| * Real.exp ((k : ℝ) / 2) * ‖t‖ := by ring

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl4:lipschitz`** (WN21 Corollary 7.6 along fibre discs) from Lemma 7.5 along the
discs (`ExcDiscLaplacianStatement`) and WN-LIP. -/
theorem excLipschitz_of_excDiscLaplacian (hD : ExcDiscLaplacianStatement F) :
    ExcLipschitzStatement F := by
  intro 𝒳 _ _ _ μ hμ Θ Ψ hΨ 𝒵 _ _ _ π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ G Γ hG hΓ hΓμ y₀
    hy₀ hΨy₀
  obtain ⟨R, hR, C, k₀, hC⟩ := hD 𝒳 μ hμ Θ Ψ hΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ G Γ hG
    hΓ hΓμ y₀ hy₀ hΨy₀
  obtain ⟨A, hA0, hA⟩ := abs_sub_le_of_discLaplacian
  refine ⟨R, hR, C + max C 1 * A, k₀, fun k hk y hy => ?_⟩
  obtain ⟨hbd, uj, hu2, hconv, hΔ⟩ := hC k hk y hy
  set v : 𝒳 → EReal := prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ with hv
  have hg : Continuous (cutoffObstacle μ χ k) :=
    (continuous_cutoffObstacleLine hχ k).comp (continuous_snd.comp hμ.continuous)
  have hvtop : ∀ z, v z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (prescribedEnvelope_le hg z)
  have hR1 : ‖(0 : ℂ)‖ ≤ Real.exp (-(k : ℝ) / 2) := by simp [(Real.exp_pos _).le]
  obtain ⟨hG0, hb0, hc0⟩ := hbd 0 hR1
  have hCnn : 0 ≤ C := (abs_nonneg _).trans hc0
  have hCA : 0 ≤ max C 1 * A := mul_nonneg (le_max_of_le_right zero_le_one) hA0
  refine ⟨hG0, ?_, fun t ht => ?_⟩
  · rw [(EReal.coe_toReal (hvtop _) hb0).symm, EReal.coe_le_coe_iff]
    have := (abs_le.mp hc0).1
    linarith
  have htR : ‖t‖ ≤ Real.exp (-(k : ℝ) / 2) := by
    have := (Real.exp_pos (-(k : ℝ) / 2)).le
    linarith
  obtain ⟨hGt, hbt, -⟩ := hbd t htR
  refine ⟨hGt, hbt, ?_⟩
  have hl := hA k C (fun t => (v (Γ (t, y))).toReal) uj (fun t ht => (hbd t ht).2.2) hu2 hconv
    hΔ t ht
  calc |(v (Γ (t, y))).toReal - (v (Γ (0, y))).toReal|
      ≤ max C 1 * A * Real.exp ((k : ℝ) / 2) * ‖t‖ := hl
    _ ≤ (C + max C 1 * A) * Real.exp ((k : ℝ) / 2) * ‖t‖ := by
        have : 0 ≤ Real.exp ((k : ℝ) / 2) * ‖t‖ := by positivity
        nlinarith

end SGPT.Okounkov.TranscendentalWN
