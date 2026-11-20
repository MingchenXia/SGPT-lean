import SGPT.Envelopes.TosC11dLocal

/-!
# The real-Hessian bound at the maximum point

Lane TOS-C11d (`claude-tos-c11d`, node `tos-c11d:local`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Steps 3–4, for SGPT `thm:Tos_C11` (Tosatti,
Chu–Zhou).  See `TosC11dLocal` for the statement in words.
-/

set_option autoImplicit false
-- nested spaces of continuous multilinear maps need deeper pending instance synthesis, as in
-- Mathlib's own build configuration
set_option maxSynthPendingDepth 3

noncomputable section

open Filter Set
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace ComplexConjugate

namespace SGPT.Envelopes.TosC11d

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

variable {n : ℕ}

theorem abs_apply₂_le (B : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (Y Z : ComplexModel n) :
    |B Y Z| ≤ ‖B‖ * ‖Y‖ * ‖Z‖ := by
  rw [← Real.norm_eq_abs]; exact B.le_opNorm₂ Y Z

/-- Bounds for the jets of the metric on unit vectors. -/
theorem abs_d2g_le {ψ : ComplexModel n → ℝ} {Cg : ℝ}
    (hg2 : ∀ v, ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v‖ ≤ Cg * ‖v‖) (v w Y Z : ComplexModel n) :
    |fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w Y Z| ≤ Cg * ‖v‖ * ‖w‖ * ‖Y‖ * ‖Z‖ := by
  have h1 := abs_apply₂_le (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w) Y Z
  have h2 : ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w‖ ≤ Cg * ‖v‖ * ‖w‖ :=
    ((fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (hg2 v) (norm_nonneg _))
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v w‖ * ‖Y‖ * ‖Z‖ := h1
    _ ≤ Cg * ‖v‖ * ‖w‖ * ‖Y‖ * ‖Z‖ := by gcongr

theorem abs_kosForm_le' {P : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    {c : ℝ} (hP : ‖P‖ ≤ c) (G Y Z : ComplexModel n) :
    |kosForm P G Y Z| ≤ 3 / 2 * c * ‖G‖ * ‖Y‖ * ‖Z‖ :=
  (abs_kosForm_le P G Y Z).trans (by gcongr)

theorem norm_stdVec (i : Fin n) : ‖TosC11c.stdVec i‖ = 1 := by
  simp [TosC11c.stdVec]

theorem norm_I_stdVec (i : Fin n) : ‖Complex.I • TosC11c.stdVec i‖ = 1 := by
  rw [norm_I_smul, norm_stdVec]

/-- The per-index algebra of `D_G log λ₁`. -/
theorem qlog_split {ι : Type*} (s : Finset ι) {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (l : ι → ℝ) (hl : ∀ α ∈ s, l α < lam) (x y : ι → ℝ) (x0 y0 m2e m2f ge gf : ℝ) :
    ((m2e + 2 * ∑ α ∈ s, x α ^ 2 / (lam - l α) - lam * ge) / lam - x0 ^ 2 / lam ^ 2 +
        ((m2f + 2 * ∑ α ∈ s, y α ^ 2 / (lam - l α) - lam * gf) / lam - y0 ^ 2 / lam ^ 2)) /
        (4 * r) =
      (m2e + m2f) / lam / (4 * r) +
        2 * ∑ α ∈ s, ‖cz (x α) (y α)‖ ^ 2 / (r * lam * (lam - l α)) -
        (ge + gf) / (4 * r) - ‖cz x0 y0‖ ^ 2 / (r * lam ^ 2) := by
  have hsum : ∑ α ∈ s, ‖cz (x α) (y α)‖ ^ 2 / (r * lam * (lam - l α)) =
      (∑ α ∈ s, x α ^ 2 / (lam - l α) + ∑ α ∈ s, y α ^ 2 / (lam - l α)) / (4 * r * lam) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    have h1 : 0 < lam - l α := sub_pos.mpr (hl α hα)
    rw [norm_cz_sq]
    field_simp
  rw [hsum, norm_cz_sq]
  field_simp
  ring

/-- The critical point equation in complex form. -/
theorem cz_crit {μ : ℝ} (hμ : μ ≠ 0) (A η' x1 x2 y1 y2 : ℝ) :
    cz (μ * (A * x1 - η' * y1)) (μ * (A * x2 - η' * y2)) / (μ : ℂ) =
      (A : ℂ) * cz x1 x2 - (η' : ℂ) * cz y1 y2 := by
  have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  rw [div_eq_iff hμc]
  apply Complex.ext <;> simp <;> ring

/-- The numerical part of the lower bound for `D_G log λ₁`. -/
theorem log_bound_alg {μ R' β BF n' Cg R T S' m2s gqs U N C₁ : ℝ}
    (hm2 : μ * R' + β * (μ - BF) - n' * Cg - Cg * T -
      (3 / 2 * Cg * S' + 3 * Cg * (μ + 4)) / 2 * T ≤ m2s)
    (hgq : gqs ≤ Cg / 2 * T) (hμ1 : 1 ≤ μ) (hBF : 2 * BF ≤ μ) (hβ : 0 ≤ β) (hCg : 0 ≤ Cg)
    (hS' : 0 ≤ S') (hT : 0 ≤ T) (hRT : 1 ≤ R * T) (hn' : 0 ≤ n')
    (hC₁ : C₁ = Cg * (n' * R + 9 + S')) :
    U + R' - N - C₁ * T + β / 2 ≤ m2s / μ + U - gqs - N := by
  have hμ0 : 0 < μ := by linarith
  suffices h : R' + β / 2 - (C₁ - Cg / 2) * T ≤ m2s / μ by linarith
  rw [le_div_iff₀ hμ0]
  have f1 : n' * Cg ≤ μ * (n' * Cg * (R * T)) := by
    have : n' * Cg ≤ n' * Cg * (R * T) := le_mul_of_one_le_right (by positivity) hRT
    have h2 : n' * Cg * (R * T) ≤ μ * (n' * Cg * (R * T)) :=
      le_mul_of_one_le_left (by positivity) hμ1
    linarith
  have f2 : Cg * T ≤ μ * (Cg * T) := le_mul_of_one_le_left (by positivity) hμ1
  have f3 : Cg * S' * T ≤ μ * (Cg * S' * T) := le_mul_of_one_le_left (by positivity) hμ1
  have f4 : 0 ≤ β * (μ / 2 - BF) := mul_nonneg hβ (by linarith)
  have f5 : 0 ≤ Cg * S' * T := by positivity
  have e1 : (3 / 2 * Cg * S' + 3 * Cg * (μ + 4)) / 2 * T =
      3 / 4 * (Cg * S' * T) + 3 / 2 * (μ * (Cg * T)) + 6 * (Cg * T) := by ring
  have e2 : (R' + β / 2 - (C₁ - Cg / 2) * T) * μ = μ * R' + β * μ / 2 -
      (μ * (n' * Cg * (R * T)) + 17 / 2 * (μ * (Cg * T)) + μ * (Cg * S' * T)) := by
    rw [hC₁]; ring
  have e3 : β * (μ - BF) = β * (μ / 2 - BF) + β * μ / 2 := by ring
  rw [e1, e3] at hm2
  rw [e2]
  linarith

/-- The numerical part of the lower bound for `D_G s`. -/
theorem s_bound_alg {β s0 f2 dfγ nDF nγ K gs C₂ T DGs : ℝ}
    (hDGs : DGs = 2 * (β * (s0 - dfγ)) + K - gs) (hgs : gs ≤ C₂ * T) (hβ : 0 ≤ β)
    (hdf : dfγ ≤ nDF * nγ) (hf2 : f2 = nDF ^ 2) (hs0 : s0 = nγ ^ 2) :
    K - C₂ * T + β * s0 - β * f2 ≤ DGs := by
  have h1 : 2 * (nDF * nγ) ≤ nDF ^ 2 + nγ ^ 2 := by nlinarith [sq_nonneg (nDF - nγ)]
  have h2 : β * (2 * dfγ) ≤ β * (nDF ^ 2 + nγ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hβ
  rw [hDGs, hf2, hs0]
  have e : β * (2 * dfγ) = 2 * (β * dfγ) := by ring
  have e' : β * (nDF ^ 2 + nγ ^ 2) = β * nDF ^ 2 + β * nγ ^ 2 := by ring
  rw [e, e'] at h2
  have e'' : 2 * (β * (nγ ^ 2 - dfγ)) = 2 * (β * nγ ^ 2) - 2 * (β * dfγ) := by ring
  rw [e'']
  linarith

set_option maxHeartbeats 1000000 in
/-- **The real-Hessian bound at the maximum point** (local form of FPT
`lem:penalized-real-hessian`, Steps 3–4). -/
theorem local_bound (hn : 0 < n) {Cg R S CF BF : ℝ} (hCg : 0 ≤ Cg) (hR : 0 < R) (hS : 0 ≤ S) :
    ∃ A Λ : ℝ, 0 < A ∧ ∀ (ψ a F w : ComplexModel n → ℝ) (β M₀ : ℝ) (r : Fin n → ℝ),
      NormalAt ψ → ContDiff ℝ ∞ a → ContDiff ℝ ∞ F → 0 ≤ β →
      (∀ v, ‖fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v‖ ≤ Cg * ‖v‖) →
      (∀ v v', ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v'‖ ≤ Cg * ‖v‖ * ‖v'‖) →
      (∀ᶠ x in 𝓝 (0 : ComplexModel n), (complexHessian (fun y => ψ y + a y) x).det.re =
        Real.exp (β * (a x - F x)) * (complexHessian ψ x).det.re) →
      (∀ v, v ≠ 0 → 0 < leviForm (fun y => ψ y + a y) 0 v) →
      complexHessian (fun y => ψ y + a y) 0 = Matrix.diagonal (fun i => (r i : ℂ)) →
      (∀ i, r i ≤ R) → ‖fderiv ℝ F 0‖ ≤ CF →
      (∀ v, fderiv ℝ (fderiv ℝ F) 0 v v ≤ BF * ‖v‖ ^ 2) →
      sFun ψ a 0 ≤ S →
      (∀ᶠ x in 𝓝 (0 : ComplexModel n), w x =
        -((1 + 2 * CF ^ 2)⁻¹ / 2) * Real.log (1 + S - sFun ψ a x) - A * a x) →
      (∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ Y, Y ≠ 0 → quot ψ a x Y * Real.exp (w x) ≤ M₀) →
      (∃ V, V ≠ 0 ∧ quot ψ a 0 V * Real.exp (w 0) = M₀) →
      ∀ Y, fderiv ℝ (fderiv ℝ a) 0 Y Y ≤ Λ * ‖Y‖ ^ 2 := by
  -- the constants
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = Cg * (n * R + 9 + Real.sqrt S) := ⟨_, rfl⟩
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = Cg * S / 2 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = C₁ + C₂ / 2 + 3 := ⟨_, rfl⟩
  have hA3 : 3 ≤ A := by rw [hA]; linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (1 + 2 * CF ^ 2)⁻¹ := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; positivity
  have hτ1 : τ ≤ 1 := by rw [hτ]; exact inv_le_one_of_one_le₀ (by nlinarith)
  have hτCF : τ * CF ^ 2 ≤ 1 / 2 := by
    rw [hτ, inv_mul_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ, η₀ = τ / (2 * (1 + S)) := ⟨_, rfl⟩
  have hη₀0 : 0 < η₀ := by rw [hη₀]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (4 * A ^ 2 * (n * S + 1))⁻¹ := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε < 1 / 2 := by
    rw [hε, inv_lt_comm₀ (by positivity) (by norm_num)]
    have : 0 ≤ (n : ℝ) * S := by positivity
    nlinarith
  obtain ⟨CE, hCE⟩ : ∃ CE : ℝ, CE = 3 * Cg * Real.sqrt S := ⟨_, rfl⟩
  have hCE0 : 0 ≤ CE := by rw [hCE]; positivity
  obtain ⟨Λth, hΛth⟩ : ∃ Λth : ℝ, Λth = max (max 1 (2 * BF))
      (max (CE ^ 2 / ε) (max (4 * R / ε) (5 / (2 * ε ^ 2)))) := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = max Λth (2 * n * Real.sqrt (2 * R * (A * n / η₀))) :=
    ⟨_, rfl⟩
  refine ⟨A, Λ, hA0, ?_⟩
  intro ψ a F w β M₀ r hN ha hF hβ hg2 hg3 heq hposa hG0 hrR hDF hD2F hs0 hw hmax hM₀
  rw [← hτ] at hw
  have hψ := hN.smooth
  -- the eigenbasis of `D²a(0)`
  obtain ⟨b, μ, i₁, hb, htop, hray⟩ := exists_top_eigen hn (d2_symm ha 0)
  suffices hlamΛ : μ i₁ ≤ Λ by
    intro Y
    exact (hray Y).trans (mul_le_mul_of_nonneg_right hlamΛ (sq_nonneg _))
  by_cases hth : μ i₁ ≤ Λth
  · rw [hΛ]; exact hth.trans (le_max_left _ _)
  push Not at hth
  have hth1 : 1 ≤ μ i₁ := by
    have : (1 : ℝ) ≤ Λth := by rw [hΛth]; exact (le_max_left _ _).trans (le_max_left _ _)
    linarith
  have hthBF : 2 * BF ≤ μ i₁ := by
    have : 2 * BF ≤ Λth := by rw [hΛth]; exact (le_max_right _ _).trans (le_max_left _ _)
    linarith
  have hthE : CE ^ 2 / ε ≤ μ i₁ := by
    have : CE ^ 2 / ε ≤ Λth := by rw [hΛth]; exact (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hthν : 4 * R / ε ≤ μ i₁ := by
    have : 4 * R / ε ≤ Λth := by
      rw [hΛth]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    linarith
  have hthU : 5 / (2 * ε ^ 2) ≤ μ i₁ := by
    have : 5 / (2 * ε ^ 2) ≤ Λth := by
      rw [hΛth]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    linarith
  have hlam0 : 0 < μ i₁ := by linarith
  -- basic facts at `0`
  have hb1 : ‖b i₁‖ = 1 := b.orthonormal.1 i₁
  have hH0b : fderiv ℝ (fderiv ℝ a) 0 (b i₁) (b i₁) = μ i₁ := by
    rw [← inner_bilinOpL, hb, inner_smul_left, real_inner_self_eq_norm_sq, hb1]; simp
  have hquot0 : ∀ V, quot ψ a 0 V = fderiv ℝ (fderiv ℝ a) 0 V V / ‖V‖ ^ 2 := fun V => by
    rw [quot_eq hψ, hN.cov_zero, hN.metric_zero, real_inner_self_eq_norm_sq]
  have hM₀eq : M₀ = μ i₁ * Real.exp (w 0) := by
    obtain ⟨V, hV, hVM⟩ := hM₀
    have h1 := hmax.self_of_nhds (b i₁) (b.orthonormal.ne_zero i₁)
    rw [hquot0, hH0b, hb1, one_pow, div_one] at h1
    have hVn : 0 < ‖V‖ ^ 2 := pow_pos (norm_pos_iff.mpr hV) 2
    have h2 : quot ψ a 0 V ≤ μ i₁ := by
      rw [hquot0, div_le_iff₀ hVn]; exact hray V
    rw [← hVM]
    refine le_antisymm ?_ (hVM ▸ h1)
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  have hmax' : ∀ᶠ x in 𝓝 (0 : ComplexModel n), ∀ Y, Y ≠ 0 →
      quot ψ a x Y * Real.exp (w x) ≤ μ i₁ * Real.exp (w 0) := by
    rw [← hM₀eq]; exact hmax
  have hfr := fun v => hN.frame_ineq ha hs0 hw b μ i₁ hb htop hlam0 hmax' v
  -- names for the jets entering the two inequalities
  obtain ⟨m1, hm1⟩ : ∃ m1 : ComplexModel n → ComplexModel n → ComplexModel n → ℝ, ∀ v Y Z,
      m1 v Y Z = fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v Y Z -
        kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) Y Z := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m2 : ComplexModel n → ℝ, ∀ v,
      m2 v = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 v v (b i₁) (b i₁) -
        (kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁) +
          2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v)
            (b i₁) (b i₁)) := ⟨_, fun _ => rfl⟩
  obtain ⟨gq, hgq⟩ : ∃ gq : ComplexModel n → ℝ, ∀ v,
      gq v = fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (b i₁) (b i₁) := ⟨_, fun _ => rfl⟩
  obtain ⟨sp, hsp⟩ : ∃ sp : ComplexModel n → ℝ, ∀ v,
      sp v = 2 * fderiv ℝ (fderiv ℝ a) 0 v (grad ψ a 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨spp, hspp⟩ : ∃ spp : ComplexModel n → ℝ, ∀ v,
      spp v = 2 * fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v (grad ψ a 0) +
        2 * ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2 -
        fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0) := ⟨_, fun _ => rfl⟩
  obtain ⟨η', hη'⟩ : ∃ η' : ℝ, η' = τ / 2 / (1 + S - sFun ψ a 0) := ⟨_, rfl⟩
  obtain ⟨η'', hη''⟩ : ∃ η'' : ℝ, η'' = τ / 2 / (1 + S - sFun ψ a 0) ^ 2 := ⟨_, rfl⟩
  have hC : ∀ v, m1 v (b i₁) (b i₁) / μ i₁ + (η' * sp v - A * fderiv ℝ a 0 v) = 0 := fun v => by
    rw [hm1, hsp, hη']; exact (hfr v).1
  have hQ : ∀ v, (m2 v + 2 * ∑ i ∈ Finset.univ.erase i₁, m1 v (b i₁) (b i) ^ 2 /
        (μ i₁ - (μ i - 1)) - μ i₁ * gq v) / μ i₁ - m1 v (b i₁) (b i₁) ^ 2 / μ i₁ ^ 2 +
      (η'' * sp v ^ 2 + η' * spp v - A * fderiv ℝ (fderiv ℝ a) 0 v v) ≤ 0 := fun v => by
    simp only [hm1, hm2, hgq, hsp, hspp, hη', hη'']; exact (hfr v).2
  -- the eigenvalues `rᵢ`, the sum `T`, the gradient
  have hrre : ∀ i, (complexHessian (fun y => ψ y + a y) 0 i i).re = r i := fun i => by
    rw [hG0, Matrix.diagonal_apply_eq, Complex.ofReal_re]
  have hr0 : ∀ i, 0 < r i := fun i => by
    rw [← hrre, complexHessian_diagonal_re]
    exact hposa _ (by
      rw [coordinateVector_eq_stdVec]; exact fun h => by simpa [h] using norm_stdVec (n := n) i)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ i, (r i)⁻¹ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; exact Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr0 i)).le
  have hRT : 1 ≤ R * T := by
    have h0 : (r ⟨0, hn⟩)⁻¹ ≤ T := by
      rw [hT]
      exact Finset.single_le_sum (f := fun i => (r i)⁻¹) (fun i _ => (inv_pos.mpr (hr0 i)).le)
        (Finset.mem_univ _)
    have h1 : R⁻¹ ≤ (r ⟨0, hn⟩)⁻¹ := inv_anti₀ (hr0 _) (hrR _)
    have := mul_le_mul_of_nonneg_left (h1.trans h0) hR.le
    rwa [mul_inv_cancel₀ hR.ne'] at this
  have hs0eq : sFun ψ a 0 = ‖fderiv ℝ a 0‖ ^ 2 := hN.sFun_zero a
  have hs00 : 0 ≤ sFun ψ a 0 := by rw [hs0eq]; positivity
  have hγ : ‖grad ψ a 0‖ = ‖fderiv ℝ a 0‖ := by rw [hN.grad_zero, norm_rieszInv]
  have hγS : ‖grad ψ a 0‖ ≤ Real.sqrt S := by
    rw [hγ]; exact Real.le_sqrt_of_sq_le (by rw [← hs0eq]; exact hs0)
  obtain ⟨-, -, hη'lo, hη'hi, -, hη''le⟩ := TosC11b.gradient_weight hτ0 hτ1 hs00 hs0
  rw [← hη'', ← hη'] at hη''le
  rw [← hη'] at hη'lo hη'hi
  have hη'lo' : η₀ ≤ η' := by rw [hη₀]; exact hη'lo
  have hη'0 : 0 ≤ η' := hη₀0.le.trans hη'lo'
  -- bounds for `D²a(0)`
  have hH0sym : ∀ Y Z, fderiv ℝ (fderiv ℝ a) 0 Y Z = fderiv ℝ (fderiv ℝ a) 0 Z Y := d2_symm ha 0
  have hlev : ∀ Y, Y ≠ 0 → 0 < ‖Y‖ ^ 2 + (fderiv ℝ (fderiv ℝ a) 0 Y Y +
      fderiv ℝ (fderiv ℝ a) 0 (Complex.I • Y) (Complex.I • Y)) / 4 := by
    intro Y hY
    have h1 := hposa Y hY
    have ha2 : ContDiffAt ℝ 2 a 0 :=
      ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hψ2 : ContDiffAt ℝ 2 ψ 0 :=
      hψ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hadd := leviForm_add (x := (0 : ComplexModel n)) hψ2 ha2 Y
    change leviForm (ψ + a) 0 Y = _ at hadd
    have h1' : 0 < leviForm (ψ + a) 0 Y := h1
    rw [hadd, leviForm_eq_metricOf, hN.metric_zero, real_inner_self_eq_norm_sq, leviForm,
      realHessian_eq_fderiv, realHessian_eq_fderiv] at h1'
    exact h1'
  have hlow : ∀ Y, -(μ i₁ + 4) * ‖Y‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ a) 0 Y Y := by
    intro Y
    rcases eq_or_ne Y 0 with rfl | hY
    · simp
    have h1' := hlev Y hY
    have h2 := hray (Complex.I • Y)
    rw [norm_I_smul] at h2
    have e : -(μ i₁ + 4) * ‖Y‖ ^ 2 = -(μ i₁ * ‖Y‖ ^ 2) - 4 * ‖Y‖ ^ 2 := by ring
    rw [e]
    linarith
  have hquad : ∀ Y, |fderiv ℝ (fderiv ℝ a) 0 Y Y| ≤ (μ i₁ + 4) * ‖Y‖ ^ 2 := fun Y => by
    rw [abs_le]
    have h4 : 0 ≤ 4 * ‖Y‖ ^ 2 := by positivity
    have e : (μ i₁ + 4) * ‖Y‖ ^ 2 = μ i₁ * ‖Y‖ ^ 2 + 4 * ‖Y‖ ^ 2 := by ring
    exact ⟨by linarith [hlow Y], by rw [e]; linarith [hray Y]⟩
  have hH0YZ := abs_apply_le_of_quad hH0sym hquad
  have hH0v : ∀ v, ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ≤ (μ i₁ + 4) * ‖v‖ := fun v =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun Z => by
      rw [Real.norm_eq_abs]; exact hH0YZ v Z
  -- the error bounds on unit vectors
  have hK1 : ∀ v Y Z, ‖v‖ = 1 → ‖Y‖ = 1 → ‖Z‖ = 1 →
      |kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (grad ψ a 0) Y Z| ≤
        3 / 2 * Cg * Real.sqrt S := by
    intro v Y Z hv hY hZ
    have h := abs_kosForm_le' (P := fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (c := Cg)
      (by have := hg2 v; rwa [hv, mul_one] at this) (grad ψ a 0) Y Z
    rw [hY, hZ, mul_one, mul_one] at h
    exact h.trans (by gcongr)
  have hgq : ∀ v, ‖v‖ = 1 → |gq v| ≤ Cg := fun v hv => by
    rw [hgq]
    have := abs_d2g_le hg2 v v (b i₁) (b i₁)
    rwa [hv, hb1, mul_one, mul_one, mul_one, mul_one] at this
  -- the inequality `D_G Q ≤ 0` at the maximum point
  obtain ⟨Qlog, hQlog⟩ : ∃ Qlog : ComplexModel n → ℝ, ∀ v,
      Qlog v = (m2 v + 2 * ∑ i ∈ Finset.univ.erase i₁, m1 v (b i₁) (b i) ^ 2 /
        (μ i₁ - (μ i - 1)) - μ i₁ * gq v) / μ i₁ - m1 v (b i₁) (b i₁) ^ 2 / μ i₁ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hQsum : frameSum r Qlog + η' * frameSum r spp + η'' * frameSum r (fun v => sp v ^ 2) -
      A * frameSum r (fun v => fderiv ℝ (fderiv ℝ a) 0 v v) ≤ 0 := by
    have h := frameSum_nonpos hr0 (Q := fun v => Qlog v +
      (η'' * sp v ^ 2 + η' * spp v - A * fderiv ℝ (fderiv ℝ a) 0 v v))
      (fun i => ⟨by rw [hQlog]; exact hQ _, by rw [hQlog]; exact hQ _⟩)
    have e : frameSum r (fun v => Qlog v +
        (η'' * sp v ^ 2 + η' * spp v - A * fderiv ℝ (fderiv ℝ a) 0 v v)) =
        frameSum r Qlog + η' * frameSum r spp + η'' * frameSum r (fun v => sp v ^ 2) -
          A * frameSum r (fun v => fderiv ℝ (fderiv ℝ a) 0 v v) := by
      simp only [frameSum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith
  -- `D_G log λ₁`
  obtain ⟨X, hX⟩ : ∃ X : Fin n → ℂ, ∀ i, X i = cz (m1 (TosC11c.stdVec i) (b i₁) (b i₁))
      (m1 (Complex.I • TosC11c.stdVec i) (b i₁) (b i₁)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Yc, hYc⟩ : ∃ Yc : Fin n → Fin (2 * n) → ℂ, ∀ i α,
      Yc i α = cz (m1 (TosC11c.stdVec i) (b i₁) (b α))
        (m1 (Complex.I • TosC11c.stdVec i) (b i₁) (b α)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin n → Fin n → ℂ, ∀ p q,
      Z p q = cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (b i₁))) p q := ⟨_, fun _ _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = 2 * ∑ i, ∑ α ∈ Finset.univ.erase i₁,
      ‖Yc i α‖ ^ 2 / (r i * μ i₁ * (μ i₁ - (μ α - 1))) := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : ℝ, Nn = ∑ i, ‖X i‖ ^ 2 / (r i * μ i₁ ^ 2) := ⟨_, rfl⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = ∑ p, ∑ q, ‖Z p q‖ ^ 2 / (r p * r q * μ i₁) := ⟨_, rfl⟩
  have hl : ∀ α ∈ Finset.univ.erase i₁, μ α - 1 < μ i₁ := fun α _ => by linarith [htop α]
  have hper : ∀ i, (Qlog (TosC11c.stdVec i) + Qlog (Complex.I • TosC11c.stdVec i)) / (4 * r i) =
      (m2 (TosC11c.stdVec i) + m2 (Complex.I • TosC11c.stdVec i)) / μ i₁ / (4 * r i) +
        2 * ∑ α ∈ Finset.univ.erase i₁, ‖Yc i α‖ ^ 2 / (r i * μ i₁ * (μ i₁ - (μ α - 1))) -
        (gq (TosC11c.stdVec i) + gq (Complex.I • TosC11c.stdVec i)) / (4 * r i) -
        ‖X i‖ ^ 2 / (r i * μ i₁ ^ 2) := by
    intro i
    rw [hQlog, hQlog, hX]
    simp only [hYc]
    exact qlog_split _ (hr0 i) hlam0 (fun α => μ α - 1) hl _ _ _ _ _ _ _ _
  have hDGlog : frameSum r Qlog = frameSum r m2 / μ i₁ + U - frameSum r gq - Nn := by
    rw [hU, hNn, frameSum, Finset.sum_congr rfl fun i _ => hper i, frameSum, frameSum,
      Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the twice differentiated equation along `b₁`
  have hcv : ∀ i, ‖coordinateVector (n := n) i‖ = 1 := fun i => by
    rw [coordinateVector_eq_stdVec]; exact norm_stdVec i
  obtain ⟨gv, hgv⟩ : ∃ gv : Fin n → ℝ, ∀ i, gv i = fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (b i₁) (b i₁)
      (coordinateVector i) (coordinateVector i) := ⟨_, fun _ => rfl⟩
  have hg2b : ∀ i, |gv i| ≤ Cg := fun i => by
    have h := abs_d2g_le hg2 (b i₁) (b i₁) (coordinateVector i) (coordinateVector i)
    have e : Cg * ‖b i₁‖ * ‖b i₁‖ * ‖coordinateVector (n := n) i‖ *
        ‖coordinateVector (n := n) i‖ = Cg := by rw [hb1, hcv i]; ring
    rw [hgv]
    exact h.trans_eq e
  have hsumg : -(n * Cg) ≤ ∑ i, gv i := by
    have h : ∑ _i : Fin n, -Cg ≤ ∑ i, gv i :=
      Finset.sum_le_sum fun i _ => by linarith [(abs_le.mp (hg2b i)).1]
    have hc : ∑ _i : Fin n, -Cg = -(n * Cg) := by simp
    linarith
  have hsumg' : ∑ i, gv i / r i ≤ Cg * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (abs_le.mp (hg2b i)).2 (inv_pos.mpr (hr0 i)).le
  have heqb := hN.equation_line ha hF heq r hr0 hG0 (b i₁)
  simp only [← hgv] at heqb
  have hZR : ∑ p, ∑ q, ‖cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 (b i₁))) p q‖ ^ 2 /
      (r p * r q) = μ i₁ * R' := by
    rw [hR', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hZ]
    have := hr0 p
    have := hr0 q
    field_simp
  have hF2 : fderiv ℝ (fderiv ℝ F) 0 (b i₁) (b i₁) ≤ BF := by
    have := hD2F (b i₁); rwa [hb1, one_pow, mul_one] at this
  obtain ⟨X4, hX4def⟩ : ∃ X4 : ℝ, X4 =
      ∑ i, (cHm (leviBil (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 (b i₁) (b i₁))) i i).re /
        r i := ⟨_, rfl⟩
  obtain ⟨F2b, hF2b⟩ : ∃ F2b : ℝ, F2b = fderiv ℝ (fderiv ℝ F) 0 (b i₁) (b i₁) := ⟨_, rfl⟩
  rw [← hF2b] at hF2
  have hX4 : μ i₁ * R' + β * (μ i₁ - BF) - n * Cg - Cg * T ≤ X4 := by
    have h2 := heqb.2
    rw [hZR, hH0b, ← hX4def, ← hF2b] at h2
    have h3 : β * (μ i₁ - BF) ≤ β * (μ i₁ - F2b) :=
      mul_le_mul_of_nonneg_left (by linarith) hβ
    linarith
  -- the lower bound for the sum of the `m₂`
  have hK2 : ∀ v, ‖v‖ = 1 →
      |kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁) +
        2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v) (b i₁) (b i₁)| ≤
      3 / 2 * Cg * Real.sqrt S + 3 * Cg * (μ i₁ + 4) := by
    intro v hv
    have h1 := abs_kosForm_le' (P := fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (c := Cg)
      (by have := hg3 v v; rwa [hv, mul_one, mul_one] at this) (grad ψ a 0) (b i₁) (b i₁)
    have hDγ : ‖fderiv ℝ (grad ψ a) 0 v‖ ≤ μ i₁ + 4 := by
      rw [(hN.grad_line ha v).1, norm_rieszInv]
      have := hH0v v; rwa [hv, mul_one] at this
    have h2 := abs_kosForm_le' (P := fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (c := Cg)
      (by have := hg2 v; rwa [hv, mul_one] at this) (fderiv ℝ (grad ψ a) 0 v) (b i₁) (b i₁)
    rw [hb1, mul_one, mul_one] at h1 h2
    have h1' : 3 / 2 * Cg * ‖grad ψ a 0‖ ≤ 3 / 2 * Cg * Real.sqrt S := by gcongr
    have h2' : 3 / 2 * Cg * ‖fderiv ℝ (grad ψ a) 0 v‖ ≤ 3 / 2 * Cg * (μ i₁ + 4) := by gcongr
    calc _ ≤ |kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁)| +
          |2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v) (b i₁) (b i₁)| :=
          abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_two]; linarith
  have hm2fs : μ i₁ * R' + β * (μ i₁ - BF) - n * Cg - Cg * T -
      (3 / 2 * Cg * Real.sqrt S + 3 * Cg * (μ i₁ + 4)) / 2 * T ≤ frameSum r m2 := by
    have hsplit : frameSum r m2 = frameSum r
        (fun v => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ a))) 0 v v (b i₁) (b i₁)) -
        frameSum r (fun v =>
          kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁) +
          2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v)
            (b i₁) (b i₁)) := by
      rw [← frameSum_sub]
      congr 1
      funext v
      rw [hm2]
    have hKs := frameSum_le hr0 (Q := fun v =>
      kosForm (fderiv ℝ (fderiv ℝ (fderiv ℝ (metricOf ψ))) 0 v v) (grad ψ a 0) (b i₁) (b i₁) +
          2 * kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v) (fderiv ℝ (grad ψ a) 0 v)
            (b i₁) (b i₁)) (c := 3 / 2 * Cg * Real.sqrt S + 3 * Cg * (μ i₁ + 4)) fun i =>
      ⟨(abs_le.mp (hK2 _ (norm_stdVec i))).2, (abs_le.mp (hK2 _ (norm_I_stdVec i))).2⟩
    rw [frameSum_d4 ha, ← hX4def] at hsplit
    rw [← hT] at hKs
    linarith
  have hgqs : frameSum r gq ≤ Cg / 2 * T := by
    have := frameSum_le hr0 (Q := gq) (c := Cg) fun i =>
      ⟨(abs_le.mp (hgq _ (norm_stdVec i))).2, (abs_le.mp (hgq _ (norm_I_stdVec i))).2⟩
    rwa [← hT] at this
  have hlog : U + R' - Nn - C₁ * T + β / 2 ≤ frameSum r Qlog := by
    rw [hDGlog]
    exact log_bound_alg hm2fs hgqs hth1 hthBF hβ hCg (Real.sqrt_nonneg S) hT0 hRT
      (Nat.cast_nonneg n) hC₁
  -- `D_G s`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * frameSum r (fun v => ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨gs, hgs⟩ : ∃ gs : ℝ, gs = frameSum r
      (fun v => fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0)) := ⟨_, rfl⟩
  obtain ⟨dfγ, hdfγ⟩ : ∃ dfγ : ℝ, dfγ = fderiv ℝ F 0 (grad ψ a 0) := ⟨_, rfl⟩
  have heqγ := (hN.equation_line ha hF heq r hr0 hG0 (grad ψ a 0)).1
  have hDGs : frameSum r spp = 2 * (β * (sFun ψ a 0 - dfγ)) + K - gs := by
    have e : frameSum r spp = 2 * frameSum r (fun v => fderiv ℝ (fderiv ℝ (fderiv ℝ a)) 0 v v
        (grad ψ a 0)) + 2 * frameSum r (fun v => ‖fderiv ℝ (fderiv ℝ a) 0 v‖ ^ 2) - gs := by
      rw [hgs, ← frameSum_const_mul, ← frameSum_const_mul, ← frameSum_add, ← frameSum_sub]
      congr 1
      funext v
      rw [hspp]
    rw [e, frameSum_d3 ha, heqγ, ← hK, ← hdfγ]
    rfl
  have hgsb : gs ≤ C₂ * T := by
    have hb' : ∀ v, ‖v‖ = 1 →
        fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0) ≤ Cg * S := by
      intro v hv
      have h := abs_d2g_le hg2 v v (grad ψ a 0) (grad ψ a 0)
      have hγ2 : ‖grad ψ a 0‖ ^ 2 ≤ S := by rw [hγ, ← hs0eq]; exact hs0
      have e : Cg * ‖v‖ * ‖v‖ * ‖grad ψ a 0‖ * ‖grad ψ a 0‖ = Cg * ‖grad ψ a 0‖ ^ 2 := by
        rw [hv]; ring
      have h2 : Cg * ‖grad ψ a 0‖ ^ 2 ≤ Cg * S := mul_le_mul_of_nonneg_left hγ2 hCg
      exact (le_abs_self _).trans (h.trans (e ▸ h2))
    have := frameSum_le hr0 (Q := fun v =>
      fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v v (grad ψ a 0) (grad ψ a 0)) (c := Cg * S) fun i =>
      ⟨hb' _ (norm_stdVec i), hb' _ (norm_I_stdVec i)⟩
    rw [hgs, hC₂]
    rw [← hT] at this
    linarith
  have hdf : dfγ ≤ ‖fderiv ℝ F 0‖ * ‖grad ψ a 0‖ := by
    rw [hdfγ]; exact (le_abs_self _).trans (by
      rw [← Real.norm_eq_abs]; exact (fderiv ℝ F 0).le_opNorm _)
  have hs : K - C₂ * T + β * sFun ψ a 0 - β * ‖fderiv ℝ F 0‖ ^ 2 ≤ frameSum r spp :=
    s_bound_alg hDGs hgsb hβ hdf rfl (by rw [hs0eq, hγ])
  -- `D_G a = n - T`
  have hDGa : frameSum r (fun v => fderiv ℝ (fderiv ℝ a) 0 v v) = n - T := by
    have ha2 : ContDiffAt ℝ 2 a 0 :=
      ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hψ2 : ContDiffAt ℝ 2 ψ 0 :=
      hψ.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    have hadd := complexHessian_add hψ2 ha2
    have hadd' : complexHessian (fun y => ψ y + a y) 0 = complexHessian ψ 0 + complexHessian a 0 :=
      hadd
    rw [hN.complexHessian_zero, hG0] at hadd'
    have hre : ∀ i, (complexHessian a 0 i i).re = r i - 1 := fun i => by
      have := congrFun (congrFun hadd' i) i
      rw [Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.one_apply_eq] at this
      have h2 := congrArg Complex.re this
      simp only [Complex.ofReal_re, Complex.add_re, Complex.one_re] at h2
      linarith
    rw [frameSum_d2, hT]
    simp only [hre]
    have e : ∀ i, (r i - 1) / r i = 1 - (r i)⁻¹ := fun i => by
      have := hr0 i; field_simp
    simp only [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- the inequality at the maximum point
  have hηf : η' * ‖fderiv ℝ F 0‖ ^ 2 ≤ 1 / 4 := by
    have h1 : ‖fderiv ℝ F 0‖ ^ 2 ≤ CF ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hDF 2
    have h2 : η' * ‖fderiv ℝ F 0‖ ^ 2 ≤ τ / 2 * CF ^ 2 :=
      mul_le_mul hη'hi h1 (sq_nonneg _) (by positivity)
    linarith
  have hmaxI := TosC11b.max_inequality_of_components hQsum hlog hs hDGa hη'0
    (by linarith) hηf hβ hT0 hC₂0
  -- the splitting and the absorption of the third-order term
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Fin (2 * n) → ℝ, ∀ α, μ' α = ⟪Complex.I • b i₁, b α⟫ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Fin n → ℂ, ∀ q, ν q = (Real.sqrt 2 : ℂ) * b i₁ q := ⟨_, fun _ => rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Fin n → ℂ, ∀ i, E i = X i - ((Real.sqrt 2 : ℂ) *
      ∑ q, conj (ν q) * Z i q - Complex.I * ∑ α ∈ Finset.univ.erase i₁, (μ' α : ℂ) * Yc i α) :=
    ⟨_, fun _ => rfl⟩
  have hsplitE : ∀ i, X i = (Real.sqrt 2 : ℂ) * ∑ q, conj (ν q) * Z i q -
      Complex.I * ∑ α ∈ Finset.univ.erase i₁, (μ' α : ℂ) * Yc i α + E i := fun i => by
    rw [hE]; ring
  have hIb1 : ‖Complex.I • b i₁‖ = 1 := by rw [norm_I_smul, hb1]
  have hEb : ∀ i, ‖E i‖ ≤ CE := by
    intro i
    have hsi := split_identity ha (fun v => kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 v)
      (grad ψ a 0)) b i₁ i
    simp only [sub_apply] at hsi
    have hEi : E i = -cz (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (b i₁))
        (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (Complex.I • TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (b i₁)) -
        Complex.I * cz (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (Complex.I • b i₁))
        (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (Complex.I • TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (Complex.I • b i₁)) := by
      rw [← hsi, hE, hX]
      simp only [hYc, hZ, hm1, hν, hμ']
    rw [hEi]
    have k1 := hK1 _ _ _ (norm_stdVec i) hb1 hb1
    have k2 := hK1 _ _ _ (norm_I_stdVec i) hb1 hb1
    have k3 := hK1 _ _ _ (norm_stdVec i) hb1 hIb1
    have k4 := hK1 _ _ _ (norm_I_stdVec i) hb1 hIb1
    have c1 := norm_cz_le (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (b i₁))
        (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (Complex.I • TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (b i₁))
    have c2 := norm_cz_le (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (Complex.I • b i₁))
        (kosForm (fderiv ℝ (fderiv ℝ (metricOf ψ)) 0 (Complex.I • TosC11c.stdVec i))
          (grad ψ a 0) (b i₁) (Complex.I • b i₁))
    calc _ ≤ ‖-cz _ _‖ + ‖Complex.I * cz _ _‖ := norm_sub_le _ _
      _ = ‖cz _ _‖ + ‖cz _ _‖ := by rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      _ ≤ CE := by rw [hCE]; linarith
  -- the coefficients of `i b₁` and the positivity bound
  have hμ'0 : μ' i₁ = 0 := by rw [hμ', real_inner_comm]; exact inner_I_smul_self _
  have hμsum : ∑ α ∈ Finset.univ.erase i₁, μ' α ^ 2 = 1 := by
    have h := sum_inner_sq b (Complex.I • b i₁)
    rw [hIb1, one_pow, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)] at h
    rw [← h, real_inner_comm, ← hμ', hμ'0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hμ', real_inner_comm]
  have hHIb : fderiv ℝ (fderiv ℝ a) 0 (Complex.I • b i₁) (Complex.I • b i₁) =
      ∑ α ∈ Finset.univ.erase i₁, (μ α - 1) * μ' α ^ 2 + 1 := by
    rw [apply_self_eq_sum_eigen _ b μ hb, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₁),
      real_inner_comm, ← hμ', hμ'0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
    have e : ∑ α ∈ Finset.univ.erase i₁, μ α * ⟪b α, Complex.I • b i₁⟫ ^ 2 =
        ∑ α ∈ Finset.univ.erase i₁, ((μ α - 1) * μ' α ^ 2 + μ' α ^ 2) := by
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [real_inner_comm, ← hμ']
      ring
    rw [e, Finset.sum_add_distrib, hμsum]
  have hpos : μ i₁ - ∑ α ∈ Finset.univ.erase i₁, (μ α - 1) * μ' α ^ 2 ≤ 2 * μ i₁ + 5 := by
    have h := hlev (b i₁) (b.orthonormal.ne_zero i₁)
    rw [hb1, hH0b, hHIb] at h
    linarith
  have hνb : ∑ q, r q * ‖ν q‖ ^ 2 ≤ 2 * R := by
    have h1 : ∑ q, r q * ‖ν q‖ ^ 2 ≤ ∑ q, R * (2 * ‖b i₁ q‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [hν, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_right (hrR q) (by positivity)
    have h2 : ∑ q, ‖b i₁ q‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, hb1, one_pow]
    rw [← Finset.mul_sum, ← Finset.mul_sum, h2] at h1
    linarith
  -- the critical point equation
  obtain ⟨aa, haa⟩ : ∃ aa : Fin n → ℂ, ∀ i, aa i = cz (fderiv ℝ a 0 (TosC11c.stdVec i))
      (fderiv ℝ a 0 (Complex.I • TosC11c.stdVec i)) := ⟨_, fun _ => rfl⟩
  obtain ⟨ss, hss⟩ : ∃ ss : Fin n → ℂ, ∀ i, ss i = cz (sp (TosC11c.stdVec i))
      (sp (Complex.I • TosC11c.stdVec i)) := ⟨_, fun _ => rfl⟩
  have hcrit : ∀ i, X i / μ i₁ = A * aa i - η' * ss i := by
    intro i
    have h1 := hC (TosC11c.stdVec i)
    have h2 := hC (Complex.I • TosC11c.stdVec i)
    have e1 : m1 (TosC11c.stdVec i) (b i₁) (b i₁) =
        μ i₁ * (A * fderiv ℝ a 0 (TosC11c.stdVec i) - η' * sp (TosC11c.stdVec i)) := by
      have h1' : m1 (TosC11c.stdVec i) (b i₁) (b i₁) / μ i₁ =
          A * fderiv ℝ a 0 (TosC11c.stdVec i) - η' * sp (TosC11c.stdVec i) := by linarith
      rw [← h1', mul_div_cancel₀ _ hlam0.ne']
    have e2 : m1 (Complex.I • TosC11c.stdVec i) (b i₁) (b i₁) =
        μ i₁ * (A * fderiv ℝ a 0 (Complex.I • TosC11c.stdVec i) -
          η' * sp (Complex.I • TosC11c.stdVec i)) := by
      have h2' : m1 (Complex.I • TosC11c.stdVec i) (b i₁) (b i₁) / μ i₁ =
          A * fderiv ℝ a 0 (Complex.I • TosC11c.stdVec i) -
            η' * sp (Complex.I • TosC11c.stdVec i) := by linarith
      rw [← h2', mul_div_cancel₀ _ hlam0.ne']
    rw [hX, e1, e2, haa, hss]
    exact cz_crit hlam0.ne' _ _ _ _ _ _
  -- the thresholds
  have hthE' : CE ^ 2 ≤ ε * μ i₁ ^ 2 := by
    have h1 : CE ^ 2 ≤ μ i₁ * ε := (div_le_iff₀ hε0).mp hthE
    have hsq : μ i₁ ≤ μ i₁ ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hlam0.le hth1
    have h2 : ε * μ i₁ ≤ ε * μ i₁ ^ 2 := mul_le_mul_of_nonneg_left hsq hε0.le
    linarith only [h1, h2]
  have hthν' : 2 * (2 * R) ≤ ε * μ i₁ := by
    have h1 := (div_le_iff₀ hε0).mp hthν
    linarith only [h1]
  have hthU' : (5 : ℝ) ≤ 2 * ε ^ 2 * μ i₁ := by
    have h1 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ε ^ 2)).mp hthU
    linarith only [h1]
  have habs := TosC11b.third_order_absorption (Finset.univ.erase i₁) r hr0 hlam0
    (fun α => μ α - 1) hl X Yc Z ν μ' E hsplitE hμsum (c₃ := 5) (by norm_num) hpos hνb hEb aa ss
    hcrit hε0 hε1 hthE' hthν' hthU'
  -- the choice of `ε`
  have haa2 : ∑ i, ‖aa i‖ ^ 2 ≤ n * S := by
    have h1 : ∀ i, ‖aa i‖ ^ 2 ≤ S := fun i => by
      rw [haa, norm_cz_sq]
      have b1 : |fderiv ℝ a 0 (TosC11c.stdVec i)| ≤ ‖fderiv ℝ a 0‖ := by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ a 0).le_opNorm _).trans_eq (by rw [norm_stdVec, mul_one])
      have b2 : |fderiv ℝ a 0 (Complex.I • TosC11c.stdVec i)| ≤ ‖fderiv ℝ a 0‖ := by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ a 0).le_opNorm _).trans_eq (by rw [norm_I_stdVec, mul_one])
      have c1 := pow_le_pow_left₀ (abs_nonneg _) b1 2
      have c2 := pow_le_pow_left₀ (abs_nonneg _) b2 2
      rw [sq_abs] at c1 c2
      have hDa : ‖fderiv ℝ a 0‖ ^ 2 ≤ S := by rw [← hs0eq]; exact hs0
      linarith only [c1, c2, hDa, hS]
    calc ∑ i, ‖aa i‖ ^ 2 ≤ ∑ _i : Fin n, S := Finset.sum_le_sum fun i _ => h1 i
      _ = n * S := by simp
  have h4e := TosC11b.four_eps_mul_sum_le r hr0 aa haa2 hA0.ne'
  rw [← hε, ← hT] at h4e
  rw [← hT] at habs
  have hS2 : frameSum r (fun v => sp v ^ 2) = ∑ i, ‖ss i‖ ^ 2 / r i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hss, norm_cz_sq]
    have := hr0 i
    field_simp
  have hU' : U = 2 * ∑ i, ∑ α ∈ Finset.univ.erase i₁,
      ‖Yc i α‖ ^ 2 / (r i * μ i₁ * (μ i₁ - (fun α => μ α - 1) α)) := hU
  rw [← hU', ← hNn, ← hR', ← hS2] at habs
  have hS20 : 0 ≤ frameSum r (fun v => sp v ^ 2) := by
    rw [hS2]; exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hr0 i).le
  have hKT := TosC11b.eta_K_add_T_le hmaxI habs h4e hη''le hS20 (by rw [hA]) hT0 hβ hη'0 hs00
  -- `η' K + T ≤ A n` bounds `D²a(0)` on the real frame, hence the top eigenvalue
  have hK0 : K ≤ A * n / η₀ := by
    have hK00 : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
        div_nonneg (by positivity) (by linarith only [hr0 i]))
    rw [le_div_iff₀ hη₀0]
    have h1 : η₀ * K ≤ η' * K := mul_le_mul_of_nonneg_right hη'lo' hK00
    linarith only [h1, hKT, hT0]
  have hframe : ∀ j, ‖fderiv ℝ (fderiv ℝ a) 0 (TosC11c.stdVec j)‖ ≤
      Real.sqrt (2 * R * (A * n / η₀)) ∧
      ‖fderiv ℝ (fderiv ℝ a) 0 (Complex.I • TosC11c.stdVec j)‖ ≤
      Real.sqrt (2 * R * (A * n / η₀)) := by
    intro j
    have hterm : (‖fderiv ℝ (fderiv ℝ a) 0 (TosC11c.stdVec j)‖ ^ 2 +
        ‖fderiv ℝ (fderiv ℝ a) 0 (Complex.I • TosC11c.stdVec j)‖ ^ 2) / (4 * r j) ≤ K / 2 := by
      rw [hK]
      have := Finset.single_le_sum (f := fun i =>
        (‖fderiv ℝ (fderiv ℝ a) 0 (TosC11c.stdVec i)‖ ^ 2 +
          ‖fderiv ℝ (fderiv ℝ a) 0 (Complex.I • TosC11c.stdVec i)‖ ^ 2) / (4 * r i))
        (fun i _ => div_nonneg (by positivity) (by linarith only [hr0 i])) (Finset.mem_univ j)
      simp only [frameSum] at this ⊢
      linarith only [this]
    have hrj := hr0 j
    have hsum2 : ‖fderiv ℝ (fderiv ℝ a) 0 (TosC11c.stdVec j)‖ ^ 2 +
        ‖fderiv ℝ (fderiv ℝ a) 0 (Complex.I • TosC11c.stdVec j)‖ ^ 2 ≤ 2 * R * (A * n / η₀) := by
      rw [div_le_iff₀ (by positivity)] at hterm
      have h1 : K / 2 * (4 * r j) ≤ A * n / η₀ / 2 * (4 * R) := by
        have hK00 : 0 ≤ K := by
          rw [hK]
          exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
            div_nonneg (by positivity) (by linarith only [hr0 i]))
        apply mul_le_mul (by linarith only [hK0]) (by linarith only [hrR j]) (by positivity)
          (by positivity)
      have e : A * n / η₀ / 2 * (4 * R) = 2 * R * (A * n / η₀) := by ring
      linarith only [hterm, h1, e]
    have hx := sq_nonneg ‖fderiv ℝ (fderiv ℝ a) 0 (TosC11c.stdVec j)‖
    have hy := sq_nonneg ‖fderiv ℝ (fderiv ℝ a) 0 (Complex.I • TosC11c.stdVec j)‖
    exact ⟨Real.le_sqrt_of_sq_le (by linarith only [hsum2, hy]),
      Real.le_sqrt_of_sq_le (by linarith only [hsum2, hx])⟩
  have hHb := norm_apply_le_of_frame' (fderiv ℝ (fderiv ℝ a) 0) hframe (b i₁)
  rw [hb1, mul_one] at hHb
  have hlamb : μ i₁ ≤ 2 * n * Real.sqrt (2 * R * (A * n / η₀)) := by
    rw [← hH0b]
    calc fderiv ℝ (fderiv ℝ a) 0 (b i₁) (b i₁) ≤ |fderiv ℝ (fderiv ℝ a) 0 (b i₁) (b i₁)| :=
          le_abs_self _
      _ = ‖fderiv ℝ (fderiv ℝ a) 0 (b i₁) (b i₁)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (fderiv ℝ a) 0 (b i₁)‖ * ‖b i₁‖ := (fderiv ℝ (fderiv ℝ a) 0 (b i₁)).le_opNorm _
      _ = ‖fderiv ℝ (fderiv ℝ a) 0 (b i₁)‖ := by rw [hb1, mul_one]
      _ ≤ _ := hHb
  rw [hΛ]
  exact hlamb.trans (le_max_right _ _)

end SGPT.Envelopes.TosC11d
