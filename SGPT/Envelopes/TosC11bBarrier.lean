import SGPT.Envelopes.TosC11Rayleigh
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Rayleigh barrier with a variable metric, and the one-dimensional maximum principle

Lane TOS-C11b (`claude-tos-c11b`, nodes `tos-c11b:rayleigh-metric`, `tos-c11b:line-max`).  Source:
Xia, *Foundations of pluripotential theory*, `lem:penalized-real-hessian`, Steps 2–3, for SGPT
`thm:Tos_C11` (Tosatti, Chu–Zhou).

FPT works with the largest eigenvalue `λ₁(Φ)` of `Φ = g₀⁻¹(∇²a - B₀)`, made smooth near the maximum
point `x₀` by the perturbation `B₀` (a simple top eigenvalue), and differentiates it twice in a
`g₀`-orthonormal frame obtained by Gram–Schmidt.  We use instead a **lower barrier**: in a chart
centred at `x₀` with `g₀(x₀)` the Euclidean product and `Dg₀(x₀) = 0`, for the curve
`Y(t) = b + t w` (with `b = V₁` and `w ⊥ b` explicit) the Rayleigh quotient
`r(t) = M(t)(Y, Y) / g(t)(Y, Y)` of `M(t) = (∇²a - B₀)(x₀ + t v)` and `g(t) = g₀(x₀ + t v)` lies
below `λ₁(Φ)(x₀ + t v)` for every `t` (it is one of the Rayleigh quotients whose supremum is
`λ₁(Φ)`), equals it at `t = 0`, and has

* `r(0) = λ`, `r'(0) = ⟪M'(0) b, b⟫`,
* `r''(0) = ⟪M''(0) b, b⟫ + 2 Σ_{α ≠ 1} ⟪M'(0) b, b_α⟫² / (λ - λ_α) - λ ⟪g''(0) b, b⟫`

(`rayleigh_quotient_metric`).  The vector `w = Σ_{α ≠ 1} ⟪M'(0) b, b_α⟫/(λ - λ_α) b_α` depends
linearly on `M'(0)`, hence on the direction `v`, so one vector field `Y(x) = b + L(x - x₀)` serves all
directions.  The last term replaces the second derivatives of the Gram–Schmidt frame in FPT (both
are bounded by `C λ`).  This extends the barrier of lane TOS-C11 (`exists_rayleigh_barrier`, constant
metric) to a variable metric.

* `deriv_eq_zero_and_second_nonpos_of_isLocalMax` — the one-dimensional maximum principle used
  along every real line through `x₀`: at a local maximum `q'(0) = 0` and `q''(0) ≤ 0`.
* `hasDerivAt_log_comp_second` — `(log r)''(0) = r''(0)/r(0) - r'(0)²/r(0)²`.
* `gradient_weight` — the weight `η(s) = -(τ/2) log(1 + S - s)` of FPT Step 2 and its bounds
  `τ/(2(1 + S)) ≤ η' ≤ τ/2`, `η'' = 2η'²/τ ≥ 2η'²` (`eq:real-hessian-gradient-weight`).
* `abs_le_of_sum_ge_of_le` — bounding all eigenvalues by the largest one and a lower bound for
  their sum (FPT Step 2: "it therefore suffices to bound `ℓ` from above").
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

namespace SGPT.Envelopes.TosC11b

/-! ### The maximum principle along a line -/

/-- **One-dimensional maximum principle**: if `q` has derivative `q' t` near `0`, `q'` has
derivative `q₂` at `0`, and `q` has a local maximum at `0`, then `q'(0) = 0` and `q₂ ≤ 0`. -/
theorem deriv_eq_zero_and_second_nonpos_of_isLocalMax {q q' : ℝ → ℝ} {q₂ : ℝ}
    (hq : ∀ᶠ t in 𝓝 0, HasDerivAt q (q' t) t) (hq' : HasDerivAt q' q₂ 0)
    (hmax : IsLocalMax q 0) : q' 0 = 0 ∧ q₂ ≤ 0 := by
  have h0 : q' 0 = 0 := hmax.hasDerivAt_eq_zero hq.self_of_nhds
  refine ⟨h0, ?_⟩
  by_contra hpos
  push Not at hpos
  -- `deriv q` agrees with `q'` near `0`
  have hdq : deriv q =ᶠ[𝓝 0] q' := hq.mono fun t ht => ht.deriv
  have hdd : deriv (deriv q) 0 = q₂ := (hq'.congr_of_eventuallyEq hdq).deriv
  have hd0 : deriv q 0 = 0 := by rw [hdq.eq_of_nhds, h0]
  have hmin : IsLocalMin q 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [hdd]; exact hpos) hd0
      hq.self_of_nhds.continuousAt
  -- `q` is constant near `0`, so `q' = 0` near `0` and `q₂ = 0`
  have hconst : ∀ᶠ t in 𝓝 0, q t = q 0 :=
    (hmax.and hmin).mono fun t ht => le_antisymm ht.1 ht.2
  have hq'0 : q' =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventually_nhds, hq] with t ht htd
    have hc : HasDerivAt q 0 t :=
      (hasDerivAt_const t (q 0)).congr_of_eventuallyEq (ht.mono fun s hs => hs)
    exact htd.unique hc
  have h2 : HasDerivAt q' 0 0 := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hq'0
  have := hq'.unique h2
  linarith

/-- **Second derivative of a logarithm**: if `r` has derivative `r' t` near `0`, `r'` has
derivative `r₂` at `0` and `r 0 > 0`, then `log ∘ r` has derivative `r' t / r t` near `0`, and
`t ↦ r' t / r t` has derivative `r₂ / r 0 - r'(0)² / r(0)²` at `0`. -/
theorem hasDerivAt_log_comp_second {r r' : ℝ → ℝ} {r₂ : ℝ}
    (hr : ∀ᶠ t in 𝓝 0, HasDerivAt r (r' t) t) (hr' : HasDerivAt r' r₂ 0) (hr0 : 0 < r 0) :
    (∀ᶠ t in 𝓝 0, HasDerivAt (fun t => Real.log (r t)) (r' t / r t) t) ∧
      HasDerivAt (fun t => r' t / r t) (r₂ / r 0 - r' 0 ^ 2 / r 0 ^ 2) 0 := by
  have hcont : ContinuousAt r 0 := hr.self_of_nhds.continuousAt
  have hpos : ∀ᶠ t in 𝓝 0, 0 < r t := hcont.eventually (lt_mem_nhds hr0)
  refine ⟨(hr.and hpos).mono fun t ht => ?_, ?_⟩
  · have := ht.1.log ht.2.ne'
    simpa [div_eq_mul_inv, mul_comm] using this
  · have h := hr'.div hr.self_of_nhds hr0.ne'
    refine h.congr_deriv ?_
    field_simp

/-! ### The Rayleigh quotient with a variable metric -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **The Rayleigh barrier with a variable metric** (FPT `lem:penalized-real-hessian`, Step 3).
Let `t ↦ M t` (the perturbed Hessian along a line) have derivative `M' t` near `0`, `M'` have
derivative `M₂` at `0`, with `M 0` and `M' 0` symmetric; let `t ↦ G t` (the metric along the line)
have derivative `G' t` near `0` and `G'` derivative `G₂` at `0`, with `G 0 = 1` and `G' 0 = 0`
(normal coordinates).  Let `(bᵢ)` be an orthonormal eigenbasis of `M 0` with eigenvalues `λᵢ` and
`λᵢ < λ_{i₁}` for `i ≠ i₁`, and put `w = Σ_{i ≠ i₁} ⟪M'(0) b_{i₁}, bᵢ⟫ / (λ_{i₁} - λᵢ) • bᵢ`.  Then
`r(t) = ⟪M t (b + t w), b + t w⟫ / ⟪G t (b + t w), b + t w⟫` (`b = b_{i₁}`) satisfies `r 0 = λ_{i₁}`,
has a derivative `r'` near `0` with `r' 0 = ⟪M' 0 b, b⟫`, and
`r''(0) = ⟪M₂ b, b⟫ + 2 Σ_{i ≠ i₁} ⟪M' 0 b, bᵢ⟫² / (λ_{i₁} - λᵢ) - λ_{i₁} ⟪G₂ b, b⟫`. -/
theorem rayleigh_quotient_metric {M M' G G' : ℝ → V →L[ℝ] V} {M₂ G₂ : V →L[ℝ] V}
    (hM : ∀ᶠ t in 𝓝 0, HasDerivAt M (M' t) t) (hM' : HasDerivAt M' M₂ 0)
    (hG : ∀ᶠ t in 𝓝 0, HasDerivAt G (G' t) t) (hG' : HasDerivAt G' G₂ 0)
    (hG0 : G 0 = 1) (hG'0 : G' 0 = 0)
    (hsym₀ : ∀ x z, ⟪M 0 x, z⟫ = ⟪x, M 0 z⟫) (hsym₁ : ∀ x z, ⟪M' 0 x, z⟫ = ⟪x, M' 0 z⟫)
    (b : OrthonormalBasis ι ℝ V) (lam : ι → ℝ) (hb : ∀ i, M 0 (b i) = lam i • b i) (i₁ : ι)
    (hgap : ∀ i, i ≠ i₁ → lam i < lam i₁) :
    let w : V := ∑ i ∈ Finset.univ.erase i₁, (⟪M' 0 (b i₁), b i⟫ / (lam i₁ - lam i)) • b i
    let r : ℝ → ℝ := fun t =>
      ⟪M t (b i₁ + t • w), b i₁ + t • w⟫ / ⟪G t (b i₁ + t • w), b i₁ + t • w⟫
    r 0 = lam i₁ ∧ ∃ r' : ℝ → ℝ, (∀ᶠ t in 𝓝 0, HasDerivAt r (r' t) t) ∧
      r' 0 = ⟪M' 0 (b i₁), b i₁⟫ ∧
      HasDerivAt r' (⟪M₂ (b i₁), b i₁⟫ + 2 * ∑ i ∈ Finset.univ.erase i₁,
        ⟪M' 0 (b i₁), b i⟫ ^ 2 / (lam i₁ - lam i) - lam i₁ * ⟪G₂ (b i₁), b i₁⟫) 0 := by
  intro w r
  set b₁ := b i₁ with hb₁
  set m : ι → ℝ := fun i => ⟪M' 0 b₁, b i⟫
  set S : ℝ := ∑ i ∈ Finset.univ.erase i₁, m i ^ 2 / (lam i₁ - lam i)
  -- `w` in the eigenbasis
  set c : ι → ℝ := fun i => if i = i₁ then 0 else m i / (lam i₁ - lam i)
  have hwc : w = ∑ i, c i • b i := by
    simp only [w, c]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₁)]
    simp only [if_true, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  have hb1n : ⟪b₁, b₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i₁, one_pow]
  have hwb : ⟪b₁, w⟫ = 0 := by
    rw [hwc, hb₁, b.orthonormal.inner_right_fintype]; simp [c]
  have hbw : ⟪w, b₁⟫ = 0 := by rw [real_inner_comm, hwb]
  have hcm : ∀ i, c i * (lam i₁ - lam i) = if i = i₁ then 0 else m i := by
    intro i
    by_cases hi : i = i₁
    · simp [c, hi]
    · have : lam i₁ - lam i ≠ 0 := sub_ne_zero.mpr (hgap i hi).ne'
      simp only [c, hi, if_false]
      field_simp
  have hS : ⟪M' 0 b₁, w⟫ = S := by
    rw [hwc, inner_sum]
    simp only [inner_smul_right]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₁)]
    simp only [c, if_true, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
    simp only [m]
    ring
  have hMw : M 0 w = ∑ i, (c i * lam i) • b i := by
    simp only [hwc, map_sum, map_smul, hb, smul_smul]
  have hMww : ⟪M 0 w, w⟫ - lam i₁ * ⟪w, w⟫ = -S := by
    have hww : ⟪w, w⟫ = ∑ i, c i * c i := by
      rw [hwc, b.orthonormal.inner_sum]; simp only [starRingEnd_apply, star_trivial]
    have hmw : ⟪M 0 w, w⟫ = ∑ i, c i * lam i * c i := by
      rw [hMw, hwc, b.orthonormal.inner_sum]; simp only [starRingEnd_apply, star_trivial]
    rw [hmw, hww, Finset.mul_sum, ← Finset.sum_sub_distrib, ← hS, hwc, inner_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_smul_right]
    have h := hcm i
    by_cases hi : i = i₁
    · simp [c, hi]
    · rw [if_neg hi] at h
      simp only [m] at h
      rw [← h]
      ring
  have hMb : M 0 b₁ = lam i₁ • b₁ := hb i₁
  have hN0 : ⟪M 0 b₁, b₁⟫ = lam i₁ := by rw [hMb, inner_smul_left, hb1n]; simp
  -- the curve `b + t w`
  set yv : ℝ → V := fun t => b₁ + t • w
  have hyv : ∀ t, HasDerivAt yv w t := fun t => by
    have h := HasDerivAt.const_add b₁ (HasDerivAt.smul_const (hasDerivAt_id t) w)
    simpa [yv] using h
  have hyv0 : yv 0 = b₁ := by simp [yv]
  set Nf : ℝ → ℝ := fun t => ⟪M t (yv t), yv t⟫
  set Df : ℝ → ℝ := fun t => ⟪G t (yv t), yv t⟫
  have hr : r = fun t => Nf t / Df t := rfl
  -- first derivatives
  set N' : ℝ → ℝ := fun t => ⟪M t (yv t), w⟫ + ⟪M' t (yv t) + M t w, yv t⟫
  set D' : ℝ → ℝ := fun t => ⟪G t (yv t), w⟫ + ⟪G' t (yv t) + G t w, yv t⟫
  have hNd : ∀ᶠ t in 𝓝 0, HasDerivAt Nf (N' t) t := hM.mono fun t ht =>
    HasDerivAt.inner ℝ (HasDerivAt.clm_apply ht (hyv t)) (hyv t)
  have hDd : ∀ᶠ t in 𝓝 0, HasDerivAt Df (D' t) t := hG.mono fun t ht =>
    HasDerivAt.inner ℝ (HasDerivAt.clm_apply ht (hyv t)) (hyv t)
  have vD0 : Df 0 = 1 := by simp only [Df, hyv0, hG0, one_apply_eq_self, hb1n]
  have vD'0 : D' 0 = 0 := by
    simp only [D', hyv0, hG0, hG'0, one_apply_eq_self,
      zero_apply, zero_add, hwb, hbw, add_zero]
  have vN0 : Nf 0 = lam i₁ := by simp only [Nf, hyv0, hN0]
  have vN'0 : N' 0 = ⟪M' 0 b₁, b₁⟫ := by
    simp only [N', hyv0]
    rw [hMb, inner_smul_left, hwb, inner_add_left, hsym₀ w b₁, hMb, inner_smul_right, hbw]
    simp
  have hDpos : ∀ᶠ t in 𝓝 0, 0 < Df t :=
    hDd.self_of_nhds.continuousAt.eventually (lt_mem_nhds (by rw [vD0]; exact one_pos))
  refine ⟨?_, fun t => (N' t * Df t - Nf t * D' t) / Df t ^ 2, ?_, ?_, ?_⟩
  · show Nf 0 / Df 0 = lam i₁
    rw [vN0, vD0, div_one]
  · rw [hr]
    exact ((hNd.and hDd).and hDpos).mono fun t ht =>
      HasDerivAt.fun_div ht.1.1 ht.1.2 ht.2.ne'
  · simp only [vN'0, vD0, vN0, vD'0]
    ring
  · -- second derivative at `0`
    have hM0 : HasDerivAt M (M' 0) 0 := hM.self_of_nhds
    have hG0d : HasDerivAt G (G' 0) 0 := hG.self_of_nhds
    have hw0 : HasDerivAt (fun _ : ℝ => w) 0 0 := hasDerivAt_const 0 w
    have hN'd : HasDerivAt N'
        ((⟪M 0 (yv 0), 0⟫ + ⟪M' 0 (yv 0) + M 0 w, w⟫) +
          (⟪M' 0 (yv 0) + M 0 w, w⟫ + ⟪(M₂ (yv 0) + M' 0 w) + (M' 0 w + M 0 0), yv 0⟫)) 0 :=
      HasDerivAt.add (HasDerivAt.inner ℝ (HasDerivAt.clm_apply hM0 (hyv 0)) hw0)
        (HasDerivAt.inner ℝ (HasDerivAt.add (HasDerivAt.clm_apply hM' (hyv 0))
          (HasDerivAt.clm_apply hM0 hw0)) (hyv 0))
    have hD'd : HasDerivAt D'
        ((⟪G 0 (yv 0), 0⟫ + ⟪G' 0 (yv 0) + G 0 w, w⟫) +
          (⟪G' 0 (yv 0) + G 0 w, w⟫ + ⟪(G₂ (yv 0) + G' 0 w) + (G' 0 w + G 0 0), yv 0⟫)) 0 :=
      HasDerivAt.add (HasDerivAt.inner ℝ (HasDerivAt.clm_apply hG0d (hyv 0)) hw0)
        (HasDerivAt.inner ℝ (HasDerivAt.add (HasDerivAt.clm_apply hG' (hyv 0))
          (HasDerivAt.clm_apply hG0d hw0)) (hyv 0))
    have hq := HasDerivAt.fun_div (HasDerivAt.fun_sub (HasDerivAt.fun_mul hN'd hDd.self_of_nhds)
      (HasDerivAt.fun_mul hNd.self_of_nhds hD'd)) (HasDerivAt.fun_pow hDd.self_of_nhds 2)
      (pow_ne_zero 2 hDpos.self_of_nhds.ne')
    refine HasDerivAt.congr_deriv hq ?_
    rw [vD0, vD'0, vN0, vN'0, hyv0]
    have hsw : ⟪M' 0 w, b₁⟫ = S := by rw [hsym₁, real_inner_comm, hS]
    simp only [hG0, hG'0, one_apply_eq_self, zero_apply,
      inner_add_left, inner_zero_right, map_zero, hsw, hS, zero_add, add_zero]
    have := hMww
    field_simp
    linarith

/-- The barrier lies below the supremum of the Rayleigh quotients: for a positive form `G` and
`Y ≠ 0`, `⟪M Y, Y⟫ / ⟪G Y, Y⟫ ≤ λ` whenever `⟪M y, y⟫ ≤ λ ⟪G y, y⟫` for all `y`. -/
theorem rayleigh_le_of_forall {M G : V →L[ℝ] V} {lam : ℝ} {Y : V} (hY : 0 < ⟪G Y, Y⟫)
    (h : ∀ y, ⟪M y, y⟫ ≤ lam * ⟪G y, y⟫) : ⟪M Y, Y⟫ / ⟪G Y, Y⟫ ≤ lam := by
  rw [div_le_iff₀ hY]
  exact h Y

/-! ### Two auxiliary facts of FPT Step 2 -/

/-- **The gradient weight** (FPT `eq:real-hessian-gradient-weight`): for `0 < τ ≤ 1` and
`s ∈ [0, S]`, the function `η(x) = -(τ/2) log(1 + S - x)` has derivative `η' = (τ/2)/(1 + S - s)`
and second derivative `η'' = (τ/2)/(1 + S - s)²` at `s`, with `τ/(2(1 + S)) ≤ η' ≤ τ/2` and
`η'' = 2η'²/τ ≥ 2η'²`. -/
theorem gradient_weight {τ S s : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    HasDerivAt (fun x => -(τ / 2) * Real.log (1 + S - x)) (τ / 2 / (1 + S - s)) s ∧
      HasDerivAt (fun x => τ / 2 / (1 + S - x)) (τ / 2 / (1 + S - s) ^ 2) s ∧
      τ / (2 * (1 + S)) ≤ τ / 2 / (1 + S - s) ∧ τ / 2 / (1 + S - s) ≤ τ / 2 ∧
      τ / 2 / (1 + S - s) ^ 2 = 2 * (τ / 2 / (1 + S - s)) ^ 2 / τ ∧
      2 * (τ / 2 / (1 + S - s)) ^ 2 ≤ τ / 2 / (1 + S - s) ^ 2 := by
  have hpos : 0 < 1 + S - s := by linarith
  have hlin : HasDerivAt (fun x : ℝ => 1 + S - x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 + S)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (hlin.log hpos.ne').const_mul (-(τ / 2))
    refine h.congr_deriv ?_
    field_simp
  · have h := (hlin.inv hpos.ne').const_mul (τ / 2)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
    · simp [div_eq_mul_inv]
    · field_simp
  · have hS0 : 0 ≤ S := hs0.trans hsS
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  · rw [div_le_iff₀ hpos]
    nlinarith
  · field_simp
  · have h1 : τ / 2 / (1 + S - s) ^ 2 = 2 * (τ / 2 / (1 + S - s)) ^ 2 / τ := by field_simp
    rw [h1, le_div_iff₀ hτ0]
    have : 0 ≤ 2 * (τ / 2 / (1 + S - s)) ^ 2 := by positivity
    nlinarith

/-- **Reduction to the largest eigenvalue** (FPT Step 2): if finitely many reals `μ_j` (`m` of
them) satisfy `μ_j ≤ ℓ` and `Σ_j μ_j ≥ -c`, then `|μ_j| ≤ max c 0 + m · max ℓ 0` for every `j`.
(Applied to the eigenvalues of `∇²a`, whose sum is `4 D_k a ≥ -4n` or `2 D_k a ≥ -2n` depending on
the normalization of `g₀`.) -/
theorem abs_le_of_sum_ge_of_le {κ : Type*} [Fintype κ] (μ : κ → ℝ) {ℓ c : ℝ}
    (hle : ∀ j, μ j ≤ ℓ) (hsum : -c ≤ ∑ j, μ j) (j : κ) :
    |μ j| ≤ max c 0 + Fintype.card κ * max ℓ 0 := by
  classical
  have hmax : ∀ k, μ k ≤ max ℓ 0 := fun k => (hle k).trans (le_max_left _ _)
  have hℓ0 : 0 ≤ max ℓ 0 := le_max_right _ _
  have hrest : ∑ k ∈ Finset.univ.erase j, μ k ≤ (Fintype.card κ - 1 : ℝ) * max ℓ 0 := by
    calc ∑ k ∈ Finset.univ.erase j, μ k ≤ ∑ _k ∈ Finset.univ.erase j, max ℓ 0 :=
          Finset.sum_le_sum fun k _ => hmax k
      _ = ((Finset.univ.erase j).card : ℝ) * max ℓ 0 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Fintype.card κ - 1 : ℝ) * max ℓ 0 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨j⟩), Nat.cast_one]
  have hsplit : ∑ k, μ k = μ j + ∑ k ∈ Finset.univ.erase j, μ k :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hc : c ≤ max c 0 := le_max_left _ _
  rw [abs_le]
  constructor
  · nlinarith
  · have : μ j ≤ max ℓ 0 := hmax j
    have : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
    nlinarith [le_max_right c 0]

end SGPT.Envelopes.TosC11b
