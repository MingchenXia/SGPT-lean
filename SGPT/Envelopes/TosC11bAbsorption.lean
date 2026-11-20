import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# The real-Hessian maximum principle: the inequality at the maximum point and the absorption of
the third-order term

Lane TOS-C11b (`claude-tos-c11b`, nodes `tos-c11b:max-inequality`, `tos-c11b:absorption`,
`tos-c11b:pointwise-bound`).  Source: Xia, *Foundations of pluripotential theory*,
`lem:penalized-real-hessian`, end of Step 3 (the inequality `eq:real-hessian-maximum`) and Step 4
(`eq:real-hessian-third-splitting`, `eq:real-hessian-third-absorption`), after Chu–Tosatti–Weinkove
(arXiv version of CTW17, Lemmas 2.1–2.2) and Tosatti 2018.  This is the core of the `C^{1,1}`
estimate behind SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

At the maximum point `x₀` of `Q = log λ₁ + η(|∂a|²) - A a` (in Kähler normal coordinates in which
`G = (k_{iȷ̄} + a_{iȷ̄})` is diagonal with entries `rᵢ > 0`) FPT considers the nonnegative quantities

* `U = 2 Σ_{i, α>1} |∂ᵢ a_{V_α V₁}|² / (rᵢ λ (λ - λ_α))`,
* `R = Σ_{p,q} |V₁ G_{p q̄}|² / (r_p r_q λ)`,
* `N = Σᵢ |∂ᵢ a_{V₁ V₁}|² / (rᵢ λ²)`,
* `T = Σᵢ rᵢ⁻¹`,

and the whole difficulty is the negative third-order term `-N`.  Everything in Steps 3–4 after
the differential identities have been computed is elementary algebra on finitely many real and
complex numbers; this file proves that algebra, with all constants explicit.

* `norm_add_sq_le_weighted`, `norm_sum_mul_sq_le` — `|b + c|² ≤ (1 + t)|b|² + (1 + t⁻¹)|c|²` and the
  weighted Cauchy–Schwarz inequality `|Σ wᵢ zᵢ|² ≤ (Σ dᵢ |wᵢ|²)(Σ |zᵢ|²/dᵢ)`.
* `max_inequality_of_components` — **end of Step 3**: the lower bounds for `D_G log λ₁`, `D_G s`, the
  identity `D_G a = n - T` and `D_G Q ≤ 0` give `eq:real-hessian-maximum`.
* `third_order_absorption` — **Step 4**: from the splitting
  `∂ᵢa_{V₁V₁} = √2 Σ_q ν̄_q V₁G_{iq̄} - i Σ_{α>1} μ_α ∂ᵢa_{V₁V_α} + Eᵢ`, the positivity bound
  `λ - Σ λ_α μ_α² ≤ 2λ + c₃` (from `G(W, W̄) > 0`; `c₃ = 3` in FPT) and the critical point equation
  `∂ᵢa_{V₁V₁}/λ = A aᵢ - η' sᵢ`, for `0 < ε < 1/2` and `λ` above explicit thresholds,
  `N ≤ U + R + T + 4εA² Σ|aᵢ|²/rᵢ + 2η'² Σ|sᵢ|²/rᵢ`  (`eq:real-hessian-third-absorption`).
* `eta_K_add_T_le` — the conclusion of Step 4: with `A ≥ C₀ + 3`, `η'' ≥ 2η'²` and
  `4εA² Σ|aᵢ|²/rᵢ ≤ T`, the inequality at the maximum point becomes `η' K + T ≤ A n`.
* `four_eps_mul_sum_le` — the choice `ε = (4A²(S + 1))⁻¹` gives `4εA² Σ|aᵢ|²/rᵢ ≤ T` when
  `Σ|aᵢ|² ≤ S`.
-/

set_option autoImplicit false

noncomputable section

open Finset Complex
open scoped ComplexConjugate

namespace SGPT.Envelopes.TosC11b

/-! ### Two elementary inequalities -/

/-- `‖b + c‖² ≤ (1 + t)‖b‖² + (1 + t⁻¹)‖c‖²` for `t > 0`. -/
theorem norm_add_sq_le_weighted {E : Type*} [SeminormedAddCommGroup E] (b c : E) {t : ℝ}
    (ht : 0 < t) : ‖b + c‖ ^ 2 ≤ (1 + t) * ‖b‖ ^ 2 + (1 + t⁻¹) * ‖c‖ ^ 2 := by
  have h1 : ‖b + c‖ ≤ ‖b‖ + ‖c‖ := norm_add_le b c
  have hx := norm_nonneg b
  have hy := norm_nonneg c
  have h2 : ‖b + c‖ ^ 2 ≤ (‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : 2 * ‖b‖ * ‖c‖ ≤ t * ‖b‖ ^ 2 + t⁻¹ * ‖c‖ ^ 2 := by
    have h0 : 0 ≤ (t * ‖b‖ - ‖c‖) ^ 2 / t := by positivity
    have e : (t * ‖b‖ - ‖c‖) ^ 2 / t = t * ‖b‖ ^ 2 + t⁻¹ * ‖c‖ ^ 2 - 2 * ‖b‖ * ‖c‖ := by
      field_simp
      ring
    linarith
  nlinarith

/-- **Weighted Cauchy–Schwarz**: `‖Σ wᵢ zᵢ‖² ≤ (Σ dᵢ ‖wᵢ‖²)(Σ ‖zᵢ‖²/dᵢ)` for weights `dᵢ > 0`. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (w z : ι → ℂ) (d : ι → ℝ)
    (hd : ∀ i ∈ s, 0 < d i) :
    ‖∑ i ∈ s, w i * z i‖ ^ 2 ≤ (∑ i ∈ s, d i * ‖w i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 / d i := by
  have h1 : ‖∑ i ∈ s, w i * z i‖ ≤ ∑ i ∈ s, ‖w i‖ * ‖z i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 : (∑ i ∈ s, ‖w i‖ * ‖z i‖) ^ 2 ≤
      (∑ i ∈ s, d i * ‖w i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 / d i := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i hi => ?_) (fun i hi => ?_)
      (fun i hi => le_of_eq ?_)
    · have := hd i hi; positivity
    · have := hd i hi; positivity
    · have := (hd i hi).ne'
      field_simp
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-! ### The inequality at the maximum point (end of Step 3) -/

/-- **End of FPT Step 3** (`eq:real-hessian-maximum`).  At the maximum point, write
`DGQ = D_G log λ₁ + η' D_G s + η'' Σ|sᵢ|²/rᵢ - A D_G a ≤ 0`.  If
`D_G log λ₁ ≥ U + R - N - C₁T + β/2`, `D_G s ≥ K - C₂T + βs - β|∂f|²`, `D_G a = n - T`,
`0 ≤ η' ≤ 1/2`, `η'|∂f|² ≤ 1/4` and `β ≥ 0`, then
`0 ≥ U + R - N + η'K + η''Σ|sᵢ|²/rᵢ + (A - C₀)T - An + βη's + β/4` with `C₀ = C₁ + C₂/2`. -/
theorem max_inequality_of_components {DGlog DGs DGa U R N K T C₁ C₂ β s f2 η' η'' S2 A n : ℝ}
    (hQ : DGlog + η' * DGs + η'' * S2 - A * DGa ≤ 0)
    (hlog : U + R - N - C₁ * T + β / 2 ≤ DGlog)
    (hs : K - C₂ * T + β * s - β * f2 ≤ DGs)
    (ha : DGa = n - T) (hη0 : 0 ≤ η') (hη1 : η' ≤ 1 / 2) (hηf : η' * f2 ≤ 1 / 4)
    (hβ : 0 ≤ β) (hT : 0 ≤ T) (hC₂ : 0 ≤ C₂) :
    U + R - N + η' * K + η'' * S2 + (A - (C₁ + C₂ / 2)) * T - A * n + β * η' * s + β / 4 ≤ 0 := by
  have hA : A * DGa = A * n - A * T := by rw [ha]; ring
  have h1 : η' * K - η' * (C₂ * T) + β * η' * s - β * (η' * f2) ≤ η' * DGs := by
    have := mul_le_mul_of_nonneg_left hs hη0
    have e : η' * (K - C₂ * T + β * s - β * f2) =
        η' * K - η' * (C₂ * T) + β * η' * s - β * (η' * f2) := by ring
    linarith
  have h2 : η' * (C₂ * T) ≤ C₂ / 2 * T := by
    have : η' * (C₂ * T) ≤ 1 / 2 * (C₂ * T) := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hC₂ hT)
    linarith
  have hβf : β * (η' * f2) ≤ β * (1 / 4) := mul_le_mul_of_nonneg_left hηf hβ
  have e2 : (A - (C₁ + C₂ / 2)) * T = A * T - C₁ * T - C₂ / 2 * T := by ring
  rw [e2]
  linarith

/-! ### The absorption of the third-order term (Step 4) -/

section Absorption

variable {n : ℕ} {ι : Type*}

/-- The per-index estimate behind `third_order_absorption`: for `X = P + Q + E` with
`0 < ε < 1/2` and `X = λ (A a - η' s)`,
`‖X‖² ≤ ε⁻¹‖P‖² + (1 - ε²)‖Q‖² + ε⁻¹‖E‖² + 4ελ²(A²‖a‖² + η'²‖s‖²)`. -/
theorem norm_sq_le_split {X P Q E a s : ℂ} {lam A η' ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hX : X = P + Q + E) (hcrit : X = lam * (A * a - η' * s)) :
    ‖X‖ ^ 2 ≤ ε⁻¹ * ‖P‖ ^ 2 + (1 - ε ^ 2) * ‖Q‖ ^ 2 + ε⁻¹ * ‖E‖ ^ 2 +
      4 * ε * lam ^ 2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2) := by
  have h12 : 0 < 1 - 2 * ε := by linarith
  set t := ε / (1 - 2 * ε) with ht
  have htpos : 0 < t := div_pos hε0 h12
  -- separate `E`
  have hA := norm_add_sq_le_weighted (P + Q) E htpos
  rw [← hX] at hA
  have hA' : (1 - 2 * ε) * ‖X‖ ^ 2 ≤ (1 - ε) * ‖P + Q‖ ^ 2 + ε⁻¹ * ‖E‖ ^ 2 := by
    have e1 : (1 - 2 * ε) * (1 + t) = 1 - ε := by rw [ht]; field_simp; ring
    have e2 : (1 - 2 * ε) * (1 + t⁻¹) ≤ ε⁻¹ := by
      rw [ht, inv_div]
      rw [show (1 - 2 * ε) * (1 + (1 - 2 * ε) / ε) = (1 - 2 * ε) * (1 - ε) / ε by
        field_simp; ring]
      rw [div_le_iff₀ hε0, inv_mul_cancel₀ hε0.ne']
      nlinarith
    have hE0 := sq_nonneg ‖E‖
    calc (1 - 2 * ε) * ‖X‖ ^ 2
        ≤ (1 - 2 * ε) * ((1 + t) * ‖P + Q‖ ^ 2 + (1 + t⁻¹) * ‖E‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hA h12.le
      _ = (1 - ε) * ‖P + Q‖ ^ 2 + (1 - 2 * ε) * (1 + t⁻¹) * ‖E‖ ^ 2 := by rw [← e1]; ring
      _ ≤ (1 - ε) * ‖P + Q‖ ^ 2 + ε⁻¹ * ‖E‖ ^ 2 := by gcongr
  -- separate `P` from `Q`
  have hB := norm_add_sq_le_weighted Q P hε0
  rw [add_comm Q P] at hB
  have hB' : (1 - ε) * ‖P + Q‖ ^ 2 ≤ ε⁻¹ * ‖P‖ ^ 2 + (1 - ε ^ 2) * ‖Q‖ ^ 2 := by
    have h1ε : 0 ≤ 1 - ε := by linarith
    have e3 : (1 - ε) * (1 + ε⁻¹) ≤ ε⁻¹ := by
      rw [mul_add, mul_one]
      have : (1 - ε) * ε⁻¹ = ε⁻¹ - 1 := by field_simp
      rw [this]; linarith
    have hP0 := sq_nonneg ‖P‖
    calc (1 - ε) * ‖P + Q‖ ^ 2 ≤ (1 - ε) * ((1 + ε) * ‖Q‖ ^ 2 + (1 + ε⁻¹) * ‖P‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hB h1ε
      _ = (1 - ε) * (1 + ε⁻¹) * ‖P‖ ^ 2 + (1 - ε ^ 2) * ‖Q‖ ^ 2 := by ring
      _ ≤ ε⁻¹ * ‖P‖ ^ 2 + (1 - ε ^ 2) * ‖Q‖ ^ 2 := by gcongr
  -- the critical point equation for the remaining `2ε‖X‖²`
  have hC : ‖X‖ ^ 2 ≤ 2 * lam ^ 2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2) := by
    have h0 : ‖X‖ = |lam| * ‖(A : ℂ) * a - (η' : ℂ) * s‖ := by
      rw [hcrit, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖(A : ℂ) * a - (η' : ℂ) * s‖ ≤ |A| * ‖a‖ + |η'| * ‖s‖ := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    have h2 : (|A| * ‖a‖ + |η'| * ‖s‖) ^ 2 ≤ 2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2) := by
      have := sq_nonneg (|A| * ‖a‖ - |η'| * ‖s‖)
      have hA2 : |A| ^ 2 = A ^ 2 := sq_abs A
      have hη2 : |η'| ^ 2 = η' ^ 2 := sq_abs η'
      nlinarith
    have h3 : ‖(A : ℂ) * a - (η' : ℂ) * s‖ ^ 2 ≤ 2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2) :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    rw [h0, mul_pow, sq_abs]
    calc lam ^ 2 * ‖(A : ℂ) * a - (η' : ℂ) * s‖ ^ 2
        ≤ lam ^ 2 * (2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg lam)
      _ = _ := by ring
  have hC' : 2 * ε * ‖X‖ ^ 2 ≤ 4 * ε * lam ^ 2 * (A ^ 2 * ‖a‖ ^ 2 + η' ^ 2 * ‖s‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 2 * ε)
    linarith
  linarith

/-- **FPT Step 4: absorption of the third-order term** (`eq:real-hessian-third-absorption`).

Data at the maximum point: `rᵢ > 0` (the eigenvalues of `G`, `i : Fin n`), `λ > 0`, eigenvalues
`λ_α < λ` for the other indices `α ∈ s`, and complex numbers `Xᵢ = ∂ᵢa_{V₁V₁}`,
`Y i α = ∂ᵢa_{V₁V_α}`, `Z i q = V₁G_{iq̄}`, the coefficients `ν_q` of `W = (V₁ - iJV₁)/√2` and the
real coefficients `μ_α` of `JV₁`, the error `Eᵢ`, and `aᵢ`, `sᵢ` (the first derivatives of `a` and of
`s = |∂a|²_k`).  Assume

* the splitting `Xᵢ = √2 Σ_q ν̄_q Z i q - i Σ_α μ_α Y i α + Eᵢ` (`eq:real-hessian-third-splitting`),
  with `‖Eᵢ‖ ≤ C_E`;
* `Σ_α μ_α² = 1` and the positivity bound `λ - Σ_α λ_α μ_α² ≤ 2λ + c₃` (`c₃ = 3` in FPT's
  normalization `g₀ = 2 Re(k_{iȷ̄} dzᵢ ⊗ dz̄ⱼ)`; any `c₃ ≥ 0` is allowed);
* `Σ_q r_q ‖ν_q‖² ≤ C_ν`;
* the critical point equation `Xᵢ / λ = A aᵢ - η' sᵢ`;
* `0 < ε < 1/2` and the thresholds `C_E² ≤ ελ²`, `2C_ν ≤ ελ`, `c₃ ≤ 2ε²λ`.

Then `N ≤ U + R + T + 4εA² Σᵢ ‖aᵢ‖²/rᵢ + 2η'² Σᵢ ‖sᵢ‖²/rᵢ`. -/
theorem third_order_absorption (s : Finset ι) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) {lam : ℝ}
    (hlam : 0 < lam) (lamα : ι → ℝ) (hgap : ∀ α ∈ s, lamα α < lam)
    (X : Fin n → ℂ) (Y : Fin n → ι → ℂ) (Z : Fin n → Fin n → ℂ) (ν : Fin n → ℂ) (μ : ι → ℝ)
    (E : Fin n → ℂ)
    (hsplit : ∀ i, X i = (Real.sqrt 2 : ℂ) * ∑ q, conj (ν q) * Z i q -
      I * ∑ α ∈ s, (μ α : ℂ) * Y i α + E i)
    (hμ : ∑ α ∈ s, μ α ^ 2 = 1) {c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hpos : lam - ∑ α ∈ s, lamα α * μ α ^ 2 ≤ 2 * lam + c₃)
    {Cν CE : ℝ} (hν : ∑ q, r q * ‖ν q‖ ^ 2 ≤ Cν) (hE : ∀ i, ‖E i‖ ≤ CE)
    {A η' : ℝ} (a sg : Fin n → ℂ) (hcrit : ∀ i, X i / lam = A * a i - η' * sg i)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hthE : CE ^ 2 ≤ ε * lam ^ 2) (hthν : 2 * Cν ≤ ε * lam) (hthU : c₃ ≤ 2 * ε ^ 2 * lam) :
    ∑ i, ‖X i‖ ^ 2 / (r i * lam ^ 2) ≤
      2 * ∑ i, ∑ α ∈ s, ‖Y i α‖ ^ 2 / (r i * lam * (lam - lamα α)) +
      ∑ p, ∑ q, ‖Z p q‖ ^ 2 / (r p * r q * lam) + ∑ i, (r i)⁻¹ +
      4 * ε * A ^ 2 * ∑ i, ‖a i‖ ^ 2 / r i + 2 * η' ^ 2 * ∑ i, ‖sg i‖ ^ 2 / r i := by
  have hd : ∀ α ∈ s, 0 < lam - lamα α := fun α hα => sub_pos.mpr (hgap α hα)
  -- the weight sums
  set zq : Fin n → ℝ := fun i => ∑ q, ‖Z i q‖ ^ 2 / r q with hzq
  set yq : Fin n → ℝ := fun i => ∑ α ∈ s, ‖Y i α‖ ^ 2 / (lam - lamα α) with hyq
  have hzq0 : ∀ i, 0 ≤ zq i := fun i =>
    Finset.sum_nonneg fun q _ => by have := hr q; positivity
  have hyq0 : ∀ i, 0 ≤ yq i := fun i =>
    Finset.sum_nonneg fun α hα => by have := hd α hα; positivity
  have hCν0 : 0 ≤ Cν := (Finset.sum_nonneg fun q _ => by have := hr q; positivity).trans hν
  have hμw : ∑ α ∈ s, (lam - lamα α) * ‖(μ α : ℂ)‖ ^ 2 ≤ 2 * lam + c₃ := by
    have : ∑ α ∈ s, (lam - lamα α) * ‖(μ α : ℂ)‖ ^ 2 = lam - ∑ α ∈ s, lamα α * μ α ^ 2 := by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hμ, mul_one]
    rw [this]; exact hpos
  -- the per-index estimate
  have hper : ∀ i, ‖X i‖ ^ 2 ≤ lam * zq i + 2 * lam * yq i + lam ^ 2 +
      4 * ε * lam ^ 2 * A ^ 2 * ‖a i‖ ^ 2 + 2 * lam ^ 2 * η' ^ 2 * ‖sg i‖ ^ 2 := by
    intro i
    set P : ℂ := (Real.sqrt 2 : ℂ) * ∑ q, conj (ν q) * Z i q
    set Q : ℂ := -(I * ∑ α ∈ s, (μ α : ℂ) * Y i α)
    have hX : X i = P + Q + E i := by rw [hsplit i]; ring
    have hcr : X i = lam * (A * a i - η' * sg i) := by
      have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      rw [← hcrit i]; field_simp
    have h := norm_sq_le_split hε0 hε1 hX hcr
    -- bound `P`
    have hP : ‖P‖ ^ 2 ≤ 2 * Cν * zq i := by
      have h1 : ‖P‖ ^ 2 = 2 * ‖∑ q, conj (ν q) * Z i q‖ ^ 2 := by
        simp only [P, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 := norm_sum_mul_sq_le Finset.univ (fun q => conj (ν q)) (fun q => Z i q) r
        (fun q _ => hr q)
      simp only [Complex.norm_conj] at h2
      rw [h1]
      have h3 : (∑ q, r q * ‖ν q‖ ^ 2) * zq i ≤ Cν * zq i :=
        mul_le_mul_of_nonneg_right hν (hzq0 i)
      linarith
    -- bound `Q`
    have hQ : ‖Q‖ ^ 2 ≤ (2 * lam + c₃) * yq i := by
      have h1 : ‖Q‖ = ‖∑ α ∈ s, (μ α : ℂ) * Y i α‖ := by
        simp only [Q, norm_neg, norm_mul, Complex.norm_I, one_mul]
      have h2 := norm_sum_mul_sq_le s (fun α => (μ α : ℂ)) (fun α => Y i α)
        (fun α => lam - lamα α) hd
      rw [h1]
      exact h2.trans (mul_le_mul_of_nonneg_right hμw (hyq0 i))
    have hE2 : ‖E i‖ ^ 2 ≤ CE ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hE i) 2
    -- the thresholds
    have t1 : ε⁻¹ * (2 * Cν * zq i) ≤ lam * zq i := by
      have : ε⁻¹ * (2 * Cν) ≤ lam := by
        rw [inv_mul_le_iff₀ hε0]; linarith
      have := mul_le_mul_of_nonneg_right this (hzq0 i)
      linarith
    have t2 : (1 - ε ^ 2) * ((2 * lam + c₃) * yq i) ≤ 2 * lam * yq i := by
      have : (1 - ε ^ 2) * (2 * lam + c₃) ≤ 2 * lam := by nlinarith
      have := mul_le_mul_of_nonneg_right this (hyq0 i)
      linarith
    have t3 : ε⁻¹ * CE ^ 2 ≤ lam ^ 2 := by
      rw [inv_mul_le_iff₀ hε0]; linarith
    have t4 : 4 * ε * lam ^ 2 * (η' ^ 2 * ‖sg i‖ ^ 2) ≤ 2 * lam ^ 2 * η' ^ 2 * ‖sg i‖ ^ 2 := by
      have : 0 ≤ lam ^ 2 * η' ^ 2 * ‖sg i‖ ^ 2 := by positivity
      nlinarith
    have hε1' : 0 ≤ 1 - ε ^ 2 := by nlinarith
    have hεi : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε0.le
    have hPε : ε⁻¹ * ‖P‖ ^ 2 ≤ ε⁻¹ * (2 * Cν * zq i) := mul_le_mul_of_nonneg_left hP hεi
    have hQε : (1 - ε ^ 2) * ‖Q‖ ^ 2 ≤ (1 - ε ^ 2) * ((2 * lam + c₃) * yq i) :=
      mul_le_mul_of_nonneg_left hQ hε1'
    have hEε : ε⁻¹ * ‖E i‖ ^ 2 ≤ ε⁻¹ * CE ^ 2 := mul_le_mul_of_nonneg_left hE2 hεi
    nlinarith
  -- divide by `rᵢ λ²` and sum
  have hdiv : ∀ i, ‖X i‖ ^ 2 / (r i * lam ^ 2) ≤
      2 * (yq i / (r i * lam)) + zq i / (r i * lam) + (r i)⁻¹ +
      4 * ε * A ^ 2 * (‖a i‖ ^ 2 / r i) + 2 * η' ^ 2 * (‖sg i‖ ^ 2 / r i) := by
    intro i
    have hri := hr i
    rw [div_le_iff₀ (by positivity)]
    have e : (2 * (yq i / (r i * lam)) + zq i / (r i * lam) + (r i)⁻¹ +
        4 * ε * A ^ 2 * (‖a i‖ ^ 2 / r i) + 2 * η' ^ 2 * (‖sg i‖ ^ 2 / r i)) * (r i * lam ^ 2) =
        lam * zq i + 2 * lam * yq i + lam ^ 2 + 4 * ε * lam ^ 2 * A ^ 2 * ‖a i‖ ^ 2 +
          2 * lam ^ 2 * η' ^ 2 * ‖sg i‖ ^ 2 := by
      field_simp
      ring
    rw [e]
    exact hper i
  have hU : ∑ i, yq i / (r i * lam) =
      ∑ i, ∑ α ∈ s, ‖Y i α‖ ^ 2 / (r i * lam * (lam - lamα α)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq, Finset.sum_div]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [div_div, mul_comm (lam - lamα α)]
  have hR : ∑ i, zq i / (r i * lam) = ∑ p, ∑ q, ‖Z p q‖ ^ 2 / (r p * r q * lam) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hzq, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [div_div]
    ring_nf
  calc ∑ i, ‖X i‖ ^ 2 / (r i * lam ^ 2)
      ≤ ∑ i, (2 * (yq i / (r i * lam)) + zq i / (r i * lam) + (r i)⁻¹ +
          4 * ε * A ^ 2 * (‖a i‖ ^ 2 / r i) + 2 * η' ^ 2 * (‖sg i‖ ^ 2 / r i)) :=
        Finset.sum_le_sum fun i _ => hdiv i
    _ = 2 * ∑ i, yq i / (r i * lam) + ∑ i, zq i / (r i * lam) + ∑ i, (r i)⁻¹ +
          4 * ε * A ^ 2 * ∑ i, ‖a i‖ ^ 2 / r i + 2 * η' ^ 2 * ∑ i, ‖sg i‖ ^ 2 / r i := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hU, hR]

/-- The choice `ε = (4A²(S + 1))⁻¹` of FPT Step 4: if `Σᵢ ‖aᵢ‖² ≤ S`, then
`4εA² Σᵢ ‖aᵢ‖²/rᵢ ≤ T = Σᵢ rᵢ⁻¹`. -/
theorem four_eps_mul_sum_le (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (a : Fin n → ℂ) {S A : ℝ}
    (hS : ∑ i, ‖a i‖ ^ 2 ≤ S) (hA : A ≠ 0) :
    4 * (4 * A ^ 2 * (S + 1))⁻¹ * A ^ 2 * ∑ i, ‖a i‖ ^ 2 / r i ≤ ∑ i, (r i)⁻¹ := by
  have hT0 : 0 ≤ ∑ i, (r i)⁻¹ := Finset.sum_nonneg fun i _ => (inv_pos.mpr (hr i)).le
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun i _ => sq_nonneg _).trans hS
  have hle : ∀ i, (r i)⁻¹ ≤ ∑ j, (r j)⁻¹ := fun i =>
    Finset.single_le_sum (f := fun j => (r j)⁻¹) (fun j _ => (inv_pos.mpr (hr j)).le)
      (Finset.mem_univ i)
  have h1 : ∑ i, ‖a i‖ ^ 2 / r i ≤ S * ∑ i, (r i)⁻¹ := by
    calc ∑ i, ‖a i‖ ^ 2 / r i ≤ ∑ i, ‖a i‖ ^ 2 * ∑ j, (r j)⁻¹ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (hle i) (sq_nonneg _)
      _ = (∑ i, ‖a i‖ ^ 2) * ∑ j, (r j)⁻¹ := by rw [Finset.sum_mul]
      _ ≤ S * ∑ j, (r j)⁻¹ := mul_le_mul_of_nonneg_right hS hT0
  have hA2 : 0 < A ^ 2 := by positivity
  have e : 4 * (4 * A ^ 2 * (S + 1))⁻¹ * A ^ 2 = (S + 1)⁻¹ := by
    field_simp
  rw [e]
  have hS1 : 0 < S + 1 := by linarith
  rw [inv_mul_le_iff₀ hS1]
  nlinarith

/-- **Conclusion of FPT Step 4.**  Combine the inequality at the maximum point
(`eq:real-hessian-maximum`, `max_inequality_of_components`) with the absorption
(`eq:real-hessian-third-absorption`, `third_order_absorption`): if
`η'' ≥ 2η'²`, `A ≥ C₀ + 3`, `β, η', s ≥ 0`, `Σ‖sᵢ‖²/rᵢ ≥ 0` and `4εA² Σ‖aᵢ‖²/rᵢ ≤ T`, then
`η' K + T ≤ A n`. -/
theorem eta_K_add_T_le {U R N K T C₀ β s η' η'' S2 A nr Sa : ℝ}
    (hmax : U + R - N + η' * K + η'' * S2 + (A - C₀) * T - A * nr + β * η' * s + β / 4 ≤ 0)
    (habs : N ≤ U + R + T + Sa + 2 * η' ^ 2 * S2) (hSa : Sa ≤ T)
    (hη'' : 2 * η' ^ 2 ≤ η'') (hS2 : 0 ≤ S2) (hA : C₀ + 3 ≤ A) (hT : 0 ≤ T) (hβ : 0 ≤ β)
    (hη' : 0 ≤ η') (hs : 0 ≤ s) :
    η' * K + T ≤ A * nr := by
  have h1 : 2 * η' ^ 2 * S2 ≤ η'' * S2 := mul_le_mul_of_nonneg_right hη'' hS2
  have h2 : 3 * T ≤ (A - C₀) * T := mul_le_mul_of_nonneg_right (by linarith) hT
  have h3 : 0 ≤ β * η' * s := by positivity
  linarith

end Absorption

end SGPT.Envelopes.TosC11b
