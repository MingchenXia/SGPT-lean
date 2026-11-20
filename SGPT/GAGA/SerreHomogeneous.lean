import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic
import SGPT.Foundations.Analysis.Pending.RiemannExtension
import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Roots

/-!
# Homogeneous holomorphic functions are homogeneous polynomials

A holomorphic section of `𝒪(m)` on `ℙᴺ` is the same as a holomorphic function `F` on
`ℂ^{N+1} ∖ {0}` with `F(c x) = c^m F(x)`. We prove that such an `F` is a homogeneous polynomial
of degree `m` (`exists_isHomogeneous_eq_of_homogeneous`). This is the analytic content of
"`H⁰(ℙᴺ, 𝒪(m))` consists of the homogeneous polynomials of degree `m`", the base case of GAGA
for global sections.

Proof.
1. `F` is bounded by `M` on the unit sphere, so `‖F x‖ ≤ M ‖x‖^m`.
2. `F` is bounded near `0`. The Riemann extension theorem (TN `exists_extension_of_bounded`,
   across the hyperplane `z₀ = 0`) and continuity extend it to an entire function `G`.
3. Cauchy estimates (TN `norm_factorial_inv_smul_iteratedFDeriv_le`) on balls of radius
   `R → ∞` give `D^n G(0) = 0` for `n > m`. So `G = ∑_{n ≤ m} pₙ(x, …, x)` with
   `pₙ = D^n G(0)/n!` (TN `hasFPowerSeriesOnBall_of_differentiableOn`).
4. Homogeneity gives `∑_{n ≤ m} tⁿ pₙ(x,…,x) = t^m ∑_{n ≤ m} pₙ(x,…,x)` for all `t ≠ 0`. A
   polynomial in `t` with infinitely many roots vanishes, so `pₙ(x,…,x) = 0` for `n < m`.
5. The diagonal of a continuous `m`-linear form on `ℂ^d` is a homogeneous polynomial of degree
   `m` (`exists_isHomogeneous_eval_eq_diag`).

Blueprint: `claude-serre-gaga.tex`, node `claude-serre-gaga:homogeneous`.
-/

set_option autoImplicit false

open Filter Topology Metric
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

namespace SGPT.GAGA

noncomputable section

variable {d : ℕ}

/-- **The diagonal of a multilinear form is a homogeneous polynomial.** For a continuous
`k`-linear form `A` on `ℂ^d` there is a homogeneous polynomial `P` of degree `k` with
`P(x) = A(x, …, x)`. -/
theorem exists_isHomogeneous_eval_eq_diag {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => ComplexModel d) ℂ) :
    ∃ P : MvPolynomial (Fin d) ℂ, P.IsHomogeneous k ∧
      ∀ x : ComplexModel d, MvPolynomial.eval (fun i => x i) P = A (fun _ => x) := by
  classical
  let e : Fin d → ComplexModel d := fun i => EuclideanSpace.single i 1
  refine ⟨∑ r : Fin k → Fin d, MvPolynomial.C (A (fun j => e (r j))) *
    ∏ j, MvPolynomial.X (r j), ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun r _ => ?_
    have hprod := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun j => (MvPolynomial.X (r j) : MvPolynomial (Fin d) ℂ)) (fun _ => 1)
      (fun j _ => MvPolynomial.isHomogeneous_X ℂ (r j))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at hprod
    exact hprod.C_mul _
  · intro x
    have hx : x = ∑ i, x i • e i := by
      ext i
      simp [e, Pi.single_apply]
    have hA : A (fun _ => x) = ∑ r : Fin k → Fin d, A (fun j => x (r j) • e (r j)) := by
      conv_lhs => rw [hx]
      exact A.map_sum (fun _ i => x i • e i)
    rw [hA]
    simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod,
      MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [A.map_smul_univ (fun j => x (r j)) (fun j => e (r j)), smul_eq_mul, mul_comm]

/-- A coefficient identity: if `∑_{n ≤ m} tⁿ aₙ = t^m ∑_{n ≤ m} aₙ` for all `t ≠ 0`, then
`aₙ = 0` for `n < m`. -/
theorem coeff_eq_zero_of_homogeneous_identity {m : ℕ} {a : ℕ → ℂ}
    (h : ∀ t : ℂ, t ≠ 0 →
      ∑ n ∈ Finset.range (m + 1), t ^ n * a n = t ^ m * ∑ n ∈ Finset.range (m + 1), a n) :
    ∀ n < m, a n = 0 := by
  classical
  set Q : Polynomial ℂ := ∑ n ∈ Finset.range (m + 1), Polynomial.C (a n) * Polynomial.X ^ n -
    Polynomial.C (∑ n ∈ Finset.range (m + 1), a n) * Polynomial.X ^ m with hQ
  have hroot : {t : ℂ | t ≠ 0} ⊆ {t | Q.IsRoot t} := by
    intro t ht
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hQ, Polynomial.eval_sub,
      Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [sub_eq_zero]
    calc ∑ n ∈ Finset.range (m + 1), a n * t ^ n
        = ∑ n ∈ Finset.range (m + 1), t ^ n * a n :=
          Finset.sum_congr rfl fun n _ => mul_comm _ _
      _ = t ^ m * ∑ n ∈ Finset.range (m + 1), a n := h t ht
      _ = (∑ n ∈ Finset.range (m + 1), a n) * t ^ m := mul_comm _ _
  have hinf : Set.Infinite {t : ℂ | t ≠ 0} := by
    have : Set.Infinite ({0}ᶜ : Set ℂ) := Set.Finite.infinite_compl (Set.finite_singleton 0)
    simpa [Set.compl_def] using this
  have hQ0 : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q (hinf.mono hroot)
  intro n hn
  have hc := congrArg (fun q : Polynomial ℂ => q.coeff n) hQ0
  simp only [hQ, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single n (fun b _ hb => if_neg (Ne.symm hb))
    (fun hn' => absurd (Finset.mem_range.mpr (by omega)) hn'), if_pos rfl,
    if_neg hn.ne, sub_zero] at hc
  exact hc

/-- **Homogeneous holomorphic functions are polynomials.** If `F` is holomorphic on
`ℂ^d ∖ {0}` and `F(c x) = c^m F(x)` for `c ≠ 0`, then `F` is a homogeneous polynomial of
degree `m`. Equivalently, every holomorphic section of `𝒪(m)` on `ℙ^{d-1}` is a homogeneous
polynomial of degree `m`. -/
theorem exists_isHomogeneous_eq_of_homogeneous {m : ℕ} {F : ComplexModel d → ℂ}
    (hF : DifferentiableOn ℂ F {x | x ≠ 0})
    (hhom : ∀ (c : ℂ) (x : ComplexModel d), c ≠ 0 → x ≠ 0 → F (c • x) = c ^ m * F x) :
    ∃ P : MvPolynomial (Fin d) ℂ, P.IsHomogeneous m ∧
      ∀ x : ComplexModel d, x ≠ 0 → F x = MvPolynomial.eval (fun i => x i) P := by
  classical
  rcases d with _ | d
  · refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun x hx => ?_⟩
    exact absurd (Subsingleton.elim x 0) hx
  have hopen : IsOpen {x : ComplexModel (d + 1) | x ≠ 0} := isOpen_ne
  -- Step 1: the bound `‖F x‖ ≤ M ‖x‖^m`.
  obtain ⟨M₀, hM₀⟩ := (isCompact_sphere (0 : ComplexModel (d + 1)) 1).exists_bound_of_continuousOn
    (hF.continuousOn.mono fun x hx => by
      intro h0
      rw [mem_sphere, h0, dist_self] at hx
      exact zero_ne_one hx)
  set M := max M₀ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hbound : ∀ x : ComplexModel (d + 1), x ≠ 0 → ‖F x‖ ≤ M * ‖x‖ ^ m := by
    intro x hx
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u : ComplexModel (d + 1) := ((‖x‖ : ℂ)⁻¹) • x with hu
    have hu1 : u ∈ sphere (0 : ComplexModel (d + 1)) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ hnx]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, mem_sphere, dist_self] at hu1
      exact zero_ne_one hu1
    have hxu : x = (‖x‖ : ℂ) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnx), one_smul]
    rw [hxu, hhom _ _ (Complex.ofReal_ne_zero.mpr hnx) hu0, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm]
    have h1 : ‖(‖x‖ : ℂ) • u‖ = ‖x‖ := by rw [← hxu]
    rw [h1]
    exact mul_le_mul_of_nonneg_right ((hM₀ u hu1).trans (le_max_left _ _)) (by positivity)
  -- Step 2: extension across the hyperplane `z₀ = 0` near the origin.
  let h : ComplexModel (d + 1) → ℂ := fun z => z 0
  have hhd : Differentiable ℂ h := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin (d + 1))).differentiable
  let e₀ : ComplexModel (d + 1) := EuclideanSpace.single 0 1
  have he₀ : ∀ t : ℂ, h (t • e₀) = t := fun t => by simp [h, e₀]
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (d + 1)), h z = 0 := by
    intro hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    have hmem : ((ε / 2 : ℝ) : ℂ) • e₀ ∈ ball (0 : ComplexModel (d + 1)) ε := by
      rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      simp only [e₀, PiLp.norm_single, norm_one, mul_one]
      rw [abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    have := hball _ hmem
    rw [he₀] at this
    exact (half_pos hε).ne' (by exact_mod_cast this)
  obtain ⟨ρ, hρ, F₁, hF₁, hF₁eq⟩ := RiemannExtension.exists_extension_of_bounded one_pos
    hhd.differentiableOn hne
    (hF.mono fun z hz hz0 => hz.2 (by rw [hz0]; simp [h]))
    ⟨M, fun z hz => by
      have hz0 : z ≠ 0 := fun h0 => hz.2 (by rw [h0]; simp [h])
      have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz.1
      calc ‖F z‖ ≤ M * ‖z‖ ^ m := hbound z hz0
        _ ≤ M * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hz1.le
        _ = M := mul_one M⟩
  -- Step 3: `F₁ = F` on the punctured ball.
  have hF₁F : ∀ z ∈ ball (0 : ComplexModel (d + 1)) ρ, z ≠ 0 → F₁ z = F z := by
    intro z hz hz0
    by_cases hhz : h z ≠ 0
    · exact hF₁eq z hz hhz
    push Not at hhz
    have hcont : Continuous fun t : ℂ => z + t • e₀ := by fun_prop
    have hlim : Tendsto (fun t : ℂ => z + t • e₀) (𝓝[≠] 0) (𝓝 z) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun t : ℂ => F₁ (z + t • e₀)) (𝓝[≠] 0) (𝓝 (F₁ z)) :=
      ((hF₁.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto).comp hlim
    have h2 : Tendsto (fun t : ℂ => F (z + t • e₀)) (𝓝[≠] 0) (𝓝 (F z)) :=
      ((hF.continuousOn.continuousAt (hopen.mem_nhds hz0)).tendsto).comp hlim
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), F₁ (z + t • e₀) = F (z + t • e₀) := by
      filter_upwards [hlim.eventually (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin]
        with t ht ht0
      refine hF₁eq _ ht ?_
      have : h (z + t • e₀) = h z + t := by simp [h, e₀]
      rw [this, hhz, zero_add]
      exact ht0
    exact tendsto_nhds_unique (h1.congr' hev) h2
  -- Step 4: the entire extension `G`.
  let G : ComplexModel (d + 1) → ℂ := fun x => if x = 0 then F₁ 0 else F x
  have hGF : ∀ x, x ≠ 0 → G x = F x := fun x hx => if_neg hx
  have hGd : Differentiable ℂ G := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have heq : F₁ =ᶠ[𝓝 0] G := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy
        by_cases hy0 : y = 0
        · simp [G, hy0]
        · rw [hGF y hy0, hF₁F y hy hy0]
      exact (hF₁.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρ))).congr_of_eventuallyEq
        heq.symm
    · have heq : F =ᶠ[𝓝 x] G := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact (hGF y hy).symm
      exact (hF.differentiableAt (hopen.mem_nhds hx)).congr_of_eventuallyEq heq.symm
  -- Step 5: Cauchy estimates.
  set p : FormalMultilinearSeries ℂ (ComplexModel (d + 1)) ℂ :=
    fun n => (n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n G 0 with hp
  have hGbound : ∀ R : ℝ, 0 < R → ∀ w ∈ ball (0 : ComplexModel (d + 1)) R,
      ‖G w‖ ≤ M * R ^ m + ‖G 0‖ := by
    intro R hR w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      have : 0 ≤ M * R ^ m := by positivity
      linarith
    · rw [hGF w hw0]
      have : ‖w‖ ≤ R := (mem_ball_zero_iff.mp hw).le
      have : M * ‖w‖ ^ m ≤ M * R ^ m := by gcongr
      linarith [hbound w hw0, norm_nonneg (G 0)]
  have hcauchy : ∀ (R : ℝ), 0 < R → ∀ n, ‖p n‖ ≤
      (M * R ^ m + ‖G 0‖) * Real.exp 1 * (Real.exp 1 / R) ^ n := fun R hR n =>
    HolomorphicAnalytic.norm_factorial_inv_smul_iteratedFDeriv_le hR hGd.differentiableOn
      (hGbound R hR) n
  have hvanish : ∀ n, m < n → p n = 0 := by
    intro n hn
    set K : ℝ := (M + ‖G 0‖) * Real.exp 1 * Real.exp 1 ^ n with hK
    have hle : ∀ R : ℝ, 1 ≤ R → ‖p n‖ ≤ K / R := by
      intro R hR
      have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
      refine (hcauchy R hR0 n).trans ?_
      have hRm : R ^ m ≤ R ^ (n - 1) := pow_le_pow_right₀ hR (by omega)
      have hRn : R ^ n = R ^ (n - 1) * R := by
        rw [← pow_succ]
        congr 1
        omega
      have hpos : 0 < R ^ (n - 1) := by positivity
      rw [div_pow, hRn, hK]
      have hG0 := norm_nonneg (G 0)
      have he := Real.exp_pos 1
      have hen : 0 < Real.exp 1 ^ n := by positivity
      have h1 : M * R ^ m + ‖G 0‖ ≤ (M + ‖G 0‖) * R ^ (n - 1) := by
        have h2 : 1 ≤ R ^ (n - 1) := one_le_pow₀ hR
        nlinarith
      have h3 : (M * R ^ m + ‖G 0‖) / R ^ (n - 1) ≤ M + ‖G 0‖ := by
        rw [div_le_iff₀ hpos]
        exact h1
      calc (M * R ^ m + ‖G 0‖) * Real.exp 1 * (Real.exp 1 ^ n / (R ^ (n - 1) * R))
          = (M * R ^ m + ‖G 0‖) / R ^ (n - 1) * (Real.exp 1 * Real.exp 1 ^ n / R) := by ring
        _ ≤ (M + ‖G 0‖) * (Real.exp 1 * Real.exp 1 ^ n / R) := by gcongr
        _ = (M + ‖G 0‖) * Real.exp 1 * Real.exp 1 ^ n / R := by ring
    have htend : Tendsto (fun R : ℝ => K / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h0 : ‖p n‖ ≤ 0 :=
      ge_of_tendsto htend (eventually_atTop.mpr ⟨1, fun R hR => hle R hR⟩)
    exact norm_le_zero_iff.mp h0
  -- Step 6: `G` is the finite sum of its Taylor terms.
  have hexp : ∀ x : ComplexModel (d + 1),
      G x = ∑ n ∈ Finset.range (m + 1), p n (fun _ => x) := by
    intro x
    set R : ℝ := Real.exp 1 * (‖x‖ + 1) with hR
    have hR0 : 0 < R := by positivity
    have hser := HolomorphicAnalytic.hasFPowerSeriesOnBall_of_differentiableOn hR0
      hGd.differentiableOn (hGbound R hR0)
    have hx : x ∈ Metric.eball (0 : ComplexModel (d + 1)) (ENNReal.ofReal (R / Real.exp 1)) := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
        ENNReal.ofReal_lt_ofReal_iff (div_pos hR0 (Real.exp_pos 1)), hR,
        mul_div_cancel_left₀ _ (Real.exp_pos 1).ne']
      linarith
    have hs := hser.hasSum hx
    rw [zero_add] at hs
    have hs' : HasSum (fun n => p n (fun _ => x))
        (∑ n ∈ Finset.range (m + 1), p n (fun _ => x)) :=
      hasSum_sum_of_ne_finset_zero fun n hn => by
        rw [hvanish n (by simpa using hn)]
        rfl
    exact hs.unique hs'
  -- Step 7: homogeneity kills the lower Taylor terms.
  have hdiag : ∀ x : ComplexModel (d + 1), x ≠ 0 → F x = p m (fun _ => x) := by
    intro x hx
    have hid : ∀ t : ℂ, t ≠ 0 →
        ∑ n ∈ Finset.range (m + 1), t ^ n * p n (fun _ => x) =
          t ^ m * ∑ n ∈ Finset.range (m + 1), p n (fun _ => x) := by
      intro t ht
      have htx : t • x ≠ 0 := smul_ne_zero ht hx
      have h1 : G (t • x) = ∑ n ∈ Finset.range (m + 1), t ^ n * p n (fun _ => x) := by
        rw [hexp]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [(p n).map_smul_univ (fun _ => t) (fun _ => x), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      rw [← h1, hGF _ htx, hhom t x ht hx, ← hGF x hx, hexp x]
    have hlow := coeff_eq_zero_of_homogeneous_identity hid
    rw [← hGF x hx, hexp x, Finset.sum_range_succ,
      Finset.sum_eq_zero fun n hn => hlow n (Finset.mem_range.mp hn), zero_add]
  -- Step 8: the top Taylor term is a homogeneous polynomial.
  obtain ⟨P, hPh, hPeval⟩ := exists_isHomogeneous_eval_eq_diag (p m)
  exact ⟨P, hPh, fun x hx => by rw [hdiag x hx, hPeval]⟩

end

end SGPT.GAGA
