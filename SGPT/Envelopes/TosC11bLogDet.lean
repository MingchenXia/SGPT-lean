import SGPT.Bergman.SourceDeterminantVariation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.PosDef

/-!
# First and second variation of `log det` along a curve of Hermitian matrices

Lane TOS-C11b (`claude-tos-c11b`, node `tos-c11b:log-det`).  Source: Xia, *Foundations of
pluripotential theory*, `lem:penalized-real-hessian`, Step 3 ("Taking logarithms in the penalized
equation gives `log det G = log det k + β(a - f)`.  Differentiating twice along `V₁` and using
`∂(G⁻¹) = -G⁻¹(∂G)G⁻¹`, we obtain at `x₀` …") and the once differentiated equation used for
`D_G s`, for SGPT `thm:Tos_C11` (Tosatti, Chu–Zhou).

For a curve `t ↦ G(t)` of complex matrices, twice differentiable entrywise at `0`, Hermitian near
`0` and positive definite at `0`:

* `hasDerivAt_det_of_det_ne_zero` — Jacobi's formula `(det G)' = det G · tr(G⁻¹ G')` at every point
  where `det G ≠ 0` (from the identity case of lane BERGMAN, `hasDerivAt_det_at_identity`);
* `hasDerivAt_inv_apply` — `(G⁻¹)' = -G⁻¹ G' G⁻¹`, entrywise;
* `log_det_variation` — `(log det G)' = Re tr(G⁻¹ G')` near `0` and
  `(log det G)''(0) = Re tr(G⁻¹ G'') - Re tr(G⁻¹ G' G⁻¹ G')`;
* `differentiated_log_det_equation` — if `log det G = φ` near `0` with `G(0) = diag(r)`, then
  `Σᵢ Re G'ᵢᵢ(0)/rᵢ = φ'(0)` and `Σᵢ Re G''ᵢᵢ(0)/rᵢ = Σ_{p,q} |G'_{pq}(0)|²/(r_p r_q) + φ''(0)`
  (the once and twice differentiated penalized equation along a line);
* `trace_diagonal_inv_mul_re`, `trace_diagonal_inv_mul_mul_re` — at a diagonal point
  `G(0) = diag(r)` with `G'(0)` Hermitian these are `Σᵢ Re G''ᵢᵢ / rᵢ` and
  `Σ_{p,q} |G'_{pq}|² / (r_p r_q)`, the two terms of FPT's identity
  `Σᵢ rᵢ⁻¹ V₁V₁G_{iī} = Σ_{p,q} |V₁G_{pq̄}|²/(r_p r_q) + V₁V₁ log det k + β(λ - f_{V₁V₁})`.
-/

set_option autoImplicit false

noncomputable section

open Matrix Filter
open scoped Topology ComplexConjugate ComplexOrder

namespace SGPT.Envelopes.TosC11b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Jacobi's formula** at a point where the determinant does not vanish:
`(det G)'(t₀) = det G(t₀) · tr(G(t₀)⁻¹ G')`. -/
theorem hasDerivAt_det_of_det_ne_zero {G : ℝ → Matrix ι ι ℂ} {G' : Matrix ι ι ℂ} {t₀ : ℝ}
    (hd : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) t₀) (h0 : (G t₀).det ≠ 0) :
    HasDerivAt (fun t => (G t).det) ((G t₀).det * ((G t₀)⁻¹ * G').trace) t₀ := by
  set P := (G t₀)⁻¹ with hP
  have hu : IsUnit (G t₀).det := isUnit_iff_ne_zero.mpr h0
  have hA : ∀ i j, HasDerivAt (fun t => (P * G t) i j) ((P * G') i j) t₀ := by
    intro i j
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hd k j).const_mul (P i k)
  have hA1 : P * G t₀ = 1 := nonsing_inv_mul _ hu
  have h := SGPT.Bergman.WeightVariation.hasDerivAt_det_at_identity (fun t => P * G t) (P * G')
    t₀ hA1 hA
  have h2 := h.const_mul (G t₀).det
  have heq : (fun t => (G t₀).det * (P * G t).det) = fun t => (G t).det := by
    funext t
    rw [det_mul, ← mul_assoc, ← det_mul, hP, mul_nonsing_inv _ hu, det_one, one_mul]
  rw [heq] at h2
  exact h2

/-- The determinant of an entrywise differentiable curve is differentiable. -/
theorem differentiableAt_det_curve {B : ℝ → Matrix ι ι ℂ} {t₀ : ℝ}
    (hd : ∀ i j, DifferentiableAt ℝ (fun t => B t i j) t₀) :
    DifferentiableAt ℝ (fun t => (B t).det) t₀ := by
  simp_rw [det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact (HasDerivAt.fun_finsetProd (u := Finset.univ) fun i _ =>
    (hd (σ i) i).hasDerivAt).differentiableAt

/-- **The derivative of the inverse**, entrywise: `(G⁻¹)'(t₀) = -G⁻¹ G' G⁻¹` where `det G(t₀) ≠ 0`. -/
theorem hasDerivAt_inv_apply {G G' : ℝ → Matrix ι ι ℂ} {t₀ : ℝ}
    (hd : ∀ᶠ t in 𝓝 t₀, ∀ i j, HasDerivAt (fun t => G t i j) (G' t i j) t)
    (h0 : (G t₀).det ≠ 0) (i j : ι) :
    HasDerivAt (fun t => (G t)⁻¹ i j) (-((G t₀)⁻¹ * G' t₀ * (G t₀)⁻¹) i j) t₀ := by
  have hd0 : ∀ i j, HasDerivAt (fun t => G t i j) (G' t₀ i j) t₀ := hd.self_of_nhds
  -- the determinant is differentiable and nonzero near `t₀`
  have hdet := hasDerivAt_det_of_det_ne_zero hd0 h0
  have hne : ∀ᶠ t in 𝓝 t₀, (G t).det ≠ 0 := hdet.continuousAt.eventually_ne h0
  -- the entries of the inverse are differentiable at `t₀`
  have hdiff : ∀ k l, DifferentiableAt ℝ (fun t => (G t)⁻¹ k l) t₀ := by
    intro k l
    have hadj : DifferentiableAt ℝ (fun t => adjugate (G t) k l) t₀ := by
      simp_rw [adjugate_apply]
      refine differentiableAt_det_curve fun a b => ?_
      by_cases hab : a = l
      · subst hab; simp only [updateRow_self]; exact differentiableAt_const _
      · simp only [updateRow_ne hab]; exact (hd0 a b).differentiableAt
    have heq : (fun t => (G t)⁻¹ k l) = fun t => ((G t).det)⁻¹ * adjugate (G t) k l := by
      funext t
      rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    rw [heq]
    exact (hdet.differentiableAt.inv h0).mul hadj
  set D : Matrix ι ι ℂ := fun k l => deriv (fun t => (G t)⁻¹ k l) t₀ with hDdef
  have hD : ∀ k l, HasDerivAt (fun t => (G t)⁻¹ k l) (D k l) t₀ := fun k l =>
    (hdiff k l).hasDerivAt
  -- differentiate `G G⁻¹ = 1`
  have hW : G' t₀ * (G t₀)⁻¹ + G t₀ * D = 0 := by
    ext a b
    have hev : (fun t => (G t * (G t)⁻¹) a b) =ᶠ[𝓝 t₀] fun _ => (1 : Matrix ι ι ℂ) a b := by
      filter_upwards [hne] with t ht
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]
    have h1 : HasDerivAt (fun t => (G t * (G t)⁻¹) a b)
        (∑ k, (G' t₀ a k * (G t₀)⁻¹ k b + G t₀ a k * D k b)) t₀ := by
      simp only [Matrix.mul_apply]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hd0 a k).mul (hD k b)
    have h2 : HasDerivAt (fun t => (G t * (G t)⁻¹) a b) 0 t₀ :=
      (hasDerivAt_const t₀ ((1 : Matrix ι ι ℂ) a b)).congr_of_eventuallyEq hev
    have := h1.unique h2
    simpa [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib] using this
  have hu : IsUnit (G t₀).det := isUnit_iff_ne_zero.mpr h0
  have hsol : D = -((G t₀)⁻¹ * G' t₀ * (G t₀)⁻¹) := by
    have h1 : G t₀ * D = -(G' t₀ * (G t₀)⁻¹) := eq_neg_of_add_eq_zero_right hW
    calc D = (G t₀)⁻¹ * (G t₀ * D) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -((G t₀)⁻¹ * G' t₀ * (G t₀)⁻¹) := by rw [h1, Matrix.mul_neg, Matrix.mul_assoc]
  have h := hD i j
  rw [hsol] at h
  simpa [Matrix.neg_apply] using h

/-- The determinant of a Hermitian matrix is real. -/
theorem det_im_eq_zero_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : A.det.im = 0 := by
  have h : star A.det = A.det := by rw [← det_conjTranspose, hA.eq]
  exact Complex.conj_eq_iff_im.mp h

/-- **First and second variation of `log det`** along a curve of Hermitian matrices, positive
definite at `0`: near `0`, `(log det G)' = Re tr(G⁻¹ G')`, and at `0` the derivative of
`t ↦ Re tr(G⁻¹ G')` is `Re tr(G⁻¹ G₂) - Re tr(G⁻¹ G' G⁻¹ G')`. -/
theorem log_det_variation {G G' : ℝ → Matrix ι ι ℂ} {G₂ : Matrix ι ι ℂ}
    (hd : ∀ᶠ t in 𝓝 0, ∀ i j, HasDerivAt (fun t => G t i j) (G' t i j) t)
    (hd' : ∀ i j, HasDerivAt (fun t => G' t i j) (G₂ i j) 0)
    (hherm : ∀ᶠ t in 𝓝 0, (G t).IsHermitian) (hpos : (G 0).PosDef) :
    (∀ᶠ t in 𝓝 0, HasDerivAt (fun t => Real.log (G t).det.re) ((G t)⁻¹ * G' t).trace.re t) ∧
      HasDerivAt (fun t => ((G t)⁻¹ * G' t).trace.re)
        (((G 0)⁻¹ * G₂).trace.re - ((G 0)⁻¹ * G' 0 * (G 0)⁻¹ * G' 0).trace.re) 0 := by
  have hdet0 : 0 < (G 0).det.re := (Complex.pos_iff.mp (Matrix.PosDef.det_pos hpos)).1
  have hne0 : (G 0).det ≠ 0 := fun h => by rw [h, Complex.zero_re] at hdet0; exact lt_irrefl _ hdet0
  have hdetd := hasDerivAt_det_of_det_ne_zero hd.self_of_nhds hne0
  have hre : ∀ᶠ t in 𝓝 0, 0 < (G t).det.re :=
    (Complex.continuous_re.continuousAt.comp hdetd.continuousAt).eventually
      (lt_mem_nhds hdet0)
  refine ⟨(hd.and (hre.and hherm)).mono fun t ht => ?_, ?_⟩
  · obtain ⟨hdt, hrt, hht⟩ := ht
    have hnet : (G t).det ≠ 0 := fun h => by rw [h, Complex.zero_re] at hrt; exact lt_irrefl _ hrt
    have h1 := hasDerivAt_det_of_det_ne_zero hdt hnet
    have h2 := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1).log hrt.ne'
    have him := det_im_eq_zero_of_isHermitian hht
    refine h2.congr_deriv ?_
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.mul_re, him, zero_mul, sub_zero]
    field_simp
  · -- the trace as a double sum
    have hinv := fun k l => hasDerivAt_inv_apply hd hne0 k l
    have hsum : HasDerivAt (fun t => ((G t)⁻¹ * G' t).trace)
        (∑ i, ∑ k, (-((G 0)⁻¹ * G' 0 * (G 0)⁻¹) i k * G' 0 k i + (G 0)⁻¹ i k * G₂ k i)) 0 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        HasDerivAt.fun_sum (u := Finset.univ) fun k _ => (hinv i k).mul (hd' k i)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hsum
    refine h.congr_deriv ?_
    simp only [Complex.reCLM_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Finset.sum_add_distrib, Complex.add_re, Complex.re_sum, neg_mul, Complex.neg_re,
      Finset.sum_neg_distrib, Finset.sum_mul]
    ring

/-- The inverse of an invertible real diagonal matrix. -/
theorem inv_diagonal_ofReal (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) :
    (diagonal fun i => (r i : ℂ))⁻¹ = diagonal fun i => ((r i : ℂ))⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have : (r i : ℂ) ≠ 0 := by exact_mod_cast hr i
  field_simp

/-- At a diagonal point: `Re tr(diag(r)⁻¹ H) = Σᵢ Re Hᵢᵢ / rᵢ`. -/
theorem trace_diagonal_inv_mul_re (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (H : Matrix ι ι ℂ) :
    ((diagonal fun i => (r i : ℂ))⁻¹ * H).trace.re = ∑ i, (H i i).re / r i := by
  rw [inv_diagonal_ofReal r hr]
  simp only [Matrix.trace, Matrix.diag, diagonal_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, div_eq_inv_mul]

/-- At a diagonal point with `X` Hermitian:
`Re tr(diag(r)⁻¹ X diag(r)⁻¹ X) = Σ_{p,q} |X_{pq}|² / (r_p r_q)`. -/
theorem trace_diagonal_inv_mul_mul_re (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) :
    ((diagonal fun i => (r i : ℂ))⁻¹ * X * (diagonal fun i => (r i : ℂ))⁻¹ * X).trace.re =
      ∑ p, ∑ q, ‖X p q‖ ^ 2 / (r p * r q) := by
  rw [inv_diagonal_ofReal r hr]
  set d : ι → ℂ := fun i => ((r i : ℂ))⁻¹
  have hm : ∀ i k, (diagonal d * X * diagonal d) i k = d i * X i k * d k := by
    intro i k; simp [diagonal_mul, mul_diagonal]
  have htr : (diagonal d * X * diagonal d * X).trace = ∑ p, ∑ q, d p * X p q * d q * X q p := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := diagonal d * X * diagonal d), hm]
  rw [htr, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hqp : X q p = conj (X p q) := by
    have := congrFun (congrFun hX.eq q) p
    rw [conjTranspose_apply] at this
    rw [← this]; rfl
  rw [hqp]
  have hn : X p q * conj (X p q) = (‖X p q‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have e : d p * X p q * d q * conj (X p q) =
      (((r p)⁻¹ * (r q)⁻¹ * ‖X p q‖ ^ 2 : ℝ) : ℂ) := by
    simp only [d]
    push_cast
    rw [← hn]; ring
  rw [e, Complex.ofReal_re]
  have := hr p
  have := hr q
  field_simp

/-- **The differentiated penalized equation along a line** (FPT `lem:penalized-real-hessian`,
Step 3).  Let `t ↦ G(t)` be Hermitian near `0`, twice differentiable entrywise at `0`, with
`G(0) = diag(r)`, `rᵢ > 0`, and let `log det G = φ` near `0`, where `φ` is twice differentiable at `0`
(in FPT `φ = log det k + β(a - f)` along `t ↦ x₀ + t V₁`).  Then
`Σᵢ Re G'ᵢᵢ(0) / rᵢ = φ'(0)` and `Σᵢ Re G''ᵢᵢ(0) / rᵢ = Σ_{p,q} |G'_{pq}(0)|² / (r_p r_q) + φ''(0)`. -/
theorem differentiated_log_det_equation {G G' : ℝ → Matrix ι ι ℂ} {G₂ : Matrix ι ι ℂ}
    {φ φ' : ℝ → ℝ} {φ₂ : ℝ} (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hd : ∀ᶠ t in 𝓝 0, ∀ i j, HasDerivAt (fun t => G t i j) (G' t i j) t)
    (hd' : ∀ i j, HasDerivAt (fun t => G' t i j) (G₂ i j) 0)
    (hherm : ∀ᶠ t in 𝓝 0, (G t).IsHermitian) (hG0 : G 0 = diagonal fun i => (r i : ℂ))
    (hφ : ∀ᶠ t in 𝓝 0, HasDerivAt φ (φ' t) t) (hφ' : HasDerivAt φ' φ₂ 0)
    (heq : ∀ᶠ t in 𝓝 0, Real.log (G t).det.re = φ t) :
    ∑ i, (G' 0 i i).re / r i = φ' 0 ∧
      ∑ i, (G₂ i i).re / r i = (∑ p, ∑ q, ‖G' 0 p q‖ ^ 2 / (r p * r q)) + φ₂ := by
  have hr0 : ∀ i, r i ≠ 0 := fun i => (hr i).ne'
  have hpos : (G 0).PosDef := by
    rw [hG0]
    exact Matrix.PosDef.diagonal fun i => by exact_mod_cast hr i
  obtain ⟨h1, h2⟩ := log_det_variation hd hd' hherm hpos
  -- the first derivatives agree near `0`
  have hfirst : ∀ᶠ t in 𝓝 0, ((G t)⁻¹ * G' t).trace.re = φ' t := by
    filter_upwards [h1, hφ, heq.eventually_nhds] with t ht hφt heqt
    exact ht.unique (hφt.congr_of_eventuallyEq heqt)
  have hherm0 : (G' 0).IsHermitian := by
    -- the derivative of a Hermitian curve is Hermitian
    ext i j
    have hev : ∀ᶠ t in 𝓝 0, G t j i = star (G t i j) :=
      hherm.mono fun t ht => by
        have := congrFun (congrFun ht.eq j) i
        rw [conjTranspose_apply] at this
        exact this.symm
    have hA := (hd.self_of_nhds j i)
    have hB : HasDerivAt (fun t => star (G t i j)) (star (G' 0 i j)) 0 :=
      (Complex.conjCLE.hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hd.self_of_nhds i j)
    have := hA.unique (hB.congr_of_eventuallyEq hev)
    rw [conjTranspose_apply, this, star_star]
  refine ⟨?_, ?_⟩
  · rw [← hfirst.self_of_nhds, hG0, trace_diagonal_inv_mul_re r hr0]
  · have h3 := h2.unique (hφ'.congr_of_eventuallyEq hfirst)
    rw [hG0, trace_diagonal_inv_mul_re r hr0] at h3
    have h4 := trace_diagonal_inv_mul_mul_re r hr0 hherm0
    linarith

end SGPT.Envelopes.TosC11b
