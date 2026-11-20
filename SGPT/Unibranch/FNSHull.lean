import SGPT.Unibranch.FNRHullBasics

/-!
# Circular sets and monomial polyhedra

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Theorem 5.3.1 (`[FN80]`), used for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`, after `def:unibranch:L105`).

In the proof of `[FN80, Thm. 5.3.1]` one works in `ℂⁿ × ℂ ∋ (z, w)` with the circular
("Hartogs") domain `Ω = {φ(z) + log |w| < 0}` over `X ⊆ ℂⁿ`. We realize `ℂⁿ × ℂ` as
`ComplexModel (n + 1)` with **`w` the coordinate `0`** and `z` the coordinates `i.succ`, so that
`MvPolynomial.finSuccEquiv` writes every polynomial as `∑ₖ aₖ(z) wᵏ`.

* `mono a k`: the monomial `a(z) wᵏ` (`polyEval_mono`).
* `wscale c`: `(z, w) ↦ (z, c w)`; `IsRotationInvariant`, `IsCircular` (invariance under
  `|c| = 1`, resp. `|c| ≤ 1`); hulls of such sets are such (`IsRotationInvariant.polyHull`,
  `IsCircular.polyHull`, from FNR's `diagScale_mem_polyHull`).
* `norm_coeff_mul_pow_le`: Cauchy's estimate `|cₖ| rᵏ ≤ max_{|t| = r} |Q(t)|` for one-variable
  polynomials.
* `exists_mono_separator`: on a rotation invariant set, a polynomial separating a point can be
  replaced by a **monomial** `a(z) wᵏ` (Cauchy's estimate applied to a high power).
* `monoPoly S`, `monoPolyClosed S`: open and closed monomial polyhedra
  `{(z, w) : |aᵢ(z)| |w|^{kᵢ} < 1}`; `exists_monoPoly_nhds`: the polynomial hull of a compact
  rotation invariant set has a basis of neighbourhoods which are monomial polyhedra (the
  monomial version of the Codex lemma `exists_polyhedron_neighborhood`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum FNR

variable {n : ℕ}

/-! ### Coordinates and monomials -/

/-- The `z`-coordinates `(x_{i+1})_i` of a point of `ℂⁿ × ℂ = ℂ^{n+1}`. -/
def zpart (x : ComplexModel (n + 1)) : ComplexModel n :=
  WithLp.toLp 2 fun i => x i.succ

@[simp] theorem zpart_apply (x : ComplexModel (n + 1)) (i : Fin n) : zpart x i = x i.succ := rfl

/-- The point `(z, w) ∈ ℂⁿ × ℂ` of `ℂ^{n+1}` (with `w` in coordinate `0`). -/
def mkPt (z : ComplexModel n) (w : ℂ) : ComplexModel (n + 1) :=
  WithLp.toLp 2 (Fin.cons w fun i => z i)

@[simp] theorem mkPt_zero (z : ComplexModel n) (w : ℂ) : mkPt z w 0 = w := rfl

@[simp] theorem mkPt_succ (z : ComplexModel n) (w : ℂ) (i : Fin n) : mkPt z w i.succ = z i := rfl

@[simp] theorem zpart_mkPt (z : ComplexModel n) (w : ℂ) : zpart (mkPt z w) = z := by
  ext i; rfl

theorem mkPt_zpart (x : ComplexModel (n + 1)) : mkPt (zpart x) (x 0) = x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- `zpart` as a continuous linear map. -/
def zpartCLM : ComplexModel (n + 1) →L[ℂ] ComplexModel n :=
  LinearMap.toContinuousLinearMap
    { toFun := zpart
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

theorem zpartCLM_apply (x : ComplexModel (n + 1)) : zpartCLM x = zpart x := rfl

theorem differentiable_zpart : Differentiable ℂ (zpart (n := n)) :=
  zpartCLM.differentiable

theorem continuous_zpart : Continuous (zpart (n := n)) :=
  zpartCLM.continuous

/-- `(z, w) ↦ mkPt z w` as a continuous linear map on `ℂⁿ × ℂ`. -/
def mkPtCLM : ComplexModel n × ℂ →L[ℂ] ComplexModel (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => mkPt p.1 p.2
      map_add' := fun p q => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [mkPt]
      map_smul' := fun c p => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [mkPt] }

theorem mkPtCLM_apply (p : ComplexModel n × ℂ) : mkPtCLM p = mkPt p.1 p.2 := rfl

theorem continuous_mkPt : Continuous fun p : ComplexModel n × ℂ => mkPt p.1 p.2 :=
  mkPtCLM.continuous

theorem differentiable_mkPt : Differentiable ℂ fun p : ComplexModel n × ℂ => mkPt p.1 p.2 :=
  mkPtCLM.differentiable

/-- The monomial `a(z) wᵏ` as a polynomial on `ℂ^{n+1}`. -/
def mono (a : Poly n) (k : ℕ) : Poly (n + 1) :=
  (MvPolynomial.finSuccEquiv ℂ n).symm (Polynomial.C a * Polynomial.X ^ k)

/-- Evaluation of a polynomial on `ℂ^{n+1}` through `finSuccEquiv`. -/
theorem polyEval_eq_eval_finSuccEquiv (P : Poly (n + 1)) (x : ComplexModel (n + 1)) :
    polyEval P x = Polynomial.eval (x 0)
      (Polynomial.map (MvPolynomial.eval fun i => x i.succ)
        (MvPolynomial.finSuccEquiv ℂ n P)) := by
  have hx : (Fin.cons (x 0) fun i : Fin n => x i.succ : Fin (n + 1) → ℂ) = fun i => x i :=
    Fin.cons_self_tail (fun i => x i)
  rw [← MvPolynomial.eval_eq_eval_mv_eval', hx]
  rfl

theorem polyEval_mono (a : Poly n) (k : ℕ) (x : ComplexModel (n + 1)) :
    polyEval (mono a k) x = polyEval a (zpart x) * x 0 ^ k := by
  rw [polyEval_eq_eval_finSuccEquiv, mono, AlgEquiv.apply_symm_apply]
  simp [polyEval, Polynomial.eval_mul]

/-- The coefficient `aₖ(z)` of `wᵏ` in a polynomial on `ℂ^{n+1}`. -/
def wcoeff (P : Poly (n + 1)) (k : ℕ) : Poly n :=
  (MvPolynomial.finSuccEquiv ℂ n P).coeff k

/-- The one-variable polynomial `w ↦ P(z, w)` for the `z`-part of `x`. -/
def wslice (P : Poly (n + 1)) (x : ComplexModel (n + 1)) : Polynomial ℂ :=
  Polynomial.map (MvPolynomial.eval fun i => x i.succ) (MvPolynomial.finSuccEquiv ℂ n P)

theorem coeff_wslice (P : Poly (n + 1)) (x : ComplexModel (n + 1)) (k : ℕ) :
    (wslice P x).coeff k = polyEval (wcoeff P k) (zpart x) := by
  simp [wslice, wcoeff, polyEval, Polynomial.coeff_map]

theorem polyEval_mono_wcoeff (P : Poly (n + 1)) (k : ℕ) (x : ComplexModel (n + 1)) :
    polyEval (mono (wcoeff P k) k) x = (wslice P x).coeff k * x 0 ^ k := by
  rw [polyEval_mono, coeff_wslice]

/-! ### Scaling in `w` -/

/-- The scaling `(z, w) ↦ (z, c w)`. -/
def wscale (c : ℂ) (x : ComplexModel (n + 1)) : ComplexModel (n + 1) :=
  diagScale (Fin.cons c fun _ => 1) x

@[simp] theorem wscale_zero (c : ℂ) (x : ComplexModel (n + 1)) : wscale c x 0 = c * x 0 := by
  simp [wscale, diagScale]

@[simp] theorem wscale_succ (c : ℂ) (x : ComplexModel (n + 1)) (i : Fin n) :
    wscale c x i.succ = x i.succ := by
  simp [wscale, diagScale]

theorem zpart_wscale (c : ℂ) (x : ComplexModel (n + 1)) : zpart (wscale c x) = zpart x := by
  ext i; simp

theorem polyEval_wscale (P : Poly (n + 1)) (c : ℂ) (x : ComplexModel (n + 1)) :
    polyEval P (wscale c x) = (wslice P x).eval (c * x 0) := by
  rw [polyEval_eq_eval_finSuccEquiv, wscale_zero]
  simp only [wscale_succ]
  rfl

/-- Invariance under the rotations `(z, w) ↦ (z, c w)`, `|c| = 1`. -/
def IsRotationInvariant (M : Set (ComplexModel (n + 1))) : Prop :=
  ∀ x ∈ M, ∀ c : ℂ, ‖c‖ = 1 → wscale c x ∈ M

/-- Complete circularity: invariance under `(z, w) ↦ (z, c w)` for `|c| ≤ 1`. -/
def IsCircular (M : Set (ComplexModel (n + 1))) : Prop :=
  ∀ x ∈ M, ∀ c : ℂ, ‖c‖ ≤ 1 → wscale c x ∈ M

theorem IsCircular.isRotationInvariant {M : Set (ComplexModel (n + 1))} (hM : IsCircular M) :
    IsRotationInvariant M :=
  fun x hx c hc => hM x hx c hc.le

theorem IsRotationInvariant.polyHull {M : Set (ComplexModel (n + 1))}
    (hM : IsRotationInvariant M) : IsRotationInvariant (polyHull M) :=
  fun _ hx c hc => diagScale_mem_polyHull _ (fun y hy => hM y hy c hc) hx

theorem IsCircular.polyHull {M : Set (ComplexModel (n + 1))} (hM : IsCircular M) :
    IsCircular (polyHull M) :=
  fun _ hx c hc => diagScale_mem_polyHull _ (fun y hy => hM y hy c hc) hx

theorem IsRotationInvariant.union {M M' : Set (ComplexModel (n + 1))}
    (hM : IsRotationInvariant M) (hM' : IsRotationInvariant M') : IsRotationInvariant (M ∪ M') := by
  rintro x (hx | hx) c hc
  · exact Or.inl (hM x hx c hc)
  · exact Or.inr (hM' x hx c hc)

theorem IsCircular.union {M M' : Set (ComplexModel (n + 1))}
    (hM : IsCircular M) (hM' : IsCircular M') : IsCircular (M ∪ M') := by
  rintro x (hx | hx) c hc
  · exact Or.inl (hM x hx c hc)
  · exact Or.inr (hM' x hx c hc)

/-! ### Cauchy's estimate for polynomial coefficients -/

theorem iteratedDeriv_polynomial_eval (Q : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun t => Q.eval t) = fun t => (Polynomial.derivative^[k] Q).eval t := by
  induction k generalizing Q with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have h : deriv (fun t => Q.eval t) = fun t => (Polynomial.derivative Q).eval t := by
      funext t; exact Polynomial.deriv Q
    rw [h, ih]

theorem iteratedDeriv_polynomial_eval_zero (Q : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun t => Q.eval t) 0 = k.factorial * Q.coeff k := by
  rw [iteratedDeriv_polynomial_eval]
  show (Polynomial.derivative^[k] Q).eval 0 = _
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

/-- **Cauchy's estimate** for one-variable polynomials: `|cₖ| rᵏ ≤ max_{|t| = r} |Q(t)|`. -/
theorem norm_coeff_mul_pow_le (Q : Polynomial ℂ) (k : ℕ) {r C : ℝ} (hr : 0 ≤ r)
    (hC : ∀ t : ℂ, ‖t‖ = r → ‖Q.eval t‖ ≤ C) : ‖Q.coeff k‖ * r ^ k ≤ C := by
  rcases hr.eq_or_lt with rfl | hr
  · have h0 := hC 0 (by simp)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
    · rw [zero_pow hk.ne', mul_zero]
      exact (norm_nonneg _).trans h0
  · have hdc : DiffContOnCl ℂ (fun t => Q.eval t) (ball (0 : ℂ) r) :=
      (Polynomial.differentiable Q).diffContOnCl
    have hS : ∀ t ∈ sphere (0 : ℂ) r, ‖Q.eval t‖ ≤ C := fun t ht => hC t (by simpa using ht)
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdc hS
    rw [iteratedDeriv_polynomial_eval_zero, norm_mul, Complex.norm_natCast] at hcauchy
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hrk : 0 < r ^ k := pow_pos hr k
    rw [le_div_iff₀ hrk] at hcauchy
    nlinarith [norm_nonneg (Q.coeff k)]

/-- On a rotation invariant set, the monomial parts of a polynomial are bounded by the
polynomial. -/
theorem norm_polyEval_mono_wcoeff_le {M : Set (ComplexModel (n + 1))}
    (hM : IsRotationInvariant M) {P : Poly (n + 1)} {C : ℝ}
    (hP : ∀ y ∈ M, ‖polyEval P y‖ ≤ C) (k : ℕ) :
    ∀ y ∈ M, ‖polyEval (mono (wcoeff P k) k) y‖ ≤ C := by
  intro y hy
  rw [polyEval_mono_wcoeff, norm_mul, norm_pow]
  apply norm_coeff_mul_pow_le _ k (norm_nonneg _)
  intro t ht
  by_cases hy0 : y 0 = 0
  · have ht0 : t = 0 := by rw [hy0, norm_zero] at ht; exact norm_eq_zero.mp ht
    have h := hP _ (hM y hy 1 (by simp))
    rw [polyEval_wscale] at h
    rw [ht0]
    rwa [hy0, mul_zero] at h
  · have hc : ‖t / y 0‖ = 1 := by
      rw [norm_div, ht, div_self (norm_ne_zero_iff.mpr hy0)]
    have h := hP _ (hM y hy _ hc)
    rwa [polyEval_wscale, div_mul_cancel₀ t hy0] at h

/-- `q^N` eventually exceeds `N · D + 1` for `q > 1`. -/
theorem exists_pow_gt_linear {q : ℝ} (hq : 1 < q) (D : ℕ) :
    ∃ N : ℕ, (N * D + 1 : ℝ) < q ^ N := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hq
  have hε : (0 : ℝ) < 1 / (D + 2) := by positivity
  obtain ⟨N₀, hN₀⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max N₀ 1, ?_⟩
  set N := max N₀ 1
  have hN := hN₀ N (le_max_left _ _)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_max_right N₀ 1
  have hqN : 0 < q ^ N := pow_pos (by linarith) N
  rw [pow_one, div_lt_div_iff₀ hqN (by positivity), one_mul] at hN
  nlinarith

/-- **Monomial separators.** If a polynomial separates `x₀` from a rotation invariant set `M`,
so does a monomial `a(z) wᵏ` (a monomial part of a power of the polynomial). -/
theorem exists_mono_separator {M : Set (ComplexModel (n + 1))} (hM : IsRotationInvariant M)
    {P : Poly (n + 1)} (hP : ∀ y ∈ M, ‖polyEval P y‖ ≤ 1) {x₀ : ComplexModel (n + 1)}
    (hx₀ : 1 < ‖polyEval P x₀‖) :
    ∃ (a : Poly n) (k : ℕ), (∀ y ∈ M, ‖polyEval (mono a k) y‖ ≤ 1) ∧
      1 < ‖polyEval (mono a k) x₀‖ := by
  classical
  set D := (MvPolynomial.finSuccEquiv ℂ n P).natDegree
  obtain ⟨N, hN⟩ := exists_pow_gt_linear hx₀ D
  have hPN : ∀ y ∈ M, ‖polyEval (P ^ N) y‖ ≤ 1 := by
    intro y hy
    have : polyEval (P ^ N) y = polyEval P y ^ N := by simp [polyEval]
    rw [this, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hP y hy)
  by_contra hcon
  push Not at hcon
  have hk : ∀ k, ‖(wslice (P ^ N) x₀).coeff k * x₀ 0 ^ k‖ ≤ 1 := by
    intro k
    by_contra hk
    push Not at hk
    have h1 := hcon (wcoeff (P ^ N) k) k (norm_polyEval_mono_wcoeff_le hM hPN k)
    rw [polyEval_mono_wcoeff] at h1
    exact absurd hk (not_lt.mpr h1)
  have hdeg : (wslice (P ^ N) x₀).natDegree ≤ N * D := by
    unfold wslice
    refine (Polynomial.natDegree_map_le).trans ?_
    rw [map_pow]
    exact Polynomial.natDegree_pow_le
  have heval : polyEval (P ^ N) x₀ = (wslice (P ^ N) x₀).eval (x₀ 0) :=
    polyEval_eq_eval_finSuccEquiv _ _
  have hsum : ‖polyEval (P ^ N) x₀‖ ≤ (N * D + 1 : ℝ) := by
    rw [heval, Polynomial.eval_eq_sum_range]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.succ_le_succ hdeg
  have : polyEval (P ^ N) x₀ = polyEval P x₀ ^ N := by simp [polyEval]
  rw [this, norm_pow] at hsum
  linarith

/-! ### Monomial polyhedra -/

/-- The open monomial polyhedron `{x : |aᵢ(z)| |w|^{kᵢ} < 1 for (aᵢ, kᵢ) ∈ S}`. -/
def monoPoly (S : Finset (Poly n × ℕ)) : Set (ComplexModel (n + 1)) :=
  {x | ∀ m ∈ S, ‖polyEval (mono m.1 m.2) x‖ < 1}

/-- The closed monomial polyhedron `{x : |aᵢ(z)| |w|^{kᵢ} ≤ 1 for (aᵢ, kᵢ) ∈ S}`. -/
def monoPolyClosed (S : Finset (Poly n × ℕ)) : Set (ComplexModel (n + 1)) :=
  {x | ∀ m ∈ S, ‖polyEval (mono m.1 m.2) x‖ ≤ 1}

theorem isOpen_monoPoly (S : Finset (Poly n × ℕ)) : IsOpen (monoPoly S) := by
  have h : monoPoly S = ⋂ m ∈ S, {x | ‖polyEval (mono m.1 m.2) x‖ < 1} := by
    ext x; simp [monoPoly]
  rw [h]
  exact isOpen_biInter_finset fun m _ =>
    isOpen_lt (continuous_polyEval _).norm continuous_const

theorem isClosed_monoPolyClosed (S : Finset (Poly n × ℕ)) : IsClosed (monoPolyClosed S) := by
  have h : monoPolyClosed S = ⋂ m ∈ S, {x | ‖polyEval (mono m.1 m.2) x‖ ≤ 1} := by
    ext x; simp [monoPolyClosed]
  rw [h]
  exact isClosed_biInter fun m _ => isClosed_le (continuous_polyEval _).norm continuous_const

theorem monoPoly_subset_monoPolyClosed (S : Finset (Poly n × ℕ)) :
    monoPoly S ⊆ monoPolyClosed S :=
  fun _ hx m hm => (hx m hm).le

theorem closure_monoPoly_subset (S : Finset (Poly n × ℕ)) :
    closure (monoPoly S) ⊆ monoPolyClosed S :=
  closure_minimal (monoPoly_subset_monoPolyClosed S) (isClosed_monoPolyClosed S)

/-- Closed monomial polyhedra are polynomially convex. -/
theorem polyHull_monoPolyClosed (S : Finset (Poly n × ℕ)) :
    polyHull (monoPolyClosed S) = monoPolyClosed S := by
  refine Subset.antisymm ?_ (subset_polyHull _)
  intro x hx m hm
  exact hx _ 1 fun y hy => hy m hm

theorem isCircular_monoPoly (S : Finset (Poly n × ℕ)) : IsCircular (monoPoly S) := by
  intro x hx c hc m hm
  have h := hx m hm
  rw [polyEval_mono] at h ⊢
  rw [zpart_wscale, wscale_zero, mul_pow, norm_mul, norm_mul, norm_pow, norm_pow]
  rw [norm_mul, norm_pow] at h
  calc ‖polyEval m.1 (zpart x)‖ * (‖c‖ ^ m.2 * ‖x 0‖ ^ m.2)
      ≤ ‖polyEval m.1 (zpart x)‖ * (1 * ‖x 0‖ ^ m.2) := by
        gcongr; exact pow_le_one₀ (norm_nonneg _) hc
    _ < 1 := by rw [one_mul]; exact h

theorem isCircular_monoPolyClosed (S : Finset (Poly n × ℕ)) : IsCircular (monoPolyClosed S) := by
  intro x hx c hc m hm
  have h := hx m hm
  rw [polyEval_mono] at h ⊢
  rw [zpart_wscale, wscale_zero, mul_pow, norm_mul, norm_mul, norm_pow, norm_pow]
  rw [norm_mul, norm_pow] at h
  calc ‖polyEval m.1 (zpart x)‖ * (‖c‖ ^ m.2 * ‖x 0‖ ^ m.2)
      ≤ ‖polyEval m.1 (zpart x)‖ * (1 * ‖x 0‖ ^ m.2) := by
        gcongr; exact pow_le_one₀ (norm_nonneg _) hc
    _ ≤ 1 := by rw [one_mul]; exact h

/-- The monomials `zᵢ / R` (`k = 0`) and `w / R` (`k = 1`), bounding a monomial polyhedron
by the closed polydisc of radius `R`. -/
def boxMonos (R : ℝ) : Finset (Poly n × ℕ) :=
  insert (MvPolynomial.C ((R : ℂ)⁻¹), 1)
    (Finset.univ.image fun i : Fin n => (MvPolynomial.C ((R : ℂ)⁻¹) * MvPolynomial.X i, 0))

theorem mem_boxMonos_bound {R : ℝ} (hR : 0 < R) {x : ComplexModel (n + 1)}
    (hx : ∀ m ∈ boxMonos (n := n) R, ‖polyEval (mono m.1 m.2) x‖ ≤ 1) (j : Fin (n + 1)) :
    ‖x j‖ ≤ R := by
  refine Fin.cases ?_ (fun i => ?_) j
  · have h := hx _ (Finset.mem_insert_self _ _)
    rw [polyEval_mono] at h
    simp only [polyEval, MvPolynomial.eval_C, pow_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hR.le] at h
    rwa [inv_mul_le_iff₀ hR, mul_one] at h
  · have h := hx _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    rw [polyEval_mono] at h
    simp only [polyEval, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      zpart_apply, pow_zero, mul_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hR.le] at h
    rwa [inv_mul_le_iff₀ hR, mul_one] at h

theorem lt_boxMonos {R : ℝ} (hR : 0 < R) {x : ComplexModel (n + 1)} (hx : ∀ j, ‖x j‖ < R) :
    ∀ m ∈ boxMonos (n := n) R, ‖polyEval (mono m.1 m.2) x‖ < 1 := by
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · rw [polyEval_mono]
    simp only [polyEval, MvPolynomial.eval_C, pow_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
    rw [inv_mul_lt_iff₀ hR, mul_one]
    exact hx 0
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hm
    rw [polyEval_mono]
    simp only [polyEval, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      zpart_apply, pow_zero, mul_one, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
    rw [inv_mul_lt_iff₀ hR, mul_one]
    exact hx i.succ

/-- The closed polydisc `{x : |xⱼ| ≤ R}` is compact. -/
theorem isCompact_closedPolydisc (R : ℝ) :
    IsCompact {x : ComplexModel (n + 1) | ∀ j, ‖x j‖ ≤ R} := by
  have hcl : IsClosed {x : ComplexModel (n + 1) | ∀ j, ‖x j‖ ≤ R} := by
    have : {x : ComplexModel (n + 1) | ∀ j, ‖x j‖ ≤ R} = ⋂ j, {x | ‖x j‖ ≤ R} := by
      ext x; simp
    rw [this]
    exact isClosed_iInter fun j =>
      isClosed_le ((EuclideanSpace.proj (𝕜 := ℂ) j).continuous.norm) continuous_const
  refine (isCompact_closedBall (0 : ComplexModel (n + 1)) (∑ _j : Fin (n + 1), R)).of_isClosed_subset
    hcl fun x hx => ?_
  rw [mem_closedBall_zero_iff]
  exact (SGPT.GAGA.Core.Box.norm_le_sum_norm x).trans (Finset.sum_le_sum fun j _ => hx j)

theorem isCompact_monoPolyClosed_union_boxMonos {R : ℝ} (hR : 0 < R)
    (S : Finset (Poly n × ℕ)) : IsCompact (monoPolyClosed (S ∪ boxMonos R)) :=
  (isCompact_closedPolydisc R).of_isClosed_subset (isClosed_monoPolyClosed _) fun _ hx =>
    mem_boxMonos_bound hR fun m hm => hx m (Finset.mem_union_right _ hm)

/-- **Monomial polyhedron neighbourhoods.** The polynomial hull of a compact rotation invariant
set `B` has a neighbourhood basis of monomial polyhedra: for every open `U ⊇ B̂` there is a
finite set `S` of monomials with `B̂ ⊆ monoPoly S ⊆ monoPolyClosed S ⊆ U`, `monoPolyClosed S`
compact. -/
theorem exists_monoPoly_nhds {B U : Set (ComplexModel (n + 1))} (hB : IsCompact B)
    (hBr : IsRotationInvariant B) (hU : IsOpen U) (hBU : polyHull B ⊆ U) :
    ∃ S : Finset (Poly n × ℕ), polyHull B ⊆ monoPoly S ∧ monoPolyClosed S ⊆ U ∧
      IsCompact (monoPolyClosed S) := by
  classical
  have hHc := isCompact_polyHull hB
  have hHr := hBr.polyHull
  obtain ⟨M₀, hM₀⟩ := hHc.exists_bound_of_continuousOn continuous_id.continuousOn
  set R : ℝ := max M₀ 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hHR : ∀ x ∈ polyHull B, ∀ j, ‖x j‖ < R := by
    intro x hx j
    have h1 : ‖x j‖ ≤ ‖x‖ := by
      exact PiLp.norm_apply_le x j
    have h2 : ‖x‖ ≤ M₀ := by simpa using hM₀ x hx
    linarith [le_max_left M₀ 0]
  set D : Set (ComplexModel (n + 1)) := {x | ∀ j, ‖x j‖ ≤ R} \ U
  have hD : IsCompact D := (isCompact_closedPolydisc R).diff hU
  have hsep : ∀ x : D, ∃ m : Poly n × ℕ, (∀ y ∈ polyHull B, ‖polyEval (mono m.1 m.2) y‖ < 1) ∧
      1 < ‖polyEval (mono m.1 m.2) x.val‖ := by
    intro x
    obtain ⟨p, hp1, hp2⟩ := exists_normalized_separator (K := B) (x := x.val)
      (fun hx => x.property.2 (hBU hx))
    obtain ⟨a, k, hak1, hak2⟩ := exists_mono_separator hHr (P := p)
      (fun y hy => (hp1 y hy).le) hp2
    set t : ℝ := (1 + ‖polyEval (mono a k) x.val‖) / 2
    have ht1 : 1 < t := by simp only [t]; linarith
    have ht2 : t < ‖polyEval (mono a k) x.val‖ := by simp only [t]; linarith
    have ht0 : 0 < t := by linarith
    refine ⟨(MvPolynomial.C ((t : ℂ)⁻¹) * a, k), ?_, ?_⟩
    · intro y hy
      have h := hak1 y hy
      rw [polyEval_mono] at h ⊢
      simp only [polyEval, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h ⊢
      rw [mul_assoc, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le,
        inv_mul_lt_iff₀ ht0]
      linarith
    · have h := ht2
      rw [polyEval_mono] at h ⊢
      simp only [polyEval, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h ⊢
      rw [mul_assoc, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0.le,
        lt_inv_mul_iff₀ ht0, mul_one]
      exact h
  choose m hm1 hm2 using hsep
  obtain ⟨s, hs⟩ := hD.elim_finite_subcover (fun x : D => {y | 1 < ‖polyEval (mono (m x).1 (m x).2) y‖})
    (fun x => isOpen_lt continuous_const (continuous_polyEval _).norm)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hm2 ⟨x, hx⟩⟩)
  refine ⟨s.image m ∪ boxMonos R, ?_, ?_, isCompact_monoPolyClosed_union_boxMonos hR _⟩
  · intro x hx q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hq
      exact hm1 y x hx
    · exact lt_boxMonos hR (hHR x hx) q hq
  · intro x hx
    by_contra hxU
    have hxD : x ∈ D := ⟨mem_boxMonos_bound hR fun q hq => hx q (Finset.mem_union_right _ hq), hxU⟩
    obtain ⟨y, hy, hyx⟩ := mem_iUnion₂.mp (hs hxD)
    have := hx (m y) (Finset.mem_union_left _ (Finset.mem_image_of_mem m hy))
    exact absurd hyx (not_lt.mpr this)

end SGPT.Unibranch.FNS
