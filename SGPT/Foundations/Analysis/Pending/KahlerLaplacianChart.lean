import SGPT.Foundations.Analysis.Pending.ManifoldContinuity
import SGPT.Foundations.Analysis.Pending.HolomorphicHessianTwo
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant
import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian
import SGPT.Foundations.Analysis.Pending.RelativeEigenvalueMax

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Laplacian of a Hermitian form as a realizable chartwise operator

For a real two-form `g` on a complex manifold `M` which is Hermitian (`(1,1)` and strictly positive
in every chart, e.g. a Kähler form `A + ddᶜφ`), with coefficient matrix `H_e(z)` in the chart `e`
(`normalizedHermitianMatrix (g.coeff e z)`), the **Laplacian** of `u` is
`Δ_g u = Re tr(H_e⁻¹ · (∂²(u ∘ e⁻¹)/∂z_j∂z̄_k))` (`chartLaplacian`, `laplacian`).  It is the
derivative of `φ ↦ log det(H + complexHessian φ)` and hence the linearisation of the complex
Monge–Ampère operator.

* `re_trace_mul_complexHessian` (**real form**): `Re tr(P · complexHessian v) = (¼ P̄) : D²v` for every
  complex matrix `P`, `P̄` acting on `ℂⁿ` as a real-linear map (`matCLM`); with `P = H⁻¹` the
  coefficient is `lapCoeff H = ¼ conj(H⁻¹)`, symmetric and positive definite for `H` positive
  definite (`lapCoeff_symm`, `lapCoeff_pos`), smooth in `z` (`contDiffOn_lapCoeff`, through
  `Ring.inverse` on `ℂⁿ →L[ℝ] ℂⁿ`).
* `chartLaplacian_eq_of_mem` (**chart independence**) for functions that are `C²` in every chart: the
  complex Hessian and `H` both transform by `Jᵀ (·) J̄` along chart transitions
  (`HolomorphicHessianTwo.complexHessian_comp_holomorphic_two`,
  `normalizedHermitianMatrix_compLinearMap`), and `tr(H⁻¹ K)` is invariant
  (`trace_inv_mul_congr`).
* `exists_chart_coeff`, `exists_atlas_coeff`: whole-space coefficients in the Schauder class, equal to
  `lapCoeff H_{e_i}` on an open `U_i ⊇ e_i(tsupport χ_i)` (cut-off combination
  `ψ a + (1 - ψ) id`; uniform ellipticity on compact sets by compactness, `exists_lapCoeff_ge`).
* `laplacian_eq_ellipticOp` (**realizability**, the hypothesis `hreal` of
  `ManifoldParametrix` / `ManifoldContinuity`), hence:
  `exists_laplacian_sub_eq` (`Δ_g - s` onto `C^{0,r}(M)` for `s > 0`),
  `eq_zero_of_laplacian_sub_eq_zero` (injective), `laplacianCLM` (bounded
  `C^{2,r}(M) → C^{0,r}(M)`), `bijective_laplacianCLM_sub`, `laplacianSubEquiv` (an isomorphism).

Blueprint: `bou:kahler-laplacian-solvability` (the realizable Laplacian); consumer: the openness step
`bou:yau-openness` of the `ε`-continuity path `(A + ddᶜφ)^N = e^{tF + εφ} A^N`, whose linearisation
at a smooth solution `φ` is `Δ_{A_φ} - ε` (TN.4 B5, linear track; agreed route I-0831 C-0054..C-0057).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff InnerProductSpace Manifold ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

open FirstPass FirstPass.MongeAmpere ComplexHessianDeterminant

variable {n : ℕ}

/-! ### Matrices acting on `ℂⁿ` as real linear maps -/

/-- The real-linear map `x ↦ P x` of a complex matrix on `ℂⁿ`. -/
def matCLM (P : Matrix (Fin n) (Fin n) ℂ) : ComplexModel n →L[ℝ] ComplexModel n :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) P).restrictScalars ℝ

theorem matCLM_apply (P : Matrix (Fin n) (Fin n) ℂ) (x : ComplexModel n) :
    matCLM P x = WithLp.toLp 2 (Matrix.mulVec P (WithLp.ofLp x)) := rfl

theorem matCLM_smul_complex (P : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x : ComplexModel n) :
    matCLM P (c • x) = c • matCLM P x :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) P).map_smul c x

theorem matCLM_coordinateVector (P : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    matCLM P (coordinateVector j) = ∑ k, P k j • coordinateVector k := by
  ext l
  simp [matCLM_apply, coordinateVector, Pi.single_apply]

theorem matCLM_mul (P P' : Matrix (Fin n) (Fin n) ℂ) :
    matCLM (P * P') = matCLM P * matCLM P' := by
  ext x : 1
  simp [matCLM, map_mul]

theorem matCLM_one : matCLM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext x : 1
  simp [matCLM, map_one]

/-- `ℝ`-linearity of `P ↦ matCLM P`. -/
def matCLMₗ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (ComplexModel n →L[ℝ] ComplexModel n) where
  toFun := matCLM
  map_add' P P' := by ext x : 1; simp [matCLM, map_add]
  map_smul' c P := by
    ext x : 1
    simp only [matCLM, RingHom.id_apply, ContinuousLinearMap.coe_restrictScalars',
      smul_apply]
    rw [show c • P = (c : ℂ) • P from (Complex.coe_smul c P).symm, map_smul,
      smul_apply, Complex.coe_smul]

/-! ### The real orthonormal basis `(e_j, i e_j)` -/

theorem orthonormal_coordinateVector : Orthonormal ℂ (coordinateVector : Fin n → ComplexModel n) := by
  exact EuclideanSpace.orthonormal_single

/-- The real orthonormal basis `(e_j, i e_j)` of `ℂⁿ`. -/
def realBasis : OrthonormalBasis (Fin n × Fin 2) ℝ (ComplexModel n) :=
  OrthonormalBasis.mk (orthonormal_unitPair_smul orthonormal_coordinateVector)
    ((orthonormal_unitPair_smul orthonormal_coordinateVector).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [finrank_real_of_complex, finrank_euclideanSpace]; simp [mul_comm])).ge

theorem realBasis_apply (p : Fin n × Fin 2) :
    realBasis p = unitPair p.2 • coordinateVector p.1 := by
  simp [realBasis]

/-! ### The trace identity -/

/-- One term of the trace identity. -/
theorem bilin_smul_add (Q : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ) (c : ℂ)
    (x y : ComplexModel n) :
    Q x (c • y) + Q (Complex.I • x) (Complex.I • (c • y)) =
      c.re * (Q x y + Q (Complex.I • x) (Complex.I • y)) +
        c.im * (Q x (Complex.I • y) - Q (Complex.I • x) y) := by
  have hc : c • y = c.re • y + c.im • (Complex.I • y) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_comm, mul_smul, Complex.coe_smul, Complex.coe_smul, smul_comm Complex.I]
  have hIc : Complex.I • (c • y) = c.re • (Complex.I • y) - c.im • y := by
    rw [hc, smul_add, smul_comm Complex.I c.re, smul_comm Complex.I c.im, smul_smul,
      Complex.I_mul_I, neg_one_smul, smul_neg, sub_eq_add_neg]
  rw [hIc, hc]
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring

/-- **The trace identity**: `Re tr(P · H(v)) = (¼ P̄) : D²v`, where `H(v)` is the complex Hessian
`(∂²v/∂z_j∂z̄_k)` and `P̄` acts on `ℂⁿ` as a real-linear map. -/
theorem re_trace_mul_complexHessian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (P : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexModel n → ℝ) (z : ComplexModel n) :
    (Matrix.trace (P * complexHessian v z)).re =
      EllipticMeanValue.hessTrace b ((1 / 4 : ℝ) • matCLM (P.map (starRingEnd ℂ)))
        (fderiv ℝ (fderiv ℝ v) z) := by
  rw [WholeSpaceMaxPrinciple.hessTrace_eq_of_orthonormalBasis b realBasis]
  set Q := fderiv ℝ (fderiv ℝ v) z with hQ
  simp only [EllipticMeanValue.hessTrace, Fintype.sum_prod_type, Fin.sum_univ_two, realBasis_apply]
  simp only [unitPair, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul,
    smul_apply, matCLM_smul_complex, matCLM_coordinateVector, map_smul,
    smul_eq_mul, map_sum, Finset.smul_sum]
  rw [Matrix.trace, Complex.re_sum]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, bilin_smul_add Q]
  simp only [Matrix.map_apply, Complex.conj_re, Complex.conj_im, complexHessian,
    ← realHessian_eq_fderiv, hQ, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  ring

/-! ### Hermitian matrices: symmetry, positivity, inverse -/

theorem inner_matCLM_of_isHermitian {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (u v : ComplexModel n) : ⟪matCLM P u, v⟫_ℝ = ⟪u, matCLM P v⟫_ℝ := by
  rw [real_inner_eq_re, real_inner_eq_re]
  congr 1
  have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) = Matrix.toEuclideanCLM (𝕜 := ℂ) P := by
    rw [← map_star, Matrix.star_eq_conjTranspose, hP.eq]
  have h := ContinuousLinearMap.adjoint_inner_left (Matrix.toEuclideanCLM (𝕜 := ℂ) P) v u
  rw [← ContinuousLinearMap.star_eq_adjoint, hstar] at h
  exact h

theorem inner_matCLM_self_pos {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) {v : ComplexModel n}
    (hv : v ≠ 0) : 0 < ⟪matCLM P v, v⟫_ℝ := by
  rw [real_inner_eq_re, EuclideanSpace.inner_eq_star_dotProduct]
  have hv' : WithLp.ofLp v ≠ 0 := by
    intro h; apply hv; ext i; simpa using congrFun h i
  have h := hP.dotProduct_mulVec_pos hv'
  have h2 : WithLp.ofLp v ⬝ᵥ star (WithLp.ofLp (matCLM P v)) =
      star (star (WithLp.ofLp v) ⬝ᵥ P.mulVec (WithLp.ofLp v)) := by
    rw [← Matrix.star_dotProduct, dotProduct_comm]
    simp [matCLM_apply]
  rw [h2, Complex.star_def, Complex.conj_re]
  exact (Complex.pos_iff.mp h).1

theorem isHermitian_map_conj {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian) :
    (P.map (starRingEnd ℂ)).IsHermitian := by
  ext j k
  have := congrFun (congrFun hP.eq j) k
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at this ⊢
  rw [← this]
  simp

theorem map_conj_eq_transpose {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian) :
    P.map (starRingEnd ℂ) = Pᵀ := by
  ext j k
  have := congrFun (congrFun hP.eq k) j
  simp only [Matrix.conjTranspose_apply] at this
  simp [← this]

theorem posDef_map_conj {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    (P.map (starRingEnd ℂ)).PosDef := by
  rw [map_conj_eq_transpose hP.isHermitian]
  exact hP.transpose

/-- `P ↦ matCLM (conj P)` is multiplicative. -/
theorem matCLM_map_conj_mul (P P' : Matrix (Fin n) (Fin n) ℂ) :
    matCLM ((P * P').map (starRingEnd ℂ)) =
      matCLM (P.map (starRingEnd ℂ)) * matCLM (P'.map (starRingEnd ℂ)) := by
  rw [Matrix.map_mul, matCLM_mul]

theorem matCLM_map_conj_one :
    matCLM ((1 : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ)) = 1 := by
  rw [Matrix.map_one _ (map_zero _) (map_one _), matCLM_one]

/-- `matCLM (conj H⁻¹)` is the ring inverse of `matCLM (conj H)`. -/
theorem matCLM_map_conj_inv {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) :
    matCLM ((H⁻¹).map (starRingEnd ℂ)) = Ring.inverse (matCLM (H.map (starRingEnd ℂ))) := by
  let u : (ComplexModel n →L[ℝ] ComplexModel n)ˣ :=
    ⟨matCLM (H.map (starRingEnd ℂ)), matCLM ((H⁻¹).map (starRingEnd ℂ)),
      by rw [← matCLM_map_conj_mul, Matrix.mul_nonsing_inv _ hH, matCLM_map_conj_one],
      by rw [← matCLM_map_conj_mul, Matrix.nonsing_inv_mul _ hH, matCLM_map_conj_one]⟩
  have h : Ring.inverse (u : ComplexModel n →L[ℝ] ComplexModel n) = ↑u⁻¹ := Ring.inverse_unit u
  exact h.symm

/-- The coefficient of the Laplacian of a Hermitian matrix `H`: `a = ¼ · conj(H⁻¹)`, acting on `ℂⁿ`
as a real-linear map, so that `Re tr(H⁻¹ · complexHessian v) = a : D²v`. -/
def lapCoeff (H : Matrix (Fin n) (Fin n) ℂ) : ComplexModel n →L[ℝ] ComplexModel n :=
  (1 / 4 : ℝ) • matCLM ((H⁻¹).map (starRingEnd ℂ))

theorem re_trace_inv_mul_complexHessian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (H : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexModel n → ℝ) (z : ComplexModel n) :
    (Matrix.trace (H⁻¹ * complexHessian v z)).re =
      EllipticMeanValue.hessTrace b (lapCoeff H) (fderiv ℝ (fderiv ℝ v) z) :=
  re_trace_mul_complexHessian b H⁻¹ v z

theorem lapCoeff_symm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (u v : ComplexModel n) :
    ⟪lapCoeff H u, v⟫_ℝ = ⟪u, lapCoeff H v⟫_ℝ := by
  simp only [lapCoeff, smul_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [inner_matCLM_of_isHermitian (isHermitian_map_conj hH.inv)]

theorem lapCoeff_pos {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {v : ComplexModel n}
    (hv : v ≠ 0) : 0 < ⟪lapCoeff H v, v⟫_ℝ := by
  simp only [lapCoeff, smul_apply, inner_smul_left, RCLike.conj_to_real]
  exact mul_pos (by norm_num) (inner_matCLM_self_pos (posDef_map_conj hH.inv) hv)

theorem lapCoeff_eq_inverse {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) :
    lapCoeff H = (1 / 4 : ℝ) • Ring.inverse (matCLM (H.map (starRingEnd ℂ))) := by
  rw [lapCoeff, matCLM_map_conj_inv hH]

/-- `matCLM` through the real and imaginary parts of the entries. -/
theorem matCLM_eq_sum (P : Matrix (Fin n) (Fin n) ℂ) :
    matCLM P = ∑ j, ∑ k, ((P j k).re • matCLM (Matrix.single j k 1) +
      (P j k).im • matCLM (Matrix.single j k Complex.I)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single P]
  have hs : ∀ j k, Matrix.single j k (P j k) =
      (P j k).re • Matrix.single j k (1 : ℂ) + (P j k).im • Matrix.single j k Complex.I := by
    intro j k
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    conv_lhs => rw [← Complex.re_add_im (P j k)]
    simp [Complex.real_smul]
  simp_rw [hs]
  change matCLMₗ _ = _
  simp only [map_sum, map_add, map_smul]
  rfl

theorem isUnit_matCLM_map_conj {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsUnit H.det) :
    IsUnit (matCLM (H.map (starRingEnd ℂ))) :=
  ⟨⟨matCLM (H.map (starRingEnd ℂ)), matCLM ((H⁻¹).map (starRingEnd ℂ)),
      by rw [← matCLM_map_conj_mul, Matrix.mul_nonsing_inv _ hH, matCLM_map_conj_one],
      by rw [← matCLM_map_conj_mul, Matrix.nonsing_inv_mul _ hH, matCLM_map_conj_one]⟩, rfl⟩

/-! ### Smoothness of the coefficient of a smooth field of two-forms -/

theorem re_map_conj_normalizedHermitianMatrix (A : CoordinateRealTwoForm n) (j k : Fin n) :
    ((normalizedHermitianMatrix A).map (starRingEnd ℂ) j k).re =
      Real.pi * A ![coordinateVector j, Complex.I • coordinateVector k] := by
  simp [normalizedHermitianMatrix, Complex.mul_re]

theorem im_map_conj_normalizedHermitianMatrix (A : CoordinateRealTwoForm n) (j k : Fin n) :
    ((normalizedHermitianMatrix A).map (starRingEnd ℂ) j k).im =
      Real.pi * A ![coordinateVector j, coordinateVector k] := by
  simp [normalizedHermitianMatrix, Complex.mul_im]

/-- Evaluation of a smooth field of two-forms on fixed vectors is smooth. -/
theorem contDiffOn_apply {F : ComplexModel n → CoordinateRealTwoForm n} {U : Set (ComplexModel n)}
    {m : WithTop ℕ∞} (hF : ContDiffOn ℝ m F U) (w : Fin 2 → ComplexModel n) :
    ContDiffOn ℝ m (fun z => F z w) U :=
  (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ w).contDiff.comp_contDiffOn hF

/-- The real-linear map of `conj H(F z)` depends smoothly on `z`. -/
theorem contDiffOn_matCLM_map_conj {F : ComplexModel n → CoordinateRealTwoForm n}
    {U : Set (ComplexModel n)} {m : WithTop ℕ∞} (hF : ContDiffOn ℝ m F U) :
    ContDiffOn ℝ m
      (fun z => matCLM ((normalizedHermitianMatrix (F z)).map (starRingEnd ℂ))) U := by
  have h : (fun z => matCLM ((normalizedHermitianMatrix (F z)).map (starRingEnd ℂ))) = fun z =>
      ∑ j, ∑ k, ((Real.pi * F z ![coordinateVector j, Complex.I • coordinateVector k]) •
        matCLM (Matrix.single j k 1) + (Real.pi * F z ![coordinateVector j, coordinateVector k]) •
          matCLM (Matrix.single j k Complex.I)) := by
    funext z
    rw [matCLM_eq_sum]
    simp only [re_map_conj_normalizedHermitianMatrix, im_map_conj_normalizedHermitianMatrix]
  rw [h]
  refine ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => ?_
  exact (((contDiffOn_apply hF _).const_smul Real.pi).smul contDiffOn_const).add
    (((contDiffOn_apply hF _).const_smul Real.pi).smul contDiffOn_const)

/-- **The coefficient `¼ conj(H⁻¹)` of a smooth field of nondegenerate two-forms is smooth.** -/
theorem contDiffOn_lapCoeff {F : ComplexModel n → CoordinateRealTwoForm n}
    {U : Set (ComplexModel n)} (hU : IsOpen U) {m : WithTop ℕ∞} (hF : ContDiffOn ℝ m F U)
    (hdet : ∀ z ∈ U, IsUnit (normalizedHermitianMatrix (F z)).det) :
    ContDiffOn ℝ m (fun z => lapCoeff (normalizedHermitianMatrix (F z))) U := by
  have h1 : ContDiffOn ℝ m (fun z => (1 / 4 : ℝ) •
      Ring.inverse (matCLM ((normalizedHermitianMatrix (F z)).map (starRingEnd ℂ)))) U := by
    refine ContDiffOn.const_smul _ fun z hz => ?_
    obtain ⟨u, hu⟩ := isUnit_matCLM_map_conj (hdet z hz)
    have hinv : ContDiffAt ℝ m Ring.inverse
        (matCLM ((normalizedHermitianMatrix (F z)).map (starRingEnd ℂ))) := by
      rw [← hu]; exact contDiffAt_ringInverse ℝ u
    exact (hinv.comp z ((contDiffOn_matCLM_map_conj hF).contDiffAt
      (hU.mem_nhds hz))).contDiffWithinAt
  exact h1.congr fun z hz => lapCoeff_eq_inverse (hdet z hz)

/-! ### The Laplacian of a Hermitian form on a complex manifold -/

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The Laplacian of the real two-form `g` in the chart `e`:
`Δ_e v(z) = Re tr(H_e(z)⁻¹ · (∂²v/∂z_j∂z̄_k)(z))`, `H_e(z)` the coefficient matrix of `g` in `e`. -/
def chartLaplacian (g : SmoothRealForm n M 2) (e : ComplexChart n M) (v : ComplexModel n → ℝ)
    (z : ComplexModel n) : ℝ :=
  (Matrix.trace ((normalizedHermitianMatrix (g.coeff e z))⁻¹ * complexHessian v z)).re

/-- **The Laplacian of `g`** on `M`, read in the preferred chart at each point. -/
def laplacian (g : SmoothRealForm n M 2) (u : M → ℝ) (y : M) : ℝ :=
  chartLaplacian g (complexChartAt (n := n) y) (fun w => u ((complexChartAt (n := n) y).val.symm w))
    ((complexChartAt (n := n) y).val y)

/-- The chart Laplacian in real form: `Δ_e v = a_e : D²v` with `a_e = ¼ conj(H_e⁻¹)`. -/
theorem chartLaplacian_eq_hessTrace {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (ComplexModel n)) (g : SmoothRealForm n M 2) (e : ComplexChart n M)
    (v : ComplexModel n → ℝ) (z : ComplexModel n) :
    chartLaplacian g e v z = EllipticMeanValue.hessTrace b
      (lapCoeff (normalizedHermitianMatrix (g.coeff e z))) (fderiv ℝ (fderiv ℝ v) z) :=
  re_trace_inv_mul_complexHessian b _ v z

/-- The `ℂ`-linear derivative of a chart transition. -/
def transitionLinear (e f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) : ComplexModel n →ₗ[ℂ] ComplexModel n where
  toFun := chartTransitionDerivative e f z
  map_add' := map_add _
  map_smul' c v := chartTransitionDerivative_complex_smul e f z hz c v

theorem coeff_eq_compLinearMap (g : SmoothRealForm n M 2) (e f : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ (chartTransition e f).source) :
    g.coeff e z = compLinearMap (g.coeff f (chartTransition e f z))
      (transitionLinear e f hz) := by
  ext v
  rw [g.compatible e f z hz v]
  rfl

theorem standardMatrix_transitionLinear (e f : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    standardMatrix (transitionLinear e f hz) =
      HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) z := by
  ext p j
  rw [standardMatrix_apply]
  rfl

/-- The Jacobian matrix of a chart transition is invertible. -/
theorem isUnit_det_jacobianMatrix (e f : ComplexChart n M) {y : M} (hye : y ∈ e.val.source)
    (hyf : y ∈ f.val.source) :
    IsUnit (HolomorphicMixedDensity.jacobianMatrix (chartTransition e f) (e.val y)).det := by
  have hz := RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  rw [← standardMatrix_transitionLinear e f hz, det_standardMatrix]
  refine LinearMap.isUnit_det _ ((Module.End.isUnit_iff _).mpr ?_)
  exact RelativeEigenvalueMax.chartTransitionDerivative_bijective hye hyf

theorem complexHessian_congr' {a b : ComplexModel n → ℝ} {z : ComplexModel n}
    (hab : a =ᶠ[𝓝 z] b) : complexHessian a z = complexHessian b z := by
  have h2 : iteratedFDeriv ℝ 2 a z = iteratedFDeriv ℝ 2 b z :=
    (hab.iteratedFDeriv ℝ 2).self_of_nhds
  ext j k
  simp [complexHessian, realHessian, h2]

end Manifold

/-- The congruence `H ↦ Jᵀ H J̄` does not change `tr(H⁻¹ K)`. -/
theorem trace_inv_mul_congr {J H K : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) :
    (((Jᵀ * H * J.map (starRingEnd ℂ))⁻¹ * (Jᵀ * K * J.map (starRingEnd ℂ)))).trace =
      (H⁻¹ * K).trace := by
  have hA : IsUnit (Jᵀ).det := by rwa [Matrix.det_transpose]
  have hC : IsUnit (J.map (starRingEnd ℂ)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hJ.map _
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have h1 : (J.map (starRingEnd ℂ))⁻¹ * (H⁻¹ * (Jᵀ)⁻¹) * (Jᵀ * K * J.map (starRingEnd ℂ)) =
      (J.map (starRingEnd ℂ))⁻¹ * (H⁻¹ * ((Jᵀ)⁻¹ * Jᵀ) * K * J.map (starRingEnd ℂ)) := by
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hC, Matrix.mul_one]

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Chart independence of the Laplacian** of a Hermitian form `g`, for functions that are `C²` in
every chart. -/
theorem chartLaplacian_eq_of_mem {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target)
    {e f : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) (hyf : y ∈ f.val.source) :
    chartLaplacian g e (fun w => u (e.val.symm w)) (e.val y) =
      chartLaplacian g f (fun w => u (f.val.symm w)) (f.val y) := by
  set τ := chartTransition e f with hτ
  have hz : e.val y ∈ τ.source := RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  have hτz : τ (e.val y) = f.val y := RelativeEigenvalueMax.chartTransition_apply_chart hye
  -- the Hessians
  have hev : (fun w => u (e.val.symm w)) =ᶠ[𝓝 (e.val y)]
      (fun w => (fun x => u (f.val.symm x)) (τ w)) := by
    filter_upwards [τ.open_source.mem_nhds hz] with w hw
    have hw2 : e.val.symm w ∈ f.val.source := hw.2
    show u (e.val.symm w) = u (f.val.symm (f.val (e.val.symm w)))
    rw [f.val.left_inv hw2]
  have hτhol : ContDiffOn ℂ ∞ τ τ.source := fun w hw =>
    (HolomorphicMaps.chartTransition_contDiffAt e f hw).contDiffWithinAt
  have hmaps : MapsTo τ τ.source f.val.target := fun w hw => (τ.map_source hw).1
  have hHess := HolomorphicHessianTwo.complexHessian_comp_holomorphic_two τ.open_source
    f.val.open_target hτhol (hu f) hmaps hz
  -- the coefficient matrices
  have hf11 : IsOneOne (g.coeff f (τ (e.val y))) := (hg f _ (hmaps hz)).1
  have hH : normalizedHermitianMatrix (g.coeff e (e.val y)) =
      (HolomorphicMixedDensity.jacobianMatrix τ (e.val y))ᵀ *
        normalizedHermitianMatrix (g.coeff f (τ (e.val y))) *
          (HolomorphicMixedDensity.jacobianMatrix τ (e.val y)).map (starRingEnd ℂ) := by
    rw [coeff_eq_compLinearMap g e f hz, normalizedHermitianMatrix_compLinearMap hf11,
      standardMatrix_transitionLinear]
  simp only [chartLaplacian]
  rw [complexHessian_congr' hev, hHess, hH, trace_inv_mul_congr (isUnit_det_jacobianMatrix e f hye hyf),
    hτz]

/-- The Laplacian on `M` is computed in any chart. -/
theorem laplacian_eq {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {u : M → ℝ}
    (hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target)
    {e : ComplexChart n M} {y : M} (hye : y ∈ e.val.source) :
    laplacian g u y = chartLaplacian g e (fun w => u (e.val.symm w)) (e.val y) :=
  chartLaplacian_eq_of_mem hg hu (mem_complexChartAt_source y) hye

end Manifold

/-! ### Whole-space coefficients in the charts of a Hölder atlas -/

/-- A `C^∞` cut-off with values in `[0, 1]`, equal to `1` on a compact `K`, with compact support
inside an open `U ⊇ K`. -/
theorem exists_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧ (∀ x ∈ K, ρ x = 1) ∧
      ∀ x, ρ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ρ, hρ1, hρV, hρI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (n := (⊤ : ℕ∞))
    𝓘(ℝ, E) hK.isClosed (by rwa [hVo.interior_eq])
  have hρsupp : support (ρ : E → ℝ) ⊆ V := fun x hx => by
    by_contra hxV
    exact hx (hρV x hxV)
  exact ⟨ρ, ρ.contMDiff.contDiff,
    HasCompactSupport.of_support_subset_isCompact hVc (hρsupp.trans subset_closure),
    (closure_mono hρsupp).trans hVU, fun x hx => hρ1.self_of_nhdsSet x hx, hρI⟩

/-- `ψ • f` is smooth on the whole space if `f` is smooth on an open set containing `tsupport ψ`. -/
theorem contDiff_smul_of_tsupport {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {m : WithTop ℕ∞} {ψ : E → ℝ} {f : E → F}
    {U : Set E} (hU : IsOpen U) (hψ : ContDiff ℝ m ψ) (hsupp : tsupport ψ ⊆ U)
    (hf : ContDiffOn ℝ m f U) : ContDiff ℝ m (fun x => ψ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hψ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have h0 : ψ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hsupp h)
    refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

theorem isEllipticCoeff_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a : E → E →L[ℝ] E} {lam Λ lam' Λ' α : ℝ} (ha : SchauderBlowup.IsEllipticCoeff a lam Λ α)
    (hlam : lam' ≤ lam) (hΛ : Λ ≤ Λ') :
    SchauderBlowup.IsEllipticCoeff a lam' Λ' α where
  symm := ha.symm
  elliptic x v := (mul_le_mul_of_nonneg_right hlam (sq_nonneg _)).trans (ha.elliptic x v)
  bound x := (ha.bound x).trans hΛ
  holder x y := (ha.holder x y).trans
    (mul_le_mul_of_nonneg_right hΛ (Real.rpow_nonneg (norm_nonneg _) _))

section Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

theorem posDef_coeff {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {e : ComplexChart n M}
    {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (normalizedHermitianMatrix (g.coeff e z)).PosDef :=
  ConcentrationMassComparison.normalizedHermitianMatrix_posDef (hg e z hz).1 (hg e z hz).2

/-- **Uniform ellipticity on compact sets**: `⟪a_e(z) v, v⟫ ≥ λ ‖v‖²` for `z` in a compact subset of
the chart target. -/
theorem exists_lapCoeff_ge {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ K, ∀ v : ComplexModel n,
      lam * ‖v‖ ^ 2 ≤ ⟪lapCoeff (normalizedHermitianMatrix (g.coeff e z)) v, v⟫_ℝ := by
  set a0 := fun z => lapCoeff (normalizedHermitianMatrix (g.coeff e z)) with ha0def
  have ha0 : ContDiffOn ℝ ∞ a0 e.val.target :=
    contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun z hz =>
      isUnit_iff_ne_zero.mpr (posDef_coeff hg hz).det_pos.ne'
  set S := K ×ˢ sphere (0 : ComplexModel n) 1 with hSdef
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun p : ComplexModel n × ComplexModel n => ⟪a0 p.1 p.2, p.2⟫_ℝ) S := by
    have h1 : ContinuousOn (fun p : ComplexModel n × ComplexModel n => a0 p.1) S :=
      (ha0.continuousOn.mono hKt).comp continuousOn_fst fun p hp => hp.1
    exact (h1.clm_apply continuousOn_snd).inner continuousOn_snd
  have hscale : ∀ z v, v ≠ 0 → ⟪a0 z v, v⟫_ℝ = ‖v‖ ^ 2 * ⟪a0 z (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫_ℝ := by
    intro z v hv
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    field_simp
  have hmem : ∀ z ∈ K, ∀ v : ComplexModel n, v ≠ 0 → (z, ‖v‖⁻¹ • v) ∈ S := by
    intro z hz v hv
    refine ⟨hz, ?_⟩
    simp [norm_smul, norm_ne_zero_iff.mpr hv]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z hz v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have := hmem z hz v hv
      rw [hSe] at this
      exact this.elim
  · obtain ⟨p, hpS, hpmin⟩ := hS.exists_isMinOn hSne hcont
    have hp2 : p.2 ≠ 0 := by
      intro h0
      have := hpS.2
      rw [h0] at this
      simp at this
    refine ⟨⟪a0 p.1 p.2, p.2⟫_ℝ, lapCoeff_pos (posDef_coeff hg (hKt hpS.1)) hp2,
      fun z hz v => ?_⟩
    by_cases hv : v = 0
    · simp [hv]
    · have h := hpmin (hmem z hz v hv)
      simp only [Set.mem_ofPred_eq] at h
      rw [show (⟪lapCoeff (normalizedHermitianMatrix (g.coeff e z)) v, v⟫_ℝ) = ⟪a0 z v, v⟫_ℝ from rfl,
        hscale z v hv, mul_comm]
      exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- **Whole-space coefficients for one chart**: on a neighbourhood `U` of a compact `K` in the chart
target, `a = ¼ conj(H_e⁻¹)`; elsewhere the cut-off convex combination `ψ a_e + (1 - ψ) id`, which is
in the Schauder class. -/
theorem exists_chart_coeff {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    ∃ (lam Λ : ℝ) (a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
      (U : Set (ComplexModel n)),
      0 < lam ∧ SchauderBlowup.IsEllipticCoeff a lam Λ r ∧ IsOpen U ∧ K ⊆ U ∧
        U ⊆ e.val.target ∧ ∀ z ∈ U, a z = lapCoeff (normalizedHermitianMatrix (g.coeff e z)) := by
  obtain ⟨K', hK'c, hKK', hK't⟩ := exists_compact_between hK e.val.open_target hKt
  obtain ⟨ψ, hψs, hψc, hψt, hψ1, hψI⟩ := exists_cutoff hK'c e.val.open_target hK't
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n,
      a0 = fun z => lapCoeff (normalizedHermitianMatrix (g.coeff e z)) := ⟨_, rfl⟩
  have ha0 : ContDiffOn ℝ ∞ a0 e.val.target := by
    rw [ha0def]
    exact contDiffOn_lapCoeff e.val.open_target (g.smooth e) fun z hz =>
      isUnit_iff_ne_zero.mpr (posDef_coeff hg hz).det_pos.ne'
  obtain ⟨d, hddef⟩ : ∃ d : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n,
      d = fun z => ψ z • (a0 z - ContinuousLinearMap.id ℝ (ComplexModel n)) := ⟨_, rfl⟩
  have hd : ContDiff ℝ ∞ d := by
    rw [hddef]
    exact contDiff_smul_of_tsupport e.val.open_target hψs hψt (ha0.sub contDiffOn_const)
  have hdc : HasCompactSupport d := by
    refine hψc.mono' fun z hz => subset_tsupport _ fun h0 => hz ?_
    rw [hddef]
    show ψ z • (a0 z - ContinuousLinearMap.id ℝ (ComplexModel n)) = 0
    rw [h0]
    exact zero_smul ℝ (a0 z - ContinuousLinearMap.id ℝ (ComplexModel n))
  obtain ⟨Kd, hKd0, hKdb, hKdl⟩ :=
    ManifoldSchauder.exists_lipschitz_of_hasCompactSupport (hd.of_le (by simp)) hdc
  obtain ⟨lam0, hlam0, hlam0le⟩ := exists_lapCoeff_ge hg e hψc.isCompact hψt
  have hψ0 : ∀ z, z ∉ tsupport ψ → ψ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  obtain ⟨a, hadef⟩ : ∃ a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n,
      a = fun z => ContinuousLinearMap.id ℝ (ComplexModel n) + d z := ⟨_, rfl⟩
  have happ : ∀ z v, a z v = v + ψ z • (a0 z v - v) := by
    intro z v
    rw [hadef, hddef]
    simp
  have hsymm : ∀ x u v, ⟪a x u, v⟫_ℝ = ⟪u, a x v⟫_ℝ := by
    intro x u v
    rw [happ, happ]
    by_cases hx : x ∈ tsupport ψ
    · have hs : ⟪a0 x u, v⟫_ℝ = ⟪u, a0 x v⟫_ℝ := by
        rw [ha0def]
        exact lapCoeff_symm (posDef_coeff hg (hψt hx)).isHermitian u v
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, RCLike.conj_to_real, hs]
    · simp [hψ0 x hx]
  have hell : ∀ x v, min lam0 1 * ‖v‖ ^ 2 ≤ ⟪a x v, v⟫_ℝ := by
    intro x v
    rw [happ]
    have hvv : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    by_cases hx : x ∈ tsupport ψ
    · simp only [inner_add_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real, hvv]
      have h1 : lam0 * ‖v‖ ^ 2 ≤ ⟪a0 x v, v⟫_ℝ := by rw [ha0def]; exact hlam0le x hx v
      obtain ⟨hψa, hψb⟩ := hψI x
      have hm1 : min lam0 1 ≤ lam0 := min_le_left _ _
      have hm2 : min lam0 1 ≤ 1 := min_le_right _ _
      have hv2 := sq_nonneg ‖v‖
      nlinarith [mul_nonneg hψa hv2, mul_nonneg (sub_nonneg.mpr hψb) hv2,
        mul_le_mul_of_nonneg_right hm1 hv2, mul_le_mul_of_nonneg_right hm2 hv2]
    · simp only [hψ0 x hx, zero_smul, add_zero, hvv]
      exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)
  have hbd : ∀ x, ‖a x‖ ≤ 1 + 3 * Kd := by
    intro x
    rw [hadef]
    calc ‖ContinuousLinearMap.id ℝ (ComplexModel n) + d x‖
        ≤ ‖ContinuousLinearMap.id ℝ (ComplexModel n)‖ + ‖d x‖ := norm_add_le _ _
      _ ≤ 1 + Kd := add_le_add (ContinuousLinearMap.norm_id_le) (hKdb x)
      _ ≤ 1 + 3 * Kd := by linarith
  have hhol : ∀ x y, ‖a x - a y‖ ≤ (1 + 3 * Kd) * ‖x - y‖ ^ r := by
    intro x y
    have h := SchauderWholeSpace.norm_sub_le_rpow_of_lipschitz_of_bound hKd0 hr0 hr1 hKdl hKdb x y
    have hxy : a x - a y = d x - d y := by rw [hadef]; simp
    rw [hxy]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))
  refine ⟨min lam0 1, 1 + 3 * Kd, a, interior K', lt_min hlam0 one_pos, ⟨hsymm, hell, hbd, hhol⟩,
    isOpen_interior, hKK', interior_subset.trans hK't, fun z hz => ?_⟩
  have hz' : z ∈ K' := interior_subset hz
  rw [hadef, hddef]
  simp only [hψ1 z hz', one_smul]
  rw [ha0def]
  abel

end Manifold

/-! ### The Laplacian on `C^{2,r}(M)`: realizability, solvability, invertibility -/

section Atlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

open SchauderBlowup SchauderWholeSpace HolderAtlas.HolderMap

theorem image_tsupport_subset_target (A : HolderAtlas n M) (i : Fin A.m) :
    (A.chart i).val '' tsupport (A.χ i) ⊆ (A.chart i).val.target := by
  rintro _ ⟨y, hy, rfl⟩
  exact (A.chart i).val.map_source (A.tsupport_subset i hy)

/-- **Whole-space Schauder coefficients** for the Laplacian of `g` in the charts of a Hölder atlas:
`a_i = ¼ conj(H_{e_i}⁻¹)` on an open `U_i ⊇ e_i(tsupport χ_i)`. -/
theorem exists_atlas_coeff {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (A : HolderAtlas n M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ (lam Λ : ℝ) (a : Fin A.m → ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n)
      (U : Fin A.m → Set (ComplexModel n)), 0 < lam ∧ 0 ≤ Λ ∧
      (∀ i, IsEllipticCoeff (a i) lam Λ r) ∧ (∀ i, IsOpen (U i)) ∧
      (∀ i, (A.chart i).val '' tsupport (A.χ i) ⊆ U i) ∧ (∀ i, U i ⊆ (A.chart i).val.target) ∧
      ∀ i, ∀ z ∈ U i, a i z = lapCoeff (normalizedHermitianMatrix (g.coeff (A.chart i) z)) := by
  have key := fun i => exists_chart_coeff hg (A.chart i) (A.isCompact_image_tsupport i)
    (image_tsupport_subset_target A i) hr0 hr1
  choose lam Λ a U hlam ha hU hKU hUt heq using key
  have hΛ0 : ∀ i, 0 ≤ Λ i := fun i => (norm_nonneg _).trans ((ha i).bound 0)
  set lam' : ℝ := 1 / (1 + ∑ i, 1 / lam i) with hlam'
  have hsum0 : 0 ≤ ∑ i, 1 / lam i := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hlam i)).le
  have hlam'0 : 0 < lam' := one_div_pos.mpr (by linarith)
  have hlam'le : ∀ i, lam' ≤ lam i := by
    intro i
    have h1 : 1 / lam i ≤ 1 + ∑ j, 1 / lam j := by
      have := Finset.single_le_sum (f := fun j => 1 / lam j)
        (fun j _ => (one_div_pos.mpr (hlam j)).le) (Finset.mem_univ i)
      linarith
    rw [hlam', div_le_iff₀ (by linarith)]
    have := (div_le_iff₀ (hlam i)).mp h1
    linarith [mul_comm (lam i) (1 + ∑ j, 1 / lam j)]
  refine ⟨lam', ∑ i, Λ i, a, U, hlam'0, Finset.sum_nonneg fun i _ => hΛ0 i,
    fun i => isEllipticCoeff_mono (ha i) (hlam'le i) (Finset.single_le_sum (fun j _ => hΛ0 j) (Finset.mem_univ i)),
    hU, hKU, hUt, heq⟩

/-- **Realizability**: in the chart `e_i`, on `U_i`, the Laplacian of `u ∈ C^{2,r}(M)` is the
whole-space operator `a_i : D²` applied to `u ∘ e_i⁻¹`. -/
theorem laplacian_eq_ellipticOp {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (ComplexModel n))
    {g : SmoothRealForm n M 2} (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr1 : r ≤ 1)
    (u : A.HolderMap 2 r ℝ) (i : Fin A.m)
    {a : ComplexModel n → ComplexModel n →L[ℝ] ComplexModel n} {U : Set (ComplexModel n)}
    (hUt : U ⊆ (A.chart i).val.target)
    (heq : ∀ z ∈ U, a z = lapCoeff (normalizedHermitianMatrix (g.coeff (A.chart i) z)))
    {z : ComplexModel n} (hz : z ∈ U) :
    laplacian g u ((A.chart i).val.symm z) =
      ellipticOp b a (fun _ => 0) (fun _ => 0) (fun w => u ((A.chart i).val.symm w)) z := by
  have hu : ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun w => u (e.val.symm w)) e.val.target :=
    fun e z hz => (ManifoldContinuity.contDiffAt_comp_symm hr1 u e hz).contDiffWithinAt
  rw [laplacian_eq hg hu ((A.chart i).val.map_target (hUt hz)), (A.chart i).val.right_inv (hUt hz),
    chartLaplacian_eq_hessTrace b, ← heq z hz, ellipticOp_zero]

/-- **`Δ_g - s` is onto `C^{0,r}(M)`** for every `s > 0`, `g` a Hermitian form on a compact complex
manifold (blueprint `bou:kahler-laplacian-solvability`; the linearisation of the
`ε`-continuity path of Yau's theorem). -/
theorem exists_laplacian_sub_eq [CompactSpace M] {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (A : HolderAtlas n M) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {s : ℝ} (hs : 0 < s)
    (f : A.HolderMap 0 r ℝ) :
    ∃ u : A.HolderMap 2 r ℝ, ∀ y, laplacian g u y - s * u y = f y := by
  obtain ⟨lam, Λ, a, U, hlam, hΛ, ha, hU, hKU, hUt, heq⟩ :=
    exists_atlas_coeff hg A (r := r) r.2 hr1.le
  have hreal : ∀ u : A.HolderMap 2 r ℝ, ∃ G : M → ℝ, ∀ i, ∀ z ∈ U i,
      G ((A.chart i).val.symm z) = ellipticOp realBasis (a i) ((fun _ _ => 0) i)
        ((fun _ _ => 0) i) (fun w => u ((A.chart i).val.symm w)) z :=
    fun u => ⟨laplacian g u, fun i z hz =>
      laplacian_eq_ellipticOp realBasis hg hr1.le u i (hUt i) (heq i) hz⟩
  obtain ⟨u, hu⟩ := ManifoldContinuity.exists_ellipticOp_sub_eq realBasis hlam hr0 hr1 a
    (fun _ _ => 0) (fun _ _ => 0) ha (fun _ => isLowerCoeff_zero hΛ) (fun _ _ => le_rfl) U hU hKU
    hUt hreal hs f
  refine ⟨u, fun y => ?_⟩
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, A.χ i y ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [A.sum_eq_one]; exact one_ne_zero)
  have hys : y ∈ (A.chart i).val.source := A.tsupport_subset i (subset_tsupport _ hi)
  have hz : (A.chart i).val y ∈ U i := hKU i ⟨y, subset_tsupport _ hi, rfl⟩
  have h1 := hu i _ hz
  rw [← laplacian_eq_ellipticOp realBasis hg hr1.le u i (hUt i) (heq i) hz,
    (A.chart i).val.left_inv hys] at h1
  exact h1

/-- **Uniqueness**: `Δ_g u = s u` with `s > 0` forces `u = 0` (maximum principle). -/
theorem eq_zero_of_laplacian_sub_eq_zero [CompactSpace M] {g : SmoothRealForm n M 2}
    (hg : g.IsHermitian) {A : HolderAtlas n M} {r : ℝ≥0} (hr1 : r ≤ 1) {s : ℝ} (hs : 0 < s)
    (u : A.HolderMap 2 r ℝ) (h : ∀ y, laplacian g u y - s * u y = 0) : u = 0 := by
  obtain ⟨lam, Λ, a, U, hlam, hΛ, ha, hU, hKU, hUt, heq⟩ :=
    exists_atlas_coeff hg A (r := r) r.2 hr1
  ext y
  have key := ManifoldMaxPrinciple.mul_abs_le_of_chartOp_sub realBasis hr1 (β := fun _ _ => 0)
    (c := fun _ _ => 0) (fun i => (ha i).symm)
    (fun i x v => le_trans (mul_nonneg hlam.le (sq_nonneg ‖v‖)) ((ha i).elliptic x v))
    (fun _ _ => le_rfl) hs u (laplacian g u)
    (fun i z hz => laplacian_eq_ellipticOp realBasis hg hr1 u i (hUt i) (heq i) (hKU i hz))
    (F := 0) (fun y => by rw [h y, abs_zero]) y
  have : |u y| = 0 := le_antisymm (by
    by_contra hpos; rw [not_le] at hpos; nlinarith [mul_pos hs hpos]) (abs_nonneg _)
  simpa using this

/-- **The Laplacian as a bounded linear map** `C^{2,r}(M) → C^{0,r}(M)`. -/
theorem exists_laplacianCLM {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (A : HolderAtlas n M)
    {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ T : A.HolderMap 2 r ℝ →L[ℝ] A.HolderMap 0 r ℝ, ∀ u y, T u y = laplacian g u y := by
  obtain ⟨lam, Λ, a, U, hlam, hΛ, ha, hU, hKU, hUt, heq⟩ :=
    exists_atlas_coeff hg A (r := r) r.2 hr1.le
  obtain ⟨T, CT, -, hT, hTrel⟩ := ManifoldContinuity.exists_chartOp realBasis hr0 hr1 a
    (fun _ _ => 0) (fun _ _ => 0) (fun i => (ha i).bound) (fun i => (ha i).holder)
    (fun _ => isLowerCoeff_zero hΛ) U hKU hUt fun u => ⟨laplacian g u, fun i z hz =>
      laplacian_eq_ellipticOp realBasis hg hr1.le u i (hUt i) (heq i) hz⟩
  refine ⟨T.mkContinuous CT hT, fun u y => ?_⟩
  have := ManifoldContinuity.eq_of_chartRel (A := A) realBasis (u := ⇑u)
    (g := ⇑(T u)) (g' := laplacian g u)
    (fun i z hz => hTrel u i z (hKU i hz))
    (fun i z hz => laplacian_eq_ellipticOp realBasis hg hr1.le u i (hUt i) (heq i) (hKU i hz))
  exact congrFun this y

/-- The Laplacian of a Hermitian form `g` as a bounded linear map `C^{2,r}(M) → C^{0,r}(M)`. -/
def laplacianCLM {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (A : HolderAtlas n M)
    {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) : A.HolderMap 2 r ℝ →L[ℝ] A.HolderMap 0 r ℝ :=
  (exists_laplacianCLM hg A hr0 hr1).choose

@[simp]
theorem laplacianCLM_apply {g : SmoothRealForm n M 2} (hg : g.IsHermitian) (A : HolderAtlas n M)
    {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) (u : A.HolderMap 2 r ℝ) (y : M) :
    laplacianCLM hg A hr0 hr1 u y = laplacian g u y :=
  (exists_laplacianCLM hg A hr0 hr1).choose_spec u y

/-- **`Δ_g - s : C^{2,r}(M) → C^{0,r}(M)` is bijective** for every `s > 0`. -/
theorem bijective_laplacianCLM_sub [CompactSpace M] {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (A : HolderAtlas n M) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {s : ℝ} (hs : 0 < s) :
    Function.Bijective (laplacianCLM hg A hr0 hr1 -
      s • toZeroCLM (A := A) (F := ℝ) (k := 2) hr1.le (by norm_num)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
    refine eq_zero_of_laplacian_sub_eq_zero hg hr1.le hs u fun y => ?_
    have := congrArg (fun w : A.HolderMap 0 r ℝ => w y) hu
    simpa using this
  · intro f
    obtain ⟨u, hu⟩ := exists_laplacian_sub_eq hg A hr0 hr1 hs f
    refine ⟨u, ?_⟩
    ext y
    simpa using hu y

/-- **`Δ_g - s` as an isomorphism** `C^{2,r}(M) ≃ C^{0,r}(M)` (open mapping theorem). -/
def laplacianSubEquiv [CompactSpace M] {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (A : HolderAtlas n M) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {s : ℝ} (hs : 0 < s) :
    A.HolderMap 2 r ℝ ≃L[ℝ] A.HolderMap 0 r ℝ :=
  ContinuousLinearEquiv.ofBijective _
    (LinearMap.ker_eq_bot.mpr (bijective_laplacianCLM_sub hg A hr0 hr1 hs).1)
    (LinearMap.range_eq_top.mpr (bijective_laplacianCLM_sub hg A hr0 hr1 hs).2)

theorem laplacianSubEquiv_apply [CompactSpace M] {g : SmoothRealForm n M 2} (hg : g.IsHermitian)
    (A : HolderAtlas n M) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {s : ℝ} (hs : 0 < s)
    (u : A.HolderMap 2 r ℝ) (y : M) :
    laplacianSubEquiv hg A hr0 hr1 hs u y = laplacian g u y - s * u y := by
  simp [laplacianSubEquiv]

end Atlas

end SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
