import SGPT.Hodge.StarPairing
import SGPT.Foundations.Analysis.Pending.CoordinateDensityHermitian
import SGPT.Foundations.Analysis.Pending.NaturalHermitianUnitVolume
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

/-!
# An adapted unitary frame for a pair (Kähler covector, real `(1,1)`-covector)

Blueprint `claude-hodge` (lane HODGE-STAR, package `HodgeStar`), node
`claude-hodge:lem-adapted-basis`.

Let `a` be a strictly positive real `(1,1)`-covector on `ℂⁿ` and `G` a real `(1,1)`-covector.
There is a `ℂ`-linear automorphism `T` of `ℂⁿ` such that

* `a ∘ T = ω₀` is the standard Kähler form (so `T` maps the standard real frame to an
  orthonormal basis for the metric `g(u, v) = a(u, i v)` of `a`);
* `G ∘ T` is block diagonal on the standard real frame, with weights `λ₁, …, λₙ`;
* `Re tr(H_a⁻¹ H_G) = ∑ⱼ λⱼ` (the trace `Λ_a G` of `SGPT.Hodge.trace`).

The proof writes `a = ω₀ ∘ S` (TN `exists_positive_standard_factorization`), diagonalizes the
Hermitian coefficient matrix of `G ∘ S⁻¹` by a unitary matrix (spectral theorem, as in TN
`actualTopPowerDensity_eq_normalizedTopPowerDensity`), and uses the congruence invariance of
`tr(H⁻¹K)` (TN `trace_inv_mul_congr`).

* `exists_adapted_frame`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped Matrix

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.NaturalHermitianUnitVolume
  SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart

variable {n : ℕ}

/-- The coefficient matrix of the standard Kähler form is `π · 1`. -/
theorem normalizedHermitianMatrix_standard :
    normalizedHermitianMatrix (standardHermitianTwoForm n) =
      (Real.pi : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext j k
  by_cases h : j = k
  · subst h
    simp [normalizedHermitianMatrix, coordinateVector, inner_smul_right]
  · simp [normalizedHermitianMatrix, coordinateVector, EuclideanSpace.inner_single_left,
      inner_smul_right, h, Matrix.one_apply_ne h]

/-- Two-forms agreeing on all pairs of standard frame vectors are equal. -/
theorem twoForm_ext_frame {A B : CoordinateRealTwoForm n}
    (h : ∀ x y : Fin n × Fin 2, A ![frameVec x, frameVec y] = B ![frameVec x, frameVec y]) :
    A = B := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply (coordinateRealBasis n).ext_alternating
  intro v _
  obtain ⟨x, hx⟩ := finProdFinEquiv.surjective (v 0)
  obtain ⟨y, hy⟩ := finProdFinEquiv.surjective (v 1)
  have hv : (fun i => coordinateRealBasis n (v i)) = ![frameVec x, frameVec y] := by
    funext i
    fin_cases i <;> simp [frameVec, hx, hy]
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap]
  rw [hv]
  exact h x y

/-- **Real `(1,1)`-forms are determined by their coefficient matrix.** -/
theorem eq_of_normalizedHermitianMatrix_eq {A B : CoordinateRealTwoForm n} (hA : IsOneOne A)
    (hB : IsOneOne B) (h : normalizedHermitianMatrix A = normalizedHermitianMatrix B) :
    A = B := by
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hre : ∀ j k : Fin n, A ![coordinateVector j, Complex.I • coordinateVector k] =
      B ![coordinateVector j, Complex.I • coordinateVector k] := by
    intro j k
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M j k).re) h
    simp only [normalizedHermitianMatrix, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      sub_zero, one_mul, zero_sub, mul_zero] at h1
    have h2 : Real.pi * A ![coordinateVector j, Complex.I • coordinateVector k] =
        Real.pi * B ![coordinateVector j, Complex.I • coordinateVector k] := by
      linear_combination h1
    exact mul_left_cancel₀ hpi h2
  have him : ∀ j k : Fin n, A ![coordinateVector j, coordinateVector k] =
      B ![coordinateVector j, coordinateVector k] := by
    intro j k
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M j k).im) h
    simp only [normalizedHermitianMatrix, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      sub_zero, one_mul, zero_sub, mul_zero, zero_add, add_zero] at h1
    have h2 : Real.pi * A ![coordinateVector j, coordinateVector k] =
        Real.pi * B ![coordinateVector j, coordinateVector k] := by
      linear_combination -h1
    exact mul_left_cancel₀ hpi h2
  apply twoForm_ext_frame
  rintro ⟨j, b⟩ ⟨k, c⟩
  rw [coordinateTwoForm_apply_realFrame_block A hA, coordinateTwoForm_apply_realFrame_block B hB,
    hre, him]

/-- **The adapted unitary frame** (`claude-hodge:lem-adapted-basis`). -/
theorem exists_adapted_frame (a G : CoordinateRealTwoForm n) (hJ : IsOneOne a)
    (hp : IsStrictlyPositive a) (hG : IsOneOne G) :
    ∃ (T : ComplexModel n →ₗ[ℂ] ComplexModel n) (d : Fin n → ℝ),
      LinearMap.det (T.restrictScalars ℝ) ≠ 0 ∧
      compLinearMap a T = standardHermitianTwoForm n ∧
      IsBlockDiagonal (compLinearMap G T) d ∧
      (Matrix.trace ((normalizedHermitianMatrix a)⁻¹ * normalizedHermitianMatrix G)).re =
        ∑ j, d j := by
  classical
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  obtain ⟨S, hS, -, -⟩ := exists_positive_standard_factorization hJ hp
  set S₁' : ComplexModel n →ₗ[ℂ] ComplexModel n := S.symm.toLinearEquiv.toLinearMap with hS₁'
  have ha : compLinearMap a S₁' = standardHermitianTwoForm n := by
    ext v
    rw [hS]
    simp only [compLinearMap, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp [hS₁']
  set G₁ := compLinearMap G S₁' with hG₁def
  have hG₁ : IsOneOne G₁ := isOneOne_compLinearMap hG S₁'
  have hH : (normalizedHermitianMatrix G₁).IsHermitian :=
    normalizedHermitianMatrix_isHermitian G₁ hG₁
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hUdef
  set S₂ : ComplexModel n →ₗ[ℂ] ComplexModel n :=
    (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm (U.map (starRingEnd ℂ)) with hSdef
  have hSM : standardMatrix S₂ = U.map (starRingEnd ℂ) := by
    rw [standardMatrix, hSdef, LinearEquiv.apply_symm_apply]
  have htrans : (U.map (starRingEnd ℂ))ᵀ = star U := by
    ext j k
    simp
  have hmapmap : (U.map (starRingEnd ℂ)).map (starRingEnd ℂ) = U := by
    ext j k
    simp
  have hUU : star U * U = 1 := by
    rw [hUdef]
    exact_mod_cast Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hdiag : normalizedHermitianMatrix (compLinearMap G₁ S₂) =
      Matrix.diagonal fun j => ((hH.eigenvalues j : ℝ) : ℂ) := by
    rw [normalizedHermitianMatrix_compLinearMap hG₁, hSM, htrans, hmapmap]
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hUdef] at this
    exact this
  have hω₂ : compLinearMap (standardHermitianTwoForm n) S₂ = standardHermitianTwoForm n := by
    apply eq_of_normalizedHermitianMatrix_eq
      (isOneOne_compLinearMap (standardHermitianTwoForm_isOneOne n) S₂)
      (standardHermitianTwoForm_isOneOne n)
    rw [normalizedHermitianMatrix_compLinearMap (standardHermitianTwoForm_isOneOne n), hSM,
      htrans, hmapmap, normalizedHermitianMatrix_standard, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hUU]
  set T : ComplexModel n →ₗ[ℂ] ComplexModel n := S₁' ∘ₗ S₂ with hTdef
  have hcomp : ∀ A : CoordinateRealTwoForm n,
      compLinearMap A T = compLinearMap (compLinearMap A S₁') S₂ := fun A => by
    ext v
    rfl
  have haT : compLinearMap a T = standardHermitianTwoForm n := by rw [hcomp, ha, hω₂]
  have hGT : compLinearMap G T = compLinearMap G₁ S₂ := hcomp G
  have hTinj : ∀ u, T u = 0 → u = 0 := by
    intro u hu
    have h1 : standardHermitianTwoForm n ![u, Complex.I • u] = 0 := by
      rw [← haT, compLinearMap_apply, map_smul, hu, smul_zero]
      exact (a.map_coord_zero (0 : Fin 2) rfl)
    rw [standardHermitianTwoForm_apply_I_smul_self] at h1
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)
  have hdetT : LinearMap.det T ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    obtain ⟨u, hu, hne⟩ := (Submodule.ne_bot_iff _).mp h0
    exact hne (hTinj u hu)
  have hdetR : LinearMap.det (T.restrictScalars ℝ) ≠ 0 := by
    rw [normSq_det_eq_realDet]
    exact (Complex.normSq_pos.mpr hdetT).ne'
  -- the block weights, from the diagonal coefficient matrix
  set A := compLinearMap G₁ S₂ with hAdef
  have hA : IsOneOne A := isOneOne_compLinearMap hG₁ S₂
  set d : Fin n → ℝ := fun j => hH.eigenvalues j with hd
  have key : ∀ j k : Fin n, hermitianEntry A (coordinateVector j) (coordinateVector k) =
      if j = k then ((d j / Real.pi : ℝ) : ℂ) else 0 := by
    intro j k
    have h : (Real.pi : ℂ) * hermitianEntry A (coordinateVector j) (coordinateVector k) =
        (Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) j k := by
      rw [← normalizedHermitianMatrix_apply', hAdef, hdiag]
    by_cases hjk : j = k
    · subst hjk
      rw [Matrix.diagonal_apply_eq] at h
      rw [if_pos rfl]
      push_cast
      field_simp
      linear_combination h
    · rw [Matrix.diagonal_apply_ne _ hjk] at h
      rw [if_neg hjk]
      exact (mul_eq_zero.1 h).resolve_left hpiC
  have hre : ∀ j k : Fin n, A ![coordinateVector j, Complex.I • coordinateVector k] =
      if j = k then d j / Real.pi else 0 := by
    intro j k
    have h := congrArg Complex.re (key j k)
    simpa [hermitianEntry, apply_ite Complex.re] using h
  have him : ∀ j k : Fin n, A ![coordinateVector j, coordinateVector k] = 0 := by
    intro j k
    have h := congrArg Complex.im (key j k)
    have hrhs : (if j = k then ((d j / Real.pi : ℝ) : ℂ) else 0).im = 0 := by
      by_cases hjk : j = k <;> simp [hjk]
    rw [hrhs] at h
    simp only [hermitianEntry, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_sub,
      neg_eq_zero, zero_add] at h
    linarith
  have hblock : IsBlockDiagonal (compLinearMap G T) (fun j => d j / Real.pi) := by
    rw [hGT]
    rintro ⟨j, b⟩ ⟨k, c⟩
    rw [frameVec, frameVec, coordinateTwoForm_apply_realFrame_block A hA j k b c, him j k,
      hre j k]
    by_cases hjk : j = k
    · subst hjk
      fin_cases b <;> fin_cases c <;> norm_num
    · fin_cases b <;> fin_cases c <;> simp [hjk]
  -- the trace, by congruence invariance
  have htr : (Matrix.trace ((normalizedHermitianMatrix a)⁻¹ * normalizedHermitianMatrix G)).re =
      ∑ j, d j / Real.pi := by
    have hunit : IsUnit (standardMatrix T).det := by
      rw [det_standardMatrix]
      exact isUnit_iff_ne_zero.mpr hdetT
    rw [← trace_inv_mul_congr hunit, ← normalizedHermitianMatrix_compLinearMap hJ,
      ← normalizedHermitianMatrix_compLinearMap hG, haT, hGT, hdiag,
      normalizedHermitianMatrix_standard]
    have hinv : ((Real.pi : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        (Real.pi : ℂ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hpiC,
        one_smul]
    rw [hinv, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Matrix.trace_diagonal,
      smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
      Complex.ofReal_re, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd]
    ring
  exact ⟨T, fun j => d j / Real.pi, hdetR, haT, hblock, htr⟩
