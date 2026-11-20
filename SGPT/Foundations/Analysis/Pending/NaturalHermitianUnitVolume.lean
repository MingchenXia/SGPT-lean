import SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation
import SGPT.Foundations.Analysis.Pending.NaturalHermitianMetricCoefficients
import Mathlib.Analysis.InnerProductSpace.Orientation

/-! # Genuine metric unit normalization of the original Hermitian top form -/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianUnitVolume

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianTopFormOrientation

variable {n : ℕ}

private theorem model_real_inner (u v : ComplexModel n) :
    inner ℝ u v = (inner ℂ u v).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- Actual canonical complex orientation uses the interleaved real orthonormal basis. -/
theorem coordinateRealBasis_orthonormal : Orthonormal ℝ (coordinateRealBasis n) := by
  rw [coe_coordinateRealBasis]
  apply orthonormal_iff_ite.mpr
  intro i j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨s, l⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [coordinateRealFrame_finProdFinEquiv, coordinateRealFrame_finProdFinEquiv]
  fin_cases k <;> fin_cases l <;> by_cases hrs : r = s <;>
    simp [hrs, coordinateVector, model_real_inner, EuclideanSpace.inner_single_left,
      inner_smul_left, inner_smul_right, -inner_self_eq_norm_sq_to_K]

/-- The actual standard normalized top form is the full canonical real basis determinant. -/
theorem standard_normalized_power_eq_det :
    (((n.factorial : ℝ)⁻¹) • coordinateWedgePower (standardHermitianTwoForm n) n).toAlternatingMap =
      (coordinateRealBasis n).det := by
  have h := (coordinateWedgePower (standardHermitianTwoForm n) n).toAlternatingMap.eq_smul_basis_det
    (coordinateRealBasis n)
  have hvalue : (coordinateWedgePower (standardHermitianTwoForm n) n).toAlternatingMap
      (coordinateRealBasis n) = (n.factorial : ℝ) := by
    change coordinateWedgePower (standardHermitianTwoForm n) n (coordinateRealBasis n) = _
    rw [coe_coordinateRealBasis]
    exact actualTopPowerDensity_eq_factorial_of_apply_eq_im _ standardHermitianTwoForm_apply
  ext v
  change (n.factorial : ℝ)⁻¹ *
    (coordinateWedgePower (standardHermitianTwoForm n) n).toAlternatingMap v = _
  rw [h, AlternatingMap.smul_apply, hvalue, smul_eq_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  simp only [← mul_assoc, inv_mul_cancel₀ hf, one_mul]

/-- Genuine C-star Hermitian factorization, bounded inverse, full metric and positive determinant. -/
theorem exists_positive_standard_factorization {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hJ : IsOneOne a) (hp : IsStrictlyPositive a) :
    ∃ S : ComplexModel n ≃L[ℂ] ComplexModel n,
      a = (standardHermitianTwoForm n).compContinuousLinearMap
        (S.restrictScalars ℝ).toContinuousLinearMap ∧
      (∀ u v, associatedMetricCLM a u v = inner ℝ (S u) (S v)) ∧
      0 < LinearMap.det (S.restrictScalars ℝ).toLinearEquiv.toLinearMap := by
  have hsemi : PositiveClasses.CoefficientSemipositive a := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · rw [smul_zero, a.map_eq_zero_of_eq ![0, 0] (i := 0) (j := 1) (by simp) (by decide)]
    · exact (hp u hu).le
  obtain ⟨T, hT⟩ := exists_linearMap_eq_standard_compContinuousLinearMap hJ hsemi
  have hdet : LinearMap.det T ≠ 0 :=
    det_ne_zero_of_standard_comp_strictlyPositive (A := a) (fun u v => by
      rw [hT, standardHermitianTwoForm_compContinuousLinearMap_apply]) hp
  let C := LinearMap.toContinuousLinearMap T
  have hker : C.ker = ⊥ := by
    change T.ker = ⊥
    by_contra hne
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
  have hrange : C.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact (LinearMap.injective_iff_surjective (f := T)).mp (LinearMap.ker_eq_bot.mp hker)
  let S := ContinuousLinearEquiv.ofBijective C hker hrange
  have hC : S.toContinuousLinearMap = C := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hlinear : S.toLinearEquiv.toLinearMap = T :=
    congrArg ContinuousLinearMap.toLinearMap hC
  have hreal : (S.restrictScalars ℝ).toContinuousLinearMap =
      LinearMap.toContinuousLinearMap (T.restrictScalars ℝ) := by
    apply ContinuousLinearMap.ext
    intro u
    exact congrArg (fun L : ComplexModel n →L[ℂ] ComplexModel n => L u) hC
  have hform : a = (standardHermitianTwoForm n).compContinuousLinearMap
      (S.restrictScalars ℝ).toContinuousLinearMap := by rw [hreal]; exact hT
  refine ⟨S, hform, ?_, ?_⟩
  · intro u v
    rw [associatedMetricCLM_apply, associatedMetric, hform]
    change standardHermitianTwoForm n ![S u, S (Complex.I • v)] = _
    rw [map_smul, standardHermitianTwoForm_apply, inner_smul_right, model_real_inner]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  · change 0 < LinearMap.det (S.toLinearEquiv.toLinearMap.restrictScalars ℝ)
    rw [hlinear, normSq_det_eq_realDet]
    exact Complex.normSq_pos.mpr hdet

/-- Every actual positive metric orthonormal real basis has true unit normalized top volume. -/
theorem normalized_power_on_positive_orthonormal_basis
    {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (ho : b.orientation = (coordinateRealBasis n).orientation) :
    (n.factorial : ℝ)⁻¹ * coordinateWedgePower a n b = 1 := by
  obtain ⟨S, hS, hg, hpos⟩ := exists_positive_standard_factorization hJ hp
  let c := coordinateRealBasis n
  let d := b.map (S.restrictScalars ℝ).toLinearEquiv
  have hd : Orthonormal ℝ d := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change inner ℝ (S (b i)) (S (b j)) = _
    rw [← hg]
    exact hb i j
  have hdo : d.orientation = c.orientation :=
    ((b.orientation_comp_linearEquiv_eq_iff_det_pos (S.restrictScalars ℝ).toLinearEquiv).mpr hpos).trans ho
  have hdet : c.det d = 1 := by
    have h := (c.toOrthonormalBasis coordinateRealBasis_orthonormal).det_to_matrix_orthonormalBasis_of_same_orientation
      (d.toOrthonormalBasis hd)
        (by simpa only [Module.Basis.toBasis_toOrthonormalBasis] using hdo.symm)
    simpa only [Module.Basis.toBasis_toOrthonormalBasis, Module.Basis.coe_toOrthonormalBasis] using h
  rw [hS, coordinateWedgePower_compContinuousLinearMap,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have h := congrArg (fun A : (ComplexModel n) [⋀^Fin (n * 2)]→ₗ[ℝ] ℝ =>
    A (fun i => S (b i))) (standard_normalized_power_eq_det (n := n))
  exact h.trans hdet

/-- Full alternating tensor equality with every positive metric orthonormal basis determinant. -/
theorem normalized_power_eq_positive_orthonormal_det
    {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (ho : b.orientation = (coordinateRealBasis n).orientation) :
    (((n.factorial : ℝ)⁻¹) • coordinateWedgePower a n).toAlternatingMap = b.det := by
  have h := (((n.factorial : ℝ)⁻¹) • coordinateWedgePower a n).toAlternatingMap.eq_smul_basis_det b
  have hvalue : (((n.factorial : ℝ)⁻¹) • coordinateWedgePower a n).toAlternatingMap b = 1 :=
    normalized_power_on_positive_orthonormal_basis hJ hp b hb ho
  rw [hvalue, one_smul] at h
  exact h

/-- Actual positive metric orthonormal frames are internally produced, including the empty frame. -/
theorem exists_positive_metric_orthonormal_basis
    {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ} (hJ : IsOneOne a) (hp : IsStrictlyPositive a) :
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation := by
  obtain ⟨S, -, hg, hpos⟩ := exists_positive_standard_factorization hJ hp
  let c := coordinateRealBasis n
  let b := c.map (S.restrictScalars ℝ).symm.toLinearEquiv
  have hmap : b.map (S.restrictScalars ℝ).toLinearEquiv = c := by
    apply DFunLike.ext
    intro i
    change S (S.symm (c i)) = c i
    exact S.apply_symm_apply _
  refine ⟨b, ?_, ?_⟩
  · intro i j
    rw [hg]
    change inner ℝ (S (S.symm (c i))) (S (S.symm (c j))) = _
    rw [S.apply_symm_apply, S.apply_symm_apply]
    exact orthonormal_iff_ite.mp coordinateRealBasis_orthonormal i j
  · have h := (b.orientation_comp_linearEquiv_eq_iff_det_pos
      (S.restrictScalars ℝ).toLinearEquiv).mpr hpos
    rw [hmap] at h
    exact h.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The actual original smooth Hermitian top form is metric unit volume on all positive ON frames. -/
theorem original_chart_unit_volume (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    (∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation) ∧
    ∀ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM (w.coeff e z) (b i) (b j) = if i = j then 1 else 0) →
      b.orientation = (coordinateRealBasis n).orientation →
      ∀ v : Fin (n * 2) → ComplexModel n, (normalizedHermitianTopForm w).coeff e z v = b.det v := by
  refine ⟨exists_positive_metric_orthonormal_basis (hw e z hz).1 (hw e z hz).2, ?_⟩
  intro b hb ho v
  have h := normalized_power_eq_positive_orthonormal_det (hw e z hz).1 (hw e z hz).2 b hb ho
  exact congrArg (fun A : (ComplexModel n) [⋀^Fin (n * 2)]→ₗ[ℝ] ℝ => A v) h

end SGPT.Foundations.Analysis.Pending.NaturalHermitianUnitVolume
