import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeLaplacian
import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormRieszContraction
import SGPT.Foundations.Analysis.Pending.XiaoCovectorProducts
import Mathlib.Analysis.Normed.Module.Alternating.Curry

set_option autoImplicit false

/-! Actual original exterior/interior operators and the positive Clifford covector symbol. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCliffordSymbol

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses
  NaturalHermitianCodifferential NaturalHermitianHodgeStarSquare NaturalHermitianHodgeStar
  NaturalHermitianSmoothFormMetric NaturalHermitianFormRieszContraction
  NaturalHermitianOriginalFormMetric NaturalHermitianOrthonormalFormBasis
  NaturalHermitianMetricCoefficients NaturalHermitianDualMetric NaturalHermitianUnitVolume
  NaturalHermitianMusicalInverse NaturalHermitianExteriorCovectorMetric
  NaturalOriginalGradedExteriorProduct ConstantFormProducts ProductTestForms
  ClosedProductCurrents CoordinateWedgeAssoc NaturalHermitianFormalAdjoint TopDegreeDensity

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedSpace

/-- Genuine continuous insertion in the first original alternating slot. -/
def interiorSuccCLM (q : ℕ) (v : ComplexModel n) :
    FormCoefficients n (q + 1) →L[ℝ] FormCoefficients n q :=
  (ContinuousLinearMap.apply ℝ (FormCoefficients n q) v).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ)
      (n := q)).toContinuousLinearMap

theorem interiorSuccCLM_apply (q : ℕ) (v : ComplexModel n)
    (η : FormCoefficients n (q + 1)) (u : Fin q → ComplexModel n) :
    interiorSuccCLM q v η u = η (Fin.cons v u) := rfl

/-- Actual original covector exterior multiplication, in its unchanged coefficient norm. -/
def covectorExteriorCLM (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n (q + 1) :=
  haveI := realForm_finiteDimensional (n := n) q
  LinearMap.toContinuousLinearMap (wedgeToBilin n (Nat.add_comm 1 q) (oneForm n ℓ))

theorem covectorExteriorCLM_apply (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (η : FormCoefficients n q) : covectorExteriorCLM q ℓ η = oneWedge ℓ η :=
  wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 q) ℓ η

/-- Genuine whole-tensor Clifford anticommutation, with positive input degree. -/
theorem interior_covector_clifford (ℓ : ComplexModel n →L[ℝ] ℝ) (v : ComplexModel n)
    (η : FormCoefficients n (q + 1)) :
    interiorSuccCLM (q + 1) v (covectorExteriorCLM (q + 1) ℓ η) +
      covectorExteriorCLM q ℓ (interiorSuccCLM q v η) = ℓ v • η := by
  ext u
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    covectorExteriorCLM_apply, interiorSuccCLM_apply]
  rw [oneWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    Fin.cons_zero, Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero, Fin.tail_cons,
    Fin.cons_succ, Fin.val_succ]
  have hrem (i : Fin (q + 1)) :
      (i.succ.removeNth (α := fun _ => ComplexModel n) (Fin.cons v u) : Fin (q + 1) → ComplexModel n) =
        (Fin.cons v (i.removeNth u) : Fin (q + 1) → ComplexModel n) := by
    change Fin.cons v u ∘ i.succ.succAbove = Fin.cons v (i.removeNth u)
    exact Fin.cons_comp_succ_succAbove v u i
  simp_rw [hrem, ← interiorSuccCLM_apply q v η, pow_succ]
  simp only [mul_neg, mul_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg]
  change ℓ v • η u -
    ∑ i : Fin (q + 1), (-1 : ℤ) ^ i.val •
      (ℓ (u i) • interiorSuccCLM q v η (i.removeNth u)) +
    oneWedge ℓ (interiorSuccCLM q v η) u = ℓ v • η u
  rw [oneWedge, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply]
  exact sub_add_cancel _ _

/-- The actual degree-zero Clifford formula has no predecessor term. -/
theorem interior_covector_zero (ℓ : ComplexModel n →L[ℝ] ℝ) (v : ComplexModel n)
    (η : FormCoefficients n 0) :
    interiorSuccCLM 0 v (covectorExteriorCLM 0 ℓ η) = ℓ v • η := by
  ext u
  rw [interiorSuccCLM_apply, covectorExteriorCLM_apply, oneWedge,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
  congr 2

theorem covectorExterior_square_zero (ℓ : ComplexModel n →L[ℝ] ℝ)
    (η : FormCoefficients n q) :
    covectorExteriorCLM (q + 1) ℓ (covectorExteriorCLM q ℓ η) = 0 := by
  simp only [covectorExteriorCLM_apply]
  have h := XiaoCovectorProducts.oneWedge_anticommute ℓ ℓ η
  ext u
  have hu := congrArg (fun A : FormCoefficients n (q + 1 + 1) => A u) h
  simp only [ContinuousAlternatingMap.neg_apply] at hu
  change _ = (0 : ℝ)
  linarith

theorem interior_square_zero (v : ComplexModel n) (η : FormCoefficients n (q + 1 + 1)) :
    interiorSuccCLM q v (interiorSuccCLM (q + 1) v η) = 0 :=
  ContinuousAlternatingMap.curryLeft_same η v


/-- The actual determinant form exterior product, for every original vector tuple. -/
theorem metricTupleForm_oneWedge
    (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (u : Fin q → ComplexModel n) :
    oneWedge ℓ (metricTupleForm a hJ hp u) =
      metricTupleForm a hJ hp (Fin.cons ((associatedMetricCLM a).inverse ℓ) u) := by
  ext x
  rw [metricTupleForm_apply, Matrix.det_succ_column_zero, oneWedge,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.of_apply, Fin.cons_zero, ContinuousLinearMap.smulRight_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hfirst : associatedMetricCLM a ((associatedMetricCLM a).inverse ℓ) (x i) = ℓ (x i) :=
    congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L (x i)) ((metric_inverse_identities hp).1 ℓ)
  rw [hfirst, metricTupleForm_apply]
  simp only [← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, ← mul_assoc]
  congr 1

/-- Literal metric determinant readback of the internally genuine orthonormal form basis. -/
theorem metricFormBasis_eq_metricTuple
    (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (q : ℕ) (s : FormIndex n q) :
    metricFormBasis a hJ hp b q s =
      metricTupleForm a hJ hp (fun i => b (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  rw [metricFormBasis_eq_dictionary, metricTupleForm]
  congr 2
  funext i
  exact coordinateCovector_eq_metric b hb _

/-- Entire original metric adjoint, internally extended from actual determinant forms. -/
theorem interior_metric_adjoint
    (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a) (hp : IsStrictlyPositive a)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n (q + 1))
    (θ : FormCoefficients n q) :
    originalFormMetric a hJ hp q (interiorSuccCLM q ((associatedMetricCLM a).inverse ℓ) η) θ =
      originalFormMetric a hJ hp (q + 1) η (covectorExteriorCLM q ℓ θ) := by
  obtain ⟨b, hb, _ho⟩ := exists_positive_metric_orthonormal_basis hJ hp
  have h : (originalFormMetric a hJ hp q
      (interiorSuccCLM q ((associatedMetricCLM a).inverse ℓ) η)).toLinearMap =
      ((originalFormMetric a hJ hp (q + 1) η).comp (covectorExteriorCLM q ℓ)).toLinearMap := by
    apply (metricFormBasis a hJ hp b q).ext
    intro s
    change originalFormMetric a hJ hp q
      (interiorSuccCLM q ((associatedMetricCLM a).inverse ℓ) η) (metricFormBasis a hJ hp b q s) =
      originalFormMetric a hJ hp (q + 1) η (covectorExteriorCLM q ℓ (metricFormBasis a hJ hp b q s))
    rw [metricFormBasis_eq_metricTuple a hJ hp b hb, covectorExteriorCLM_apply,
      metricTupleForm_oneWedge, form_metric_tuple_evaluation, form_metric_tuple_evaluation]
    rfl
  exact LinearMap.congr_fun h θ


/-- Literal equal-degree transport of the same original coefficient star. -/
theorem degreeStar_cast_input (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) {j k : ℕ} (h : j = k) (η : FormCoefficients n j) :
    degreeStar w e z k (castForm h η) =
      castForm (congrArg (fun t => 2 * n - t) h) (degreeStar w e z j η) := by
  subst h
  rfl

/-- The actual original Star--covector--Star identity on every entire source tensor. -/
theorem star_covector_star_eq_interior
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (η : FormCoefficients n (q + 1)) :
    castForm (show 2 * n - (2 * n - q) = q by omega)
      (degreeStar w e z (2 * n - q)
        (castForm (show 2 * n - (q + 1) + 1 = 2 * n - q by omega)
          (covectorExteriorCLM (2 * n - (q + 1)) ℓ (degreeStar w e z (q + 1) η)))) =
      interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η := by
  let S := degreeStar w e z (q + 1) η
  let T : FormCoefficients n (2 * n - q) :=
    castForm (show 2 * n - (q + 1) + 1 = 2 * n - q by omega)
      (covectorExteriorCLM (2 * n - (q + 1)) ℓ S)
  let C : FormCoefficients n q :=
    castForm (show 2 * n - (2 * n - q) = q by omega) (degreeStar w e z (2 * n - q) T)
  change C = _
  have hstar : degreeStar w e z q C = (-1 : ℝ) ^ q • T := by
    dsimp only [C]
    rw [degreeStar_cast_input]
    have hh := degreeStar_square w hw e z hz (2 * n - q) (by omega) T
    have hexp : (-1 : ℝ) ^ ((2 * n - q) * (2 * n - (2 * n - q))) = (-1 : ℝ) ^ q := by
      rw [show 2 * n - (2 * n - q) = q by omega]
      exact neg_one_pow_complement_product n q (by omega)
    rw [hexp] at hh
    exact hh
  have hprod (θ : FormCoefficients n q) :
      (-1 : ℝ) ^ q • wedgeTo (show q + (2 * n - q) = 2 * n by omega) θ T =
      wedgeTo (show (q + 1) + (2 * n - (q + 1)) = 2 * n by omega)
        (covectorExteriorCLM q ℓ θ) S := by
    dsimp only [T]
    rw [wedgeTo_castForm_right _ _ (show q + (2 * n - (q + 1) + 1) = 2 * n by omega)]
    simp only [covectorExteriorCLM_apply]
    have hh := oneWedge_coordinateWedge_right ℓ θ S
    rw [oneWedge_coordinateWedge_left] at hh
    have hc := congrArg
      (castForm (n := n) (show (q + (2 * n - (q + 1))) + 1 = 2 * n by omega)) hh
    simpa only [wedgeTo, map_smul, castForm_castForm] using hc.symm
  have hscalar (θ : FormCoefficients n q) :
      originalFormMetric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q θ C =
      originalFormMetric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q θ
        (interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η) := by
    have hh : formMetricCoefficients w e z q θ C • metricVolumeCoefficients w e z =
        formMetricCoefficients w e z (q + 1) (covectorExteriorCLM q ℓ θ) η •
          metricVolumeCoefficients w e z := by
      rw [← degreeStar_wedge_identity w hw e z hz q (by omega), hstar,
        wedgeTo_smul_right, hprod, degreeStar_wedge_identity w hw e z hz (q + 1) hq]
    have he := congrArg (topDensity (n := n)) hh
    change formMetricCoefficients w e z q θ C * metricVolumeDensity w e z =
      formMetricCoefficients w e z (q + 1) (covectorExteriorCLM q ℓ θ) η *
        metricVolumeDensity w e z at he
    have hs := mul_right_cancel₀ (metricVolumeDensity_positive w hw e z hz).ne' he
    rw [formMetricCoefficients_eq_original w hw e z hz q,
      formMetricCoefficients_eq_original w hw e z hz (q + 1)] at hs
    rw [(originalFormMetric_symm_positive _ _ _ (q + 1)).1, ← interior_metric_adjoint,
      (originalFormMetric_symm_positive _ _ _ q).1
        (interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η) θ] at hs
    exact hs
  by_contra hne
  let I := interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η
  have hpos := (originalFormMetric_symm_positive (w.coeff e z) (hw e z hz).1
    (hw e z hz).2 q).2 (C - I) (sub_ne_zero.mpr hne)
  have hzero : originalFormMetric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 q
      (C - I) (C - I) = 0 := by
    rw [map_sub, hscalar, sub_self]
  exact hpos.ne' hzero


/-- Actual original continuous codifferential coefficient composition, with its genuine zero branch. -/
def codifferentialCoefficientSymbolSucc (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    FormCoefficients n (q + 1) →L[ℝ] FormCoefficients n q :=
  if hq : q + 1 ≤ 2 * n then
    -((castForm (n := n) (show 2 * n - (2 * n - q) = q by omega)).toContinuousLinearMap.comp
      ((degreeStar w e z (2 * n - q)).comp
        ((castForm (n := n) (show 2 * n - (q + 1) + 1 = 2 * n - q by omega)).toContinuousLinearMap.comp
          ((covectorExteriorCLM (2 * n - (q + 1)) ℓ).comp (degreeStar w e z (q + 1))))))
  else 0

/-- Genuine entire-operator calibration to negative original metric insertion, in every degree. -/
theorem codifferentialCoefficientSymbolSucc_eq_neg_interior
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    codifferentialCoefficientSymbolSucc w e z q ℓ =
      -interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) := by
  apply ContinuousLinearMap.ext
  intro η
  unfold codifferentialCoefficientSymbolSucc
  split
  · rename_i hq
    change -(castForm _ (degreeStar w e z (2 * n - q)
      (castForm _ (covectorExteriorCLM (2 * n - (q + 1)) ℓ
        (degreeStar w e z (q + 1) η))))) =
      -(interiorSuccCLM q ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η)
    exact congrArg Neg.neg (star_covector_star_eq_interior w hw e z hz q hq ℓ η)
  · rename_i hq
    have hη := (degreeStar_above_source w e z (q + 1) (by omega) η).1
    subst η
    simp


/-- The actual positive Clifford endomorphism assembled from the original Hodge coefficient maps. -/
def cliffordLaplacianSymbol (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n q :=
  -((codifferentialCoefficientSymbolSucc w e z q ℓ).comp (covectorExteriorCLM q ℓ)) -
    if hzero : q = 0 then 0 else
      (castForm (n := n) (show q - 1 + 1 = q by omega)).toContinuousLinearMap.comp
        ((covectorExteriorCLM (q - 1) ℓ).comp
          ((codifferentialCoefficientSymbolSucc w e z (q - 1) ℓ).comp
            (castForm (n := n) (show q = q - 1 + 1 by omega)).toContinuousLinearMap))

/-- Entire original coefficient equality, including degree zero and excessive source degree. -/
theorem cliffordLaplacianSymbol_eq_scalar
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    cliffordLaplacianSymbol w e z q ℓ =
      ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) • ContinuousLinearMap.id ℝ (FormCoefficients n q) := by
  apply ContinuousLinearMap.ext
  intro η
  cases q with
  | zero =>
    change -(codifferentialCoefficientSymbolSucc w e z 0 ℓ (covectorExteriorCLM 0 ℓ η)) - 0 =
      ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) • η
    rw [codifferentialCoefficientSymbolSucc_eq_neg_interior w hw e z hz]
    simp only [neg_apply, neg_neg, sub_zero]
    exact interior_covector_zero ℓ _ η
  | succ q =>
    change -(codifferentialCoefficientSymbolSucc w e z (q + 1) ℓ
        (covectorExteriorCLM (q + 1) ℓ η)) -
      covectorExteriorCLM q ℓ (codifferentialCoefficientSymbolSucc w e z q ℓ η) =
      ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) • η
    rw [codifferentialCoefficientSymbolSucc_eq_neg_interior w hw e z hz,
      codifferentialCoefficientSymbolSucc_eq_neg_interior w hw e z hz]
    simp only [neg_apply, neg_neg, map_neg, sub_neg_eq_add]
    exact interior_covector_clifford ℓ _ η

/-- Genuine original strict positive scalar and nonnegative metric self-pairing. -/
theorem cliffordLaplacianSymbol_positive
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    0 < ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) ∧
      ∀ η : FormCoefficients n q, 0 ≤ formMetricCoefficients w e z q η
        (cliffordLaplacianSymbol w e z q ℓ η) := by
  have hpos : 0 < ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) :=
    (dualMetric_symm_positive (hw e z hz).1 (hw e z hz).2).2 ℓ hℓ
  refine ⟨hpos, ?_⟩
  intro η
  rw [cliffordLaplacianSymbol_eq_scalar w hw e z hz, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul,
    formMetricCoefficients_eq_original w hw e z hz]
  apply mul_nonneg hpos.le
  rcases eq_or_ne η 0 with rfl | hη
  · simp
  · exact ((originalFormMetric_symm_positive _ _ _ q).2 η hη).le

/-- Both actual continuous inverse identities, without a supplied symbol inverse. -/
theorem cliffordLaplacianSymbol_inverse
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    ((ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ))⁻¹ •
      ContinuousLinearMap.id ℝ (FormCoefficients n q)).comp
        (cliffordLaplacianSymbol w e z q ℓ) = ContinuousLinearMap.id ℝ (FormCoefficients n q) ∧
      (cliffordLaplacianSymbol w e z q ℓ).comp
        ((ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ))⁻¹ •
          ContinuousLinearMap.id ℝ (FormCoefficients n q)) = ContinuousLinearMap.id ℝ (FormCoefficients n q) := by
  have hne := (cliffordLaplacianSymbol_positive w hw e z hz q ℓ hℓ).1.ne'
  rw [cliffordLaplacianSymbol_eq_scalar w hw e z hz]
  constructor
  · apply ContinuousLinearMap.ext
    intro η
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · apply ContinuousLinearMap.ext
    intro η
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, mul_inv_cancel₀ hne, one_smul]

end SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCliffordSymbol
