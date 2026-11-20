import SGPT.Foundations.Analysis.Pending.NaturalHermitianExteriorCliffordSymbol
import Mathlib.Analysis.Calculus.FDeriv.Pow

set_option autoImplicit false

/-! Actual real differential highest-order identification of the original Hodge Laplacian. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgePrincipalSymbol

open FirstPass FirstPass.MongeAmpere NaturalHermitianExteriorCliffordSymbol
  NaturalHermitianCodifferential NaturalHermitianHodgeStarSquare NaturalHermitianHodgeStar
  NaturalHermitianHodgeLaplacian NaturalHermitianSmoothFormMetric
  NaturalHermitianMetricCoefficients NaturalHermitianMusicalInverse
  ConstantFormProducts ClosedProductCurrents NaturalOriginalGradedExteriorProduct ProductTestForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace


section ScalarJets

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Genuine smooth quadratic scalar with zero lower jets at its center. -/
def quadraticScalar (z : E) (ℓ : E →L[ℝ] ℝ) (y : E) : ℝ :=
  (1 / 2 : ℝ) * (ℓ (y - z)) ^ 2

theorem quadraticScalar_contDiff (z : E) (ℓ : E →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (quadraticScalar z ℓ) :=
  contDiff_const.mul ((ℓ.contDiff.comp (contDiff_id.sub contDiff_const)).pow 2)

theorem affineCovector_hasFDerivAt (z y : E) (ℓ : E →L[ℝ] ℝ) :
    HasFDerivAt (fun x => ℓ (x - z)) ℓ y := by
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
    ℓ.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const z)

theorem quadraticScalar_fderiv (z y : E) (ℓ : E →L[ℝ] ℝ) :
    fderiv ℝ (quadraticScalar z ℓ) y = ℓ (y - z) • ℓ := by
  have h := ((affineCovector_hasFDerivAt z y ℓ).pow 2).const_smul (1 / 2 : ℝ)
  have hd := h.fderiv
  change fderiv ℝ (quadraticScalar z ℓ) y = _ at hd
  rw [hd]
  ext v
  simp only [smul_apply, smul_eq_mul]
  norm_num
  ring

theorem quadraticScalar_center (z : E) (ℓ : E →L[ℝ] ℝ) :
    quadraticScalar z ℓ z = 0 := by
  simp only [quadraticScalar, sub_self, map_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

/-- Entire true second product jet in the original norm, not an ellipticity input. -/
theorem quadraticScalar_second_product_jet (z : E) (ℓ : E →L[ℝ] ℝ)
    (A : E → F) (hA : ContDiffAt ℝ 2 A z) :
    fderiv ℝ (fun y => quadraticScalar z ℓ y • A y) z = 0 ∧
      fderiv ℝ (fun y => fderiv ℝ (fun x => quadraticScalar z ℓ x • A x) y) z =
        ℓ.smulRight (ℓ.smulRight (A z)) := by
  have hAd := hA.differentiableAt (by norm_num)
  have hDA := (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hQ : DifferentiableAt ℝ (quadraticScalar z ℓ) z :=
    ((quadraticScalar_contDiff z ℓ).differentiable (by simp)).differentiableAt
  have hS := affineCovector_hasFDerivAt z z ℓ
  have hLA := (ContinuousLinearMap.smulRightL ℝ E F ℓ).hasFDerivAt.comp z hAd.hasFDerivAt
  have heq : (fun y => fderiv ℝ (fun x => quadraticScalar z ℓ x • A x) y) =ᶠ[𝓝 z]
      (fun y => quadraticScalar z ℓ y • fderiv ℝ A y +
        ℓ (y - z) • ℓ.smulRight (A y)) := by
    filter_upwards [hA.eventually (by norm_num)] with y hy
    rw [fderiv_fun_smul ((quadraticScalar_contDiff z ℓ).differentiable (by simp)).differentiableAt
      (hy.differentiableAt (by norm_num)), quadraticScalar_fderiv]
    congr 1
    ext v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_smul, smul_eq_mul]
  constructor
  · rw [fderiv_fun_smul hQ hAd, quadraticScalar_fderiv]
    simp only [quadraticScalar_center, sub_self, map_zero, zero_smul,
      ContinuousLinearMap.zero_smulRight, add_zero]
  · have hR := (hQ.hasFDerivAt.smul hDA.hasFDerivAt).add (hS.smul hLA)
    have hd := (hR.congr_of_eventuallyEq heq).fderiv
    have hfixed (a : F) : (ContinuousLinearMap.smulRightL ℝ E F ℓ) a = ℓ.smulRight a := by
      ext v
      rfl
    simpa only [quadraticScalar_center, quadraticScalar_fderiv, sub_self, map_zero,
      zero_smul, ContinuousLinearMap.zero_smulRight, add_zero, zero_add,
      Function.comp_apply, hfixed] using hd

end ScalarJets


/-- Literal original local positive-degree negative Star--d--Star expression. -/
def localCodifferentialSucc (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (A : ComplexModel n → FormCoefficients n (p + 1))
    (z : ComplexModel n) : FormCoefficients n p :=
  (-1 : ℝ) • castForm (show 2 * n - (2 * n - (p + 1) + 1) = p by omega)
    (degreeStar w e z (2 * n - (p + 1) + 1)
      (extDeriv (fun y => degreeStar w e y (p + 1) (A y)) z))

/-- The original local codifferential in every natural degree, with genuine zero branches. -/
def localCodifferential (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (A : ComplexModel n → FormCoefficients n q) (z : ComplexModel n) :
    FormCoefficients n (q - 1) :=
  if hzero : q = 0 then 0 else if hq : q ≤ 2 * n then
    localCodifferentialSucc w e (q - 1) (by omega)
      (fun y => castForm (show q = q - 1 + 1 by omega) (A y)) z
  else 0

/-- The literal local expression of the actual all-degree original Hodge Laplacian. -/
def localHodgeLaplacian (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (A : ComplexModel n → FormCoefficients n q) (z : ComplexModel n) :
    FormCoefficients n q :=
  castForm (Nat.add_sub_cancel q 1)
    (localCodifferential w e (q + 1) (fun y => extDeriv A y) z) +
      if hzero : q = 0 then 0 else
        castForm (show q - 1 + 1 = q by omega)
          (extDeriv (localCodifferential w e q A) z)

theorem localCodifferentialSucc_eq_original_coeff (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (A : SmoothRealForm n M (p + 1)) (z : ComplexModel n) :
    localCodifferentialSucc w e p hp (A.coeff e) z =
      (coderivativeSucc w hw p hp A).coeff e z := by
  unfold localCodifferentialSucc coderivativeSucc
  rw [coeff_smul, castSmoothForm_coeff, degreeHodgeStarForm_coeff]
  congr 3
  change extDeriv (fun y => degreeStar w e y (p + 1) (A.coeff e y)) z =
    extDeriv ((degreeHodgeStarForm w hw (p + 1) hp A).coeff e) z
  congr 1
  funext y
  exact (degreeHodgeStarForm_coeff w hw (p + 1) hp A e y).symm

theorem localCodifferential_eq_original_coeff (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : SmoothRealForm n M q) (z : ComplexModel n) :
    localCodifferential w e q (A.coeff e) z = (coderivativeForm w hw q A).coeff e z := by
  unfold localCodifferential coderivativeForm
  split
  · rfl
  · split
    · rename_i hq0 hq
      rw [← localCodifferentialSucc_eq_original_coeff]
      congr 2
      funext y
      exact (castSmoothForm_coeff (show q = q - 1 + 1 by omega) A e y).symm
    · rfl

theorem localHodgeLaplacian_eq_original_coeff (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e : ComplexChart n M) (q : ℕ)
    (A : SmoothRealForm n M q) (z : ComplexModel n) :
    localHodgeLaplacian w e q (A.coeff e) z = (hodgeLaplacianForm w hw q A).coeff e z := by
  have hδ : localCodifferential w e q (A.coeff e) = (coderivativeForm w hw q A).coeff e := by
    funext y
    exact localCodifferential_eq_original_coeff w hw e q A y
  have hd : (fun y => extDeriv (A.coeff e) y) = A.exteriorDerivative.coeff e := rfl
  unfold localHodgeLaplacian hodgeLaplacianForm
  rw [coeff_add, castSmoothForm_coeff, hd, localCodifferential_eq_original_coeff w hw e]
  rw [hδ]
  split
  · rfl
  · rw [castSmoothForm_coeff]
    rfl


/-- The same natural-degree star field is genuinely smooth in its original operator norm. -/
theorem degreeStar_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (fun z => degreeStar w e z q) e.val.target := by
  let C : FormCoefficients n (Module.finrank ℝ (ComplexModel n) - q) →L[ℝ]
      FormCoefficients n (2 * n - q) :=
    (castForm (n := n) (show Module.finrank ℝ (ComplexModel n) - q = 2 * n - q by
      rw [complexModel_real_finrank])).toContinuousLinearMap
  exact ((ContinuousLinearMap.compL ℝ (FormCoefficients n q)
    (FormCoefficients n (Module.finrank ℝ (ComplexModel n) - q))
    (FormCoefficients n (2 * n - q))) C).contDiff.comp_contDiffOn
      (allDegreeStarCoefficients_smooth w hw e q)

/-- Actual differentiated exterior expression on a scalar quadratic product. -/
theorem extDeriv_quadratic_product_jet {q : ℕ} (z : ComplexModel n)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n → FormCoefficients n q)
    (hA : ContDiffAt ℝ 2 A z) :
    extDeriv (fun y => quadraticScalar z ℓ y • A y) z = 0 ∧
      fderiv ℝ (fun y => extDeriv (fun x => quadraticScalar z ℓ x • A x) y) z =
        ℓ.smulRight (covectorExteriorCLM q ℓ (A z)) := by
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hjet := quadraticScalar_second_product_jet z ℓ A hA
  have hB : ContDiffAt ℝ 2 (fun y => quadraticScalar z ℓ y • A y) z :=
    ((quadraticScalar_contDiff z ℓ).contDiffAt.of_le (m := 2) (by exact WithTop.coe_le_coe.mpr le_top)).smul hA
  have hDB := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  constructor
  · change T (fderiv ℝ (fun y => quadraticScalar z ℓ y • A y) z) = 0
    rw [hjet.1, map_zero]
  · change fderiv ℝ (fun y => T (fderiv ℝ (fun x => quadraticScalar z ℓ x • A x) y)) z = _
    have hd := (T.hasFDerivAt.comp z hDB.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd, hjet.2]
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
      ContinuousLinearMap.smulRight_apply, covectorExteriorCLM_apply]
    rfl


/-- Actual original outer coefficient map in the positive-degree local codifferential. -/
def codifferentialOuterCLM (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) :
    FormCoefficients n (2 * n - (p + 1) + 1) →L[ℝ] FormCoefficients n p :=
  (-1 : ℝ) • (castForm (n := n)
    (show 2 * n - (2 * n - (p + 1) + 1) = p by omega)).toContinuousLinearMap.comp
      (degreeStar w e z (2 * n - (p + 1) + 1))

theorem codifferentialOuter_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n) :
    ContDiffOn ℝ ∞ (codifferentialOuterCLM w e p hp) e.val.target := by
  let C : FormCoefficients n (2 * n - (2 * n - (p + 1) + 1)) →L[ℝ] FormCoefficients n p :=
    (castForm (n := n) (show 2 * n - (2 * n - (p + 1) + 1) = p by omega)).toContinuousLinearMap
  exact (((ContinuousLinearMap.compL ℝ (FormCoefficients n (2 * n - (p + 1) + 1))
    (FormCoefficients n (2 * n - (2 * n - (p + 1) + 1))) (FormCoefficients n p)) C).contDiff.comp_contDiffOn
      (degreeStar_smooth w hw e (2 * n - (p + 1) + 1))).const_smul (-1 : ℝ)

/-- Literal index calibration to the actual already constructed coefficient symbol. -/
theorem codifferentialOuter_covector_apply (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n (p + 1)) :
    codifferentialOuterCLM w e p hp z
      (covectorExteriorCLM (2 * n - (p + 1)) ℓ (degreeStar w e z (p + 1) η)) =
      codifferentialCoefficientSymbolSucc w e z p ℓ η := by
  unfold codifferentialCoefficientSymbolSucc
  rw [dif_pos hp]
  change (-1 : ℝ) • castForm _
    (degreeStar w e z (2 * n - (p + 1) + 1)
      (covectorExteriorCLM (2 * n - (p + 1)) ℓ (degreeStar w e z (p + 1) η))) =
    -(castForm _ (degreeStar w e z (2 * n - p)
      (castForm _ (covectorExteriorCLM (2 * n - (p + 1)) ℓ (degreeStar w e z (p + 1) η)))))
  rw [degreeStar_cast_input, castForm_castForm]
  exact neg_one_smul ℝ _

/-- The actual local positive-degree codifferential has its genuine zero and first quadratic jets. -/
theorem localCodifferential_quadratic_product_jet
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (A : ComplexModel n → FormCoefficients n (p + 1)) (hA : ContDiffAt ℝ 2 A z) :
    localCodifferentialSucc w e p hp (fun y => quadraticScalar z ℓ y • A y) z = 0 ∧
      fderiv ℝ (localCodifferentialSucc w e p hp (fun y => quadraticScalar z ℓ y • A y)) z =
        ℓ.smulRight (codifferentialCoefficientSymbolSucc w e z p ℓ (A z)) := by
  let B := fun y => degreeStar w e y (p + 1) (A y)
  have hB : ContDiffAt ℝ 2 B z :=
    (((degreeStar_smooth w hw e (p + 1)).contDiffAt
      (e.val.open_target.mem_nhds hz)).of_le (m := 2) (by exact WithTop.coe_le_coe.mpr le_top)).clm_apply hA
  let U := fun y => extDeriv (fun x => quadraticScalar z ℓ x • B x) y
  have hjet := extDeriv_quadratic_product_jet z ℓ B hB
  let T : (ComplexModel n →L[ℝ] FormCoefficients n (2 * n - (p + 1))) →L[ℝ]
      FormCoefficients n (2 * n - (p + 1) + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hQB : ContDiffAt ℝ 2 (fun x => quadraticScalar z ℓ x • B x) z :=
    ((quadraticScalar_contDiff z ℓ).contDiffAt.of_le (m := 2) (by exact WithTop.coe_le_coe.mpr le_top)).smul hB
  have hDU := (hQB.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hUd : DifferentiableAt ℝ U z := T.differentiableAt.comp z hDU
  let C := codifferentialOuterCLM w e p hp
  have hCd : DifferentiableAt ℝ C z :=
    ((codifferentialOuter_smooth w hw e p hp).contDiffAt
      (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have heq : localCodifferentialSucc w e p hp (fun y => quadraticScalar z ℓ y • A y) =
      (fun y => C y (U y)) := by
    funext y
    have hi : (fun x => degreeStar w e x (p + 1) (quadraticScalar z ℓ x • A x)) =
        (fun x => quadraticScalar z ℓ x • B x) := by
      funext x
      exact map_smul (degreeStar w e x (p + 1)) _ _
    unfold localCodifferentialSucc
    rw [hi]
    rfl
  constructor
  · rw [congrFun heq z]
    rw [show U z = 0 from hjet.1, map_zero]
  · rw [heq, fderiv_clm_apply hCd hUd, show U z = 0 from hjet.1, map_zero, add_zero]
    change (C z).comp (fderiv ℝ U z) = _
    rw [show fderiv ℝ U z = ℓ.smulRight (covectorExteriorCLM (2 * n - (p + 1)) ℓ (B z)) from hjet.2]
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
      ContinuousLinearMap.smulRight_apply]
    congr 1
    exact codifferentialOuter_covector_apply w e p hp z ℓ (A z)


/-- Actual zero-first-jet local codifferential evaluation, using genuine field differentiation. -/
theorem localCodifferentialSucc_value_from_first_jet
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n)
    (z : ComplexModel n) (hz : z ∈ e.val.target) (ℓ : ComplexModel n →L[ℝ] ℝ)
    (V : ComplexModel n → FormCoefficients n (p + 1)) (hV : DifferentiableAt ℝ V z)
    (hV0 : V z = 0) (η : FormCoefficients n (p + 1))
    (hDV : fderiv ℝ V z = ℓ.smulRight η) :
    localCodifferentialSucc w e p hp V z = codifferentialCoefficientSymbolSucc w e z p ℓ η := by
  have hS := ((degreeStar_smooth w hw e (p + 1)).contDiffAt
    (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hd := fderiv_clm_apply hS hV
  rw [hV0, map_zero, add_zero, hDV] at hd
  have he : extDeriv (fun y => degreeStar w e y (p + 1) (V y)) z =
      covectorExteriorCLM (2 * n - (p + 1)) ℓ (degreeStar w e z (p + 1) η) := by
    change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
      (fderiv ℝ (fun y => degreeStar w e y (p + 1) (V y)) z) = _
    rw [hd]
    have hc : (degreeStar w e z (p + 1)).comp (ℓ.smulRight η) =
        ℓ.smulRight (degreeStar w e z (p + 1) η) := by
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
        ContinuousLinearMap.smulRight_apply]
    rw [hc, covectorExteriorCLM_apply]
    rfl
  change codifferentialOuterCLM w e p hp z
    (extDeriv (fun y => degreeStar w e y (p + 1) (V y)) z) = _
  rw [he]
  exact codifferentialOuter_covector_apply w e p hp z ℓ η

theorem localCodifferential_succ (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (A : ComplexModel n → FormCoefficients n (p + 1))
    (z : ComplexModel n) :
    castForm (Nat.add_sub_cancel p 1) (localCodifferential w e (p + 1) A z) =
      localCodifferentialSucc w e p hp A z := by
  simp only [localCodifferential, dif_neg (Nat.succ_ne_zero p), dif_pos hp]
  rfl

/-- Genuine natural-degree first-jet readback, including the excessive zero branch. -/
theorem localCodifferential_value_from_first_jet
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (ℓ : ComplexModel n →L[ℝ] ℝ)
    (V : ComplexModel n → FormCoefficients n (p + 1)) (hV : DifferentiableAt ℝ V z)
    (hV0 : V z = 0) (η : FormCoefficients n (p + 1))
    (hDV : fderiv ℝ V z = ℓ.smulRight η) :
    castForm (Nat.add_sub_cancel p 1) (localCodifferential w e (p + 1) V z) =
      codifferentialCoefficientSymbolSucc w e z p ℓ η := by
  by_cases hp : p + 1 ≤ 2 * n
  · rw [localCodifferential_succ w e p hp]
    exact localCodifferentialSucc_value_from_first_jet w hw e p hp z hz ℓ V hV hV0 η hDV
  · simp only [localCodifferential, dif_neg (Nat.succ_ne_zero p), dif_neg hp,
      codifferentialCoefficientSymbolSucc, map_zero, zero_apply]

/-- The actual δd quadratic summand in every natural input degree. -/
theorem localCodifferential_extDeriv_quadratic_product
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n → FormCoefficients n q)
    (hA : ContDiffAt ℝ 2 A z) :
    castForm (Nat.add_sub_cancel q 1)
      (localCodifferential w e (q + 1)
        (fun y => extDeriv (fun x => quadraticScalar z ℓ x • A x) y) z) =
      codifferentialCoefficientSymbolSucc w e z q ℓ (covectorExteriorCLM q ℓ (A z)) := by
  have hjet := extDeriv_quadratic_product_jet z ℓ A hA
  let T : (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hB : ContDiffAt ℝ 2 (fun y => quadraticScalar z ℓ y • A y) z :=
    ((quadraticScalar_contDiff z ℓ).contDiffAt.of_le (m := 2)
      (by exact WithTop.coe_le_coe.mpr le_top)).smul hA
  have hDV := (hB.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hV : DifferentiableAt ℝ (fun y => extDeriv (fun x => quadraticScalar z ℓ x • A x) y) z :=
    T.differentiableAt.comp z hDV
  exact localCodifferential_value_from_first_jet w hw e q z hz ℓ _ hV hjet.1 _ hjet.2

/-- The actual dδ quadratic summand, including the genuine excessive-input zero branch. -/
theorem extDeriv_localCodifferential_quadratic_product
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n → FormCoefficients n (p + 1))
    (hA : ContDiffAt ℝ 2 A z) :
    extDeriv (localCodifferential w e (p + 1)
      (fun y => quadraticScalar z ℓ y • A y)) z =
      covectorExteriorCLM p ℓ (codifferentialCoefficientSymbolSucc w e z p ℓ (A z)) := by
  by_cases hp : p + 1 ≤ 2 * n
  · have hjet := localCodifferential_quadratic_product_jet w hw e p hp z hz ℓ A hA
    have he : localCodifferential w e (p + 1)
        (fun y => quadraticScalar z ℓ y • A y) =
        localCodifferentialSucc w e p hp (fun y => quadraticScalar z ℓ y • A y) := by
      funext y
      exact localCodifferential_succ w e p hp _ y
    rw [he]
    change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
      (fderiv ℝ (localCodifferentialSucc w e p hp
        (fun y => quadraticScalar z ℓ y • A y)) z) = _
    rw [hjet.2, covectorExteriorCLM_apply]
    rfl
  · have he : localCodifferential w e (p + 1)
        (fun y => quadraticScalar z ℓ y • A y) =
        (fun _ : ComplexModel n => (0 : FormCoefficients n p)) := by
      funext y
      simp only [localCodifferential, dif_neg (Nat.succ_ne_zero p), dif_neg hp]
    rw [he]
    simp only [codifferentialCoefficientSymbolSucc, dif_neg hp, zero_apply, map_zero]
    change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
      (fderiv ℝ (fun _ : ComplexModel n => (0 : FormCoefficients n p)) z) = 0
    rw [fderiv_const_apply, map_zero]

/-- The true original second-order differential expression on every quadratic product. -/
theorem localHodgeLaplacian_quadratic_product
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (A : ComplexModel n → FormCoefficients n q)
    (hA : ContDiffAt ℝ 2 A z) :
    localHodgeLaplacian w e q (fun y => quadraticScalar z ℓ y • A y) z =
      -(ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) • A z) := by
  have hreal : localHodgeLaplacian w e q (fun y => quadraticScalar z ℓ y • A y) z =
      -(cliffordLaplacianSymbol w e z q ℓ (A z)) := by
    unfold localHodgeLaplacian
    rw [localCodifferential_extDeriv_quadratic_product w hw e q z hz ℓ A hA]
    cases q with
    | zero =>
      change codifferentialCoefficientSymbolSucc w e z 0 ℓ (covectorExteriorCLM 0 ℓ (A z)) + 0 =
        -(-(codifferentialCoefficientSymbolSucc w e z 0 ℓ (covectorExteriorCLM 0 ℓ (A z))) - 0)
      simp only [sub_zero, neg_neg, add_zero]
    | succ p =>
      simp only [dif_neg (Nat.succ_ne_zero p)]
      rw [extDeriv_localCodifferential_quadratic_product w hw e p z hz ℓ A hA]
      change codifferentialCoefficientSymbolSucc w e z (p + 1) ℓ
        (covectorExteriorCLM (p + 1) ℓ (A z)) +
        covectorExteriorCLM p ℓ (codifferentialCoefficientSymbolSucc w e z p ℓ (A z)) =
          -(-(codifferentialCoefficientSymbolSucc w e z (p + 1) ℓ
            (covectorExteriorCLM (p + 1) ℓ (A z))) -
              covectorExteriorCLM p ℓ (codifferentialCoefficientSymbolSucc w e z p ℓ (A z)))
      simp only [neg_sub, sub_neg_eq_add, add_comm]
  rw [hreal, cliffordLaplacianSymbol_eq_scalar w hw e z hz]
  rfl

/-- Raw real second-derivative principal coefficient, calibrated below to the actual differential operator. -/
def realPrincipalSymbol (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n q :=
  -(cliffordLaplacianSymbol w e z q ℓ)

/-- Calibration of the real symbol against the actual original second-order quadratic test. -/
theorem realPrincipalSymbol_eq_actual_quadratic_test
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n q) :
    realPrincipalSymbol w e z q ℓ η =
      localHodgeLaplacian w e q (fun y => quadraticScalar z ℓ y • η) z := by
  rw [localHodgeLaplacian_quadratic_product w hw e q z hz ℓ (fun _ => η) contDiffAt_const]
  unfold realPrincipalSymbol
  rw [cliffordLaplacianSymbol_eq_scalar w hw e z hz]
  rfl

/-- Entire original real principal coefficient has the genuine negative sign. -/
theorem realPrincipalSymbol_eq_scalar
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    realPrincipalSymbol w e z q ℓ =
      -(ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) •
        ContinuousLinearMap.id ℝ (FormCoefficients n q)) := by
  exact congrArg Neg.neg (cliffordLaplacianSymbol_eq_scalar w hw e z hz q ℓ)

/-- Under the conventional substitution ∂ ↦ iℓ, the two i factors reverse the real second-order sign. -/
def fourierPrincipalSymbol (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n q :=
  -(realPrincipalSymbol w e z q ℓ)

theorem fourierPrincipalSymbol_eq_clifford (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) :
    fourierPrincipalSymbol w e z q ℓ = cliffordLaplacianSymbol w e z q ℓ := by
  exact neg_neg _

/-- True Fourier positivity and two-sided continuous inverse, after actual differential calibration. -/
theorem fourierPrincipalSymbol_positive_inverse
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (q : ℕ) (ℓ : ComplexModel n →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) :
    (0 < ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ) ∧
      ∀ η : FormCoefficients n q, 0 ≤ formMetricCoefficients w e z q η
        (fourierPrincipalSymbol w e z q ℓ η)) ∧
    (((ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ))⁻¹ •
      ContinuousLinearMap.id ℝ (FormCoefficients n q)).comp
        (fourierPrincipalSymbol w e z q ℓ) = ContinuousLinearMap.id ℝ (FormCoefficients n q) ∧
      (fourierPrincipalSymbol w e z q ℓ).comp
        ((ℓ ((associatedMetricCLM (w.coeff e z)).inverse ℓ))⁻¹ •
          ContinuousLinearMap.id ℝ (FormCoefficients n q)) = ContinuousLinearMap.id ℝ (FormCoefficients n q)) := by
  rw [fourierPrincipalSymbol_eq_clifford]
  exact ⟨cliffordLaplacianSymbol_positive w hw e z hz q ℓ hℓ,
    cliffordLaplacianSymbol_inverse w hw e z hz q ℓ hℓ⟩

end SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgePrincipalSymbol
