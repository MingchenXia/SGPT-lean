import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgePrincipalSymbol

set_option autoImplicit false

/-! Full actual original codifferential first-order coefficients and internally produced freezing bounds. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFirstOrderCoefficients

open FirstPass FirstPass.MongeAmpere NaturalHermitianHodgePrincipalSymbol
  NaturalHermitianExteriorCliffordSymbol NaturalHermitianHodgeStarSquare
  NaturalHermitianOrthonormalFormBasis NaturalHermitianMetricCoefficients
  NaturalHermitianMusicalInverse NaturalHermitianOriginalFormMetric NaturalHermitianSmoothFormMetric
  ConstantFormProducts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formOperatorNormedAddCommGroup (q r : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formOperatorNormedSpace (q r : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedSpace

local instance jetNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (ComplexModel n →L[ℝ] FormCoefficients n q) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetNormedSpace (q : ℕ) :
    NormedSpace ℝ (ComplexModel n →L[ℝ] FormCoefficients n q) :=
  ContinuousLinearMap.toNormedSpace

local instance jetOperatorNormedAddCommGroup (q r : ℕ) :
    NormedAddCommGroup ((ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ]
      ComplexModel n →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetOperatorNormedSpace (q r : ℕ) :
    NormedSpace ℝ ((ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ]
      ComplexModel n →L[ℝ] FormCoefficients n r) :=
  ContinuousLinearMap.toNormedSpace

/-- Complete principal coefficient map on the original full positive-degree jet space. -/
def principalJetSuccCLM (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) :
    (ComplexModel n →L[ℝ] FormCoefficients n (p + 1)) →L[ℝ] FormCoefficients n p :=
  (codifferentialOuterCLM w e p hp z).comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).comp
      ((ContinuousLinearMap.compL ℝ (ComplexModel n) (FormCoefficients n (p + 1))
        (FormCoefficients n (2 * n - (p + 1)))) (degreeStar w e z (p + 1))))

/-- The actual differentiated star field supplies the complete zero-order coefficient map. -/
def zeroOrderSuccCLM (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) :
    FormCoefficients n (p + 1) →L[ℝ] FormCoefficients n p :=
  (codifferentialOuterCLM w e p hp z).comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ).comp
      (fderiv ℝ (fun y => degreeStar w e y (p + 1)) z).flip)

/-- Entire actual codifferential first jet; no star derivative or lower-order term is omitted. -/
theorem localCodifferentialSucc_eq_first_jet
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n → FormCoefficients n (p + 1)) (hA : DifferentiableAt ℝ A z) :
    localCodifferentialSucc w e p hp A z =
      principalJetSuccCLM w e p hp z (fderiv ℝ A z) + zeroOrderSuccCLM w e p hp z (A z) := by
  have hS := ((degreeStar_smooth w hw e (p + 1)).contDiffAt
    (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hd := fderiv_clm_apply hS hA
  let T : (ComplexModel n →L[ℝ] FormCoefficients n (2 * n - (p + 1))) →L[ℝ]
      FormCoefficients n (2 * n - (p + 1) + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  change codifferentialOuterCLM w e p hp z
    (T (fderiv ℝ (fun y => degreeStar w e y (p + 1) (A y)) z)) = _
  rw [hd, map_add, map_add]
  rfl

/-- Natural-degree full original principal jet map, with genuine degree-zero and excessive branches. -/
def principalJetCLM (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (z : ComplexModel n) :
    (ComplexModel n →L[ℝ] FormCoefficients n q) →L[ℝ] FormCoefficients n (q - 1) :=
  match q with
  | 0 => 0
  | p + 1 => if hp : p + 1 ≤ 2 * n then principalJetSuccCLM w e p hp z else 0

/-- Natural-degree actual original zero-order coefficient, including its two actual zero branches. -/
def zeroOrderCLM (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (q : ℕ) (z : ComplexModel n) :
    FormCoefficients n q →L[ℝ] FormCoefficients n (q - 1) :=
  match q with
  | 0 => 0
  | p + 1 => if hp : p + 1 ≤ 2 * n then zeroOrderSuccCLM w e p hp z else 0

/-- Genuine complete first-order expression of the actual codifferential in every natural degree. -/
theorem localCodifferential_eq_first_jet
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (A : ComplexModel n → FormCoefficients n q) (hA : DifferentiableAt ℝ A z) :
    localCodifferential w e q A z =
      principalJetCLM w e q z (fderiv ℝ A z) + zeroOrderCLM w e q z (A z) := by
  cases q with
  | zero =>
    simp [localCodifferential, principalJetCLM, zeroOrderCLM]
  | succ p =>
    by_cases hp : p + 1 ≤ 2 * n
    · have h := localCodifferentialSucc_eq_first_jet w hw e p hp z hz A hA
      simpa [localCodifferential, principalJetCLM, zeroOrderCLM, hp] using h
    · simp only [localCodifferential, dif_neg (Nat.succ_ne_zero p), dif_neg hp,
        principalJetCLM, zeroOrderCLM, zero_apply, add_zero]

/-- Entire original finite coordinate decomposition of every original continuous first jet. -/
theorem originalJet_eq_coordinate_sum
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (L : ComplexModel n →L[ℝ] FormCoefficients n q) :
    L = ∑ i, (coordinateCovector b i).smulRight (L (b i)) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [sum_apply]
  change L u = ∑ i, b.repr u i • L (b i)
  simpa only [map_sum, map_smul] using (congrArg L (b.sum_repr u)).symm

/-- Literal rank-one evaluation, before invoking the genuine metric insertion calibration. -/
theorem principalJetSucc_rank_one
    (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n (p + 1)) :
    principalJetSuccCLM w e p hp z (ℓ.smulRight η) =
      codifferentialCoefficientSymbolSucc w e z p ℓ η := by
  have hc : (degreeStar w e z (p + 1)).comp (ℓ.smulRight η) =
      ℓ.smulRight (degreeStar w e z (p + 1) η) := by
    apply ContinuousLinearMap.ext
    intro u
    exact map_smul (degreeStar w e z (p + 1)) (ℓ u) η
  change codifferentialOuterCLM w e p hp z
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
      ((degreeStar w e z (p + 1)).comp (ℓ.smulRight η))) = _
  rw [hc]
  simpa only [covectorExteriorCLM_apply, ClosedProductCurrents.oneWedge,
    ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using
    codifferentialOuter_covector_apply w e p hp z ℓ η

/-- Whole original covector principal coefficient, including the negative insertion sign. -/
theorem principalJetSucc_covector_apply
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (ℓ : ComplexModel n →L[ℝ] ℝ) (η : FormCoefficients n (p + 1)) :
    principalJetSuccCLM w e p hp z (ℓ.smulRight η) =
      codifferentialCoefficientSymbolSucc w e z p ℓ η ∧
    principalJetSuccCLM w e p hp z (ℓ.smulRight η) =
      -interiorSuccCLM p ((associatedMetricCLM (w.coeff e z)).inverse ℓ) η := by
  refine ⟨principalJetSucc_rank_one w e p hp z ℓ η, ?_⟩
  rw [principalJetSucc_rank_one, codifferentialCoefficientSymbolSucc_eq_neg_interior w hw e z hz]
  rfl

/-- Entire principal jet evaluated as the actual finite sum of covector coefficients. -/
theorem principalJetSucc_eq_coordinate_sum
    (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (z : ComplexModel n)
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (L : ComplexModel n →L[ℝ] FormCoefficients n (p + 1)) :
    principalJetSuccCLM w e p hp z L =
      ∑ i, codifferentialCoefficientSymbolSucc w e z p (coordinateCovector b i) (L (b i)) := by
  conv_lhs => rw [originalJet_eq_coordinate_sum b (p + 1) L, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact principalJetSucc_rank_one w e p hp z (coordinateCovector b i) (L (b i))

/-- The original exterior differential is the finite coordinate alternation of its entire jet. -/
theorem extDeriv_eq_coordinate_sum
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ)
    (A : ComplexModel n → FormCoefficients n q) (z : ComplexModel n) :
    extDeriv A z = ∑ i, covectorExteriorCLM q (coordinateCovector b i) (fderiv ℝ A z (b i)) := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
    (fderiv ℝ A z) = _
  conv_lhs => rw [originalJet_eq_coordinate_sum b q (fderiv ℝ A z), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (covectorExteriorCLM_apply q (coordinateCovector b i) (fderiv ℝ A z (b i))).symm

/-- Entire original operator-norm smoothness of the positive-degree principal coefficient. -/
theorem principalJetSucc_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n) :
    ContDiffOn ℝ ∞ (principalJetSuccCLM w e p hp) e.val.target := by
  let T : (ComplexModel n →L[ℝ] FormCoefficients n (2 * n - (p + 1))) →L[ℝ]
      FormCoefficients n (2 * n - (p + 1) + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hinner := (ContinuousLinearMap.compL ℝ (ComplexModel n)
    (FormCoefficients n (p + 1)) (FormCoefficients n (2 * n - (p + 1)))).contDiff.comp_contDiffOn
      (degreeStar_smooth w hw e (p + 1))
  exact (codifferentialOuter_smooth w hw e p hp).clm_comp
    ((contDiffOn_const (c := T)).clm_comp hinner)

/-- The differentiated star supplies an actually smooth whole original zero-order coefficient. -/
theorem zeroOrderSucc_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (p : ℕ) (hp : p + 1 ≤ 2 * n) :
    ContDiffOn ℝ ∞ (zeroOrderSuccCLM w e p hp) e.val.target := by
  let T : (ComplexModel n →L[ℝ] FormCoefficients n (2 * n - (p + 1))) →L[ℝ]
      FormCoefficients n (2 * n - (p + 1) + 1) :=
    ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (fun y => degreeStar w e y (p + 1))) e.val.target :=
    (contDiffOn_infty_iff_fderiv_of_isOpen e.val.open_target).mp
      (degreeStar_smooth w hw e (p + 1)) |>.2
  let F := (ContinuousLinearMap.flipₗᵢ ℝ (ComplexModel n)
    (FormCoefficients n (p + 1)) (FormCoefficients n (2 * n - (p + 1)))).toContinuousLinearEquiv.toContinuousLinearMap
  have hf := F.contDiff.comp_contDiffOn hd
  exact (codifferentialOuter_smooth w hw e p hp).clm_comp
    ((contDiffOn_const (c := T)).clm_comp hf)

/-- All natural degrees retain entire operator-norm smoothness, including actual zero branches. -/
theorem principalJet_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (principalJetCLM w e q) e.val.target := by
  cases q with
  | zero => exact contDiffOn_const
  | succ p =>
    change ContDiffOn ℝ ∞ (fun z => if hp : p + 1 ≤ 2 * n then
      principalJetSuccCLM w e p hp z else 0) e.val.target
    by_cases hp : p + 1 ≤ 2 * n
    · simpa only [dif_pos hp] using principalJetSucc_smooth w hw e p hp
    · simpa only [dif_neg hp] using
        (contDiffOn_const (c := (0 : (ComplexModel n →L[ℝ] FormCoefficients n (p + 1)) →L[ℝ]
          FormCoefficients n p)) (𝕜 := ℝ) (n := ∞) (s := e.val.target))

/-- Every whole natural-degree zero-order field is smooth in the unchanged original norm. -/
theorem zeroOrder_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (zeroOrderCLM w e q) e.val.target := by
  cases q with
  | zero => exact contDiffOn_const
  | succ p =>
    change ContDiffOn ℝ ∞ (fun z => if hp : p + 1 ≤ 2 * n then
      zeroOrderSuccCLM w e p hp z else 0) e.val.target
    by_cases hp : p + 1 ≤ 2 * n
    · simpa only [dif_pos hp] using zeroOrderSucc_smooth w hw e p hp
    · simpa only [dif_neg hp] using
        (contDiffOn_const (c := (0 : FormCoefficients n (p + 1) →L[ℝ] FormCoefficients n p))
          (𝕜 := ℝ) (n := ∞) (s := e.val.target))

/-- Genuine local uniform freezing constants, internally derived from the actual whole coefficient fields. -/
theorem exists_original_local_first_order_freezing_estimate
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∃ C > 0, Metric.ball z r ⊆ e.val.target ∧
      ∀ y ∈ Metric.ball z r,
        ‖principalJetCLM w e q y - principalJetCLM w e q z‖ ≤ ε ∧
        ‖zeroOrderCLM w e q y‖ ≤ C ∧
        ∀ A : ComplexModel n → FormCoefficients n q, DifferentiableAt ℝ A y →
          ‖localCodifferential w e q A y - principalJetCLM w e q z (fderiv ℝ A y)‖ ≤
            ε * ‖fderiv ℝ A y‖ + C * ‖A y‖ := by
  have hP := (principalJet_smooth w hw e q).continuousOn.continuousAt
    (e.val.open_target.mem_nhds hz)
  have hZ := (zeroOrder_smooth w hw e q).continuousOn.continuousAt
    (e.val.open_target.mem_nhds hz)
  have hPn : ∀ᶠ y in 𝓝 z,
      ‖principalJetCLM w e q y - principalJetCLM w e q z‖ < ε :=
    (hP.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simpa using hε))
  have hZn : ∀ᶠ y in 𝓝 z, ‖zeroOrderCLM w e q y - zeroOrderCLM w e q z‖ < 1 :=
    (hZ.sub continuousAt_const).norm.eventually (gt_mem_nhds (by simp))
  have hn : {y | y ∈ e.val.target ∧
      ‖principalJetCLM w e q y - principalJetCLM w e q z‖ < ε ∧
      ‖zeroOrderCLM w e q y - zeroOrderCLM w e q z‖ < 1} ∈ 𝓝 z :=
    inter_mem (e.val.open_target.mem_nhds hz) (hPn.and hZn)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, 1 + ‖zeroOrderCLM w e q z‖, by positivity,
    fun y hy => (hball hy).1, ?_⟩
  intro y hy
  have hy' := hball hy
  have hZle : ‖zeroOrderCLM w e q y‖ ≤ 1 + ‖zeroOrderCLM w e q z‖ := by
    calc
      ‖zeroOrderCLM w e q y‖ =
          ‖(zeroOrderCLM w e q y - zeroOrderCLM w e q z) + zeroOrderCLM w e q z‖ :=
        congrArg norm (sub_add_cancel _ _).symm
      _ ≤ ‖zeroOrderCLM w e q y - zeroOrderCLM w e q z‖ + ‖zeroOrderCLM w e q z‖ :=
        norm_add_le _ _
      _ ≤ 1 + ‖zeroOrderCLM w e q z‖ := add_le_add hy'.2.2.le (le_refl _)
  refine ⟨hy'.2.1.le, hZle, ?_⟩
  intro A hA
  have heq : localCodifferential w e q A y - principalJetCLM w e q z (fderiv ℝ A y) =
      (principalJetCLM w e q y - principalJetCLM w e q z) (fderiv ℝ A y) +
        zeroOrderCLM w e q y (A y) := by
    rw [localCodifferential_eq_first_jet w hw e q y hy'.1 A hA,
      sub_apply]
    abel
  rw [heq]
  calc
    _ ≤ ‖(principalJetCLM w e q y - principalJetCLM w e q z) (fderiv ℝ A y)‖ +
        ‖zeroOrderCLM w e q y (A y)‖ := norm_add_le _ _
    _ ≤ ‖principalJetCLM w e q y - principalJetCLM w e q z‖ * ‖fderiv ℝ A y‖ +
        ‖zeroOrderCLM w e q y‖ * ‖A y‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ε * ‖fderiv ℝ A y‖ + (1 + ‖zeroOrderCLM w e q z‖) * ‖A y‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hy'.2.1.le (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hZle (norm_nonneg _))

/-- The same internally produced constants bound the literal original global codifferential coefficients. -/
theorem exists_original_global_form_first_order_freezing_estimate
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (q : ℕ) (z : ComplexModel n) (hz : z ∈ e.val.target) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∃ C > 0, Metric.ball z r ⊆ e.val.target ∧
      ∀ y ∈ Metric.ball z r, ∀ A : SmoothRealForm n M q,
        ‖(NaturalHermitianCodifferential.coderivativeForm w hw q A).coeff e y -
            principalJetCLM w e q z (fderiv ℝ (A.coeff e) y)‖ ≤
          ε * ‖fderiv ℝ (A.coeff e) y‖ + C * ‖A.coeff e y‖ := by
  obtain ⟨r, hr, C, hC, ht, hbound⟩ :=
    exists_original_local_first_order_freezing_estimate w hw e q z hz ε hε
  refine ⟨r, hr, C, hC, ht, ?_⟩
  intro y hy A
  have hA := ((A.smooth e).contDiffAt (e.val.open_target.mem_nhds (ht hy))).differentiableAt
    (by simp)
  simpa only [localCodifferential_eq_original_coeff w hw e q A y] using
    (hbound y hy).2.2 (A.coeff e) hA

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFirstOrderCoefficients
