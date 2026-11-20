import SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint

set_option autoImplicit false

/-! The actual original smooth Hodge Laplacian and integral Dirichlet identity. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeLaplacian

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  NaturalHermitianFormalAdjoint NaturalHermitianCodifferential
  NaturalHermitianHodgeStarSquare NaturalHermitianSmoothFormMetric
  NaturalOriginalGradedExteriorProduct ConstantFormProducts ProductTestForms
  XiaoComplexProducts IntegrationCurrent

variable {n p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedSpace

theorem exteriorProduct_add_left (A A' : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    exteriorProduct (A + A') B = exteriorProduct A B + exteriorProduct A' B := by
  apply smoothRealForm_ext
  intro e z
  exact wedgeTo_add_left rfl (A.coeff e z) (A'.coeff e z) (B.coeff e z)

theorem exteriorProduct_smul_left (c : ℝ) (A : SmoothRealForm n M p)
    (B : SmoothRealForm n M q) :
    exteriorProduct (c • A) B = c • exteriorProduct A B := by
  apply smoothRealForm_ext
  intro e z
  exact wedgeTo_smul_left rfl c (A.coeff e z) (B.coeff e z)

section Integral

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_symm (w : KahlerBackground n M) (q : ℕ)
    (A B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q A B = hodgeIntegralPairing w q B A := by
  unfold hodgeIntegralPairing
  split_ifs with hq
  · unfold topIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [hodgeProduct_topRatio, hodgeProduct_topRatio]
      rw [(formMetricCoefficients_positive w.form.val w.isKahler.1
        (complexChartAt x) ((complexChartAt (n := n) x).val x)
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)) q).1]
  · rfl

theorem hodgeIntegralPairing_add_left (w : KahlerBackground n M) (q : ℕ)
    (A A' B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q (A + A') B =
      hodgeIntegralPairing w q A B + hodgeIntegralPairing w q A' B := by
  unfold hodgeIntegralPairing
  split_ifs <;> simp only [exteriorProduct_add_left, map_add, topIntegral_add, add_zero]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_smul_left (w : KahlerBackground n M) (q : ℕ)
    (c : ℝ) (A B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q (c • A) B = c * hodgeIntegralPairing w q A B := by
  unfold hodgeIntegralPairing
  split_ifs <;> simp only [exteriorProduct_smul_left, map_smul, topIntegral_smul, mul_zero]

theorem hodgeIntegralPairing_add_right (w : KahlerBackground n M) (q : ℕ)
    (A B B' : SmoothRealForm n M q) :
    hodgeIntegralPairing w q A (B + B') =
      hodgeIntegralPairing w q A B + hodgeIntegralPairing w q A B' := by
  rw [hodgeIntegralPairing_symm, hodgeIntegralPairing_add_left,
    hodgeIntegralPairing_symm w q B A, hodgeIntegralPairing_symm w q B' A]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_smul_right (w : KahlerBackground n M) (q : ℕ)
    (c : ℝ) (A B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q A (c • B) = c * hodgeIntegralPairing w q A B := by
  rw [hodgeIntegralPairing_symm, hodgeIntegralPairing_smul_left,
    hodgeIntegralPairing_symm w q B A]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_zero_left (w : KahlerBackground n M) (q : ℕ)
    (B : SmoothRealForm n M q) : hodgeIntegralPairing w q 0 B = 0 := by
  rw [hodgeIntegralPairing_symm, hodgeIntegralPairing_zero_right]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_geometricallyEq_left (w : KahlerBackground n M) (q : ℕ)
    {A A' : SmoothRealForm n M q} (B : SmoothRealForm n M q) (h : A.GeometricallyEq A') :
    hodgeIntegralPairing w q A B = hodgeIntegralPairing w q A' B := by
  rw [hodgeIntegralPairing_symm, hodgeIntegralPairing_symm w q A' B]
  exact hodgeIntegralPairing_geometricallyEq_right w q B h

omit [BorelSpace M] in
theorem hodgeIntegralPairing_self_nonneg (w : KahlerBackground n M) (q : ℕ)
    (A : SmoothRealForm n M q) : 0 ≤ hodgeIntegralPairing w q A A := by
  unfold hodgeIntegralPairing
  split_ifs with hq
  · unfold topIntegral
    apply integral_nonneg
    intro x
    rw [hodgeProduct_topRatio]
    have hz := (complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)
    have hG : 0 ≤ formMetricCoefficients w.form.val (complexChartAt x)
        ((complexChartAt (n := n) x).val x) q
        (A.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x))
        (A.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x)) := by
      by_cases h0 : A.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x) = 0
      · simp only [h0, map_zero, le_refl]
      · exact ((formMetricCoefficients_positive w.form.val w.isKahler.1 _ _ hz q).2 _ h0).le
    exact mul_nonneg hG (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact le_refl _

end Integral

/-- The actual smooth Hodge Laplacian, with the absent degree-zero term genuinely zero. -/
def hodgeLaplacianForm (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ)
    (A : SmoothRealForm n M q) : SmoothRealForm n M q :=
  castSmoothForm (show (q + 1) - 1 = q by omega)
    (coderivativeForm w hw (q + 1) A.exteriorDerivative) +
  if hzero : q = 0 then 0 else
    castSmoothForm (show q - 1 + 1 = q by omega) (coderivativeForm w hw q A).exteriorDerivative

theorem hodgeLaplacianForm_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) {A B : SmoothRealForm n M q} (h : A.GeometricallyEq B) :
    (hodgeLaplacianForm w hw q A).GeometricallyEq (hodgeLaplacianForm w hw q B) := by
  have hc := castSmoothForm_geometricallyEq (show (q + 1) - 1 = q by omega)
    (coderivativeForm_geometricallyEq w hw (q + 1) h.exteriorDerivative)
  unfold hodgeLaplacianForm
  split_ifs with hzero
  · simpa only [add_zero] using hc
  · have hd := castSmoothForm_geometricallyEq (show q - 1 + 1 = q by omega)
      (coderivativeForm_geometricallyEq w hw q h).exteriorDerivative
    intro e z hz
    change _ + _ = _ + _
    rw [hc e hz, hd e hz]

theorem hodgeLaplacianForm_add_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (A B : SmoothRealForm n M q) :
    (hodgeLaplacianForm w hw q (A + B)).GeometricallyEq
      (hodgeLaplacianForm w hw q A + hodgeLaplacianForm w hw q B) := by
  have hc := castSmoothForm_geometricallyEq (show (q + 1) - 1 = q by omega)
    ((coderivativeForm_geometricallyEq w hw (q + 1)
      (exteriorDerivative_add_geometricallyEq A B)).trans
      (coderivativeForm_add_geometricallyEq w hw (q + 1) A.exteriorDerivative B.exteriorDerivative))
  rw [map_add] at hc
  unfold hodgeLaplacianForm
  split_ifs with hzero
  · simpa only [add_zero] using hc
  · have hd := castSmoothForm_geometricallyEq (show q - 1 + 1 = q by omega)
      ((coderivativeForm_add_geometricallyEq w hw q A B).exteriorDerivative.trans
        (exteriorDerivative_add_geometricallyEq (coderivativeForm w hw q A)
          (coderivativeForm w hw q B)))
    rw [map_add] at hd
    intro e z hz
    change _ + _ = (_ + _) + (_ + _)
    rw [hc e hz, hd e hz]
    simp only [coeff_add]
    abel_nf

theorem hodgeLaplacianForm_smul_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (c : ℝ) (A : SmoothRealForm n M q) :
    (hodgeLaplacianForm w hw q (c • A)).GeometricallyEq
      (c • hodgeLaplacianForm w hw q A) := by
  have hc := castSmoothForm_geometricallyEq (show (q + 1) - 1 = q by omega)
    (coderivativeForm_smul_geometricallyEq w hw (q + 1) c A.exteriorDerivative)
  rw [map_smul] at hc
  unfold hodgeLaplacianForm
  rw [exteriorDerivative_const_smul]
  split_ifs with hzero
  · simpa only [add_zero] using hc
  · have hd := castSmoothForm_geometricallyEq (show q - 1 + 1 = q by omega)
      (coderivativeForm_smul_geometricallyEq w hw q c A).exteriorDerivative
    rw [exteriorDerivative_const_smul, map_smul] at hd
    intro e z hz
    change _ + _ = c • (_ + _)
    rw [hc e hz, hd e hz, smul_add]
    simp only [coeff_smul]

section Dirichlet

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual two differential energies, with no nonexistent degree-zero predecessor. -/
def dirichletPairing (w : KahlerBackground n M) (q : ℕ) (A B : SmoothRealForm n M q) : ℝ :=
  hodgeIntegralPairing w (q + 1) A.exteriorDerivative B.exteriorDerivative +
  if q = 0 then 0 else
    hodgeIntegralPairing w (q - 1) (coderivativeForm w.form.val w.isKahler.1 q A)
      (coderivativeForm w.form.val w.isKahler.1 q B)

omit [BorelSpace M] in
theorem dirichletPairing_symm (w : KahlerBackground n M) (q : ℕ)
    (A B : SmoothRealForm n M q) : dirichletPairing w q A B = dirichletPairing w q B A := by
  unfold dirichletPairing
  by_cases hq : q = 0
  · rw [if_pos hq, if_pos hq]
    exact congrArg (fun t : ℝ => t + 0)
      (hodgeIntegralPairing_symm w (q + 1) A.exteriorDerivative B.exteriorDerivative)
  · rw [if_neg hq, if_neg hq]
    exact congrArg₂ (fun s t : ℝ => s + t)
      (hodgeIntegralPairing_symm w (q + 1) A.exteriorDerivative B.exteriorDerivative)
      (hodgeIntegralPairing_symm w (q - 1)
        (coderivativeForm w.form.val w.isKahler.1 q A)
        (coderivativeForm w.form.val w.isKahler.1 q B))

/-- The actual original integral adjoint proves the whole Dirichlet identity. -/
theorem hodgeLaplacian_dirichlet_identity (w : KahlerBackground n M) (q : ℕ)
    (A B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q (hodgeLaplacianForm w.form.val w.isKahler.1 q A) B =
      dirichletPairing w q A B := by
  have hf : hodgeIntegralPairing w q
      (castSmoothForm (show (q + 1) - 1 = q by omega)
        (coderivativeForm w.form.val w.isKahler.1 (q + 1) A.exteriorDerivative)) B =
      hodgeIntegralPairing w (q + 1) A.exteriorDerivative B.exteriorDerivative := by
    calc
      _ = hodgeIntegralPairing w q B
          (castSmoothForm (show (q + 1) - 1 = q by omega)
            (coderivativeForm w.form.val w.isKahler.1 (q + 1) A.exteriorDerivative)) :=
        hodgeIntegralPairing_symm w q _ B
      _ = hodgeIntegralPairing w (q + 1) B.exteriorDerivative A.exteriorDerivative :=
        (coderivative_integral_formal_adjoint w q B A.exteriorDerivative).symm
      _ = _ := hodgeIntegralPairing_symm w (q + 1) _ _
  unfold hodgeLaplacianForm dirichletPairing
  rw [hodgeIntegralPairing_add_left, hf]
  cases q with
  | zero =>
    change _ + hodgeIntegralPairing w 0 (0 : SmoothRealForm n M 0) B = _ + 0
    rw [hodgeIntegralPairing_zero_left]
  | succ r =>
    simp only [dif_neg (Nat.succ_ne_zero r), if_neg (Nat.succ_ne_zero r)]
    congr 1
    change hodgeIntegralPairing w (r + 1)
      (coderivativeForm w.form.val w.isKahler.1 (r + 1) A).exteriorDerivative B =
      hodgeIntegralPairing w r (coderivativeForm w.form.val w.isKahler.1 (r + 1) A)
        (coderivativeForm w.form.val w.isKahler.1 (r + 1) B)
    exact coderivative_integral_formal_adjoint w r _ B

/-- Integral formal symmetry of the actual original smooth Laplacian. -/
theorem hodgeLaplacian_integral_symm (w : KahlerBackground n M) (q : ℕ)
    (A B : SmoothRealForm n M q) :
    hodgeIntegralPairing w q (hodgeLaplacianForm w.form.val w.isKahler.1 q A) B =
      hodgeIntegralPairing w q A (hodgeLaplacianForm w.form.val w.isKahler.1 q B) := by
  rw [hodgeLaplacian_dirichlet_identity, dirichletPairing_symm,
    hodgeIntegralPairing_symm w q A _, hodgeLaplacian_dirichlet_identity]

/-- Genuine nonnegative original Laplacian integral energy, in every natural degree. -/
theorem hodgeLaplacian_integral_nonneg (w : KahlerBackground n M) (q : ℕ)
    (A : SmoothRealForm n M q) :
    0 ≤ hodgeIntegralPairing w q (hodgeLaplacianForm w.form.val w.isKahler.1 q A) A := by
  rw [hodgeLaplacian_dirichlet_identity]
  unfold dirichletPairing
  split_ifs
  · exact add_nonneg (hodgeIntegralPairing_self_nonneg w (q + 1) _) (le_refl 0)
  · exact add_nonneg (hodgeIntegralPairing_self_nonneg w (q + 1) _)
      (hodgeIntegralPairing_self_nonneg w (q - 1) _)

end Dirichlet

end SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeLaplacian
