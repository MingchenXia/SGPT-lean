import SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential
import SGPT.Foundations.Analysis.Pending.XiaoGlobalStokes
import SGPT.Foundations.Analysis.Pending.XiaoComplexProducts

set_option autoImplicit false

/-! The actual full exterior product rule and original integral codifferential adjoint. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint

open FirstPass FirstPass.PositiveClasses NaturalHermitianCodifferential
  NaturalHermitianHodgeStarSquare NaturalHermitianHodgeStar NaturalHermitianSmoothFormMetric
  NaturalOriginalGradedExteriorProduct ConstantFormProducts ProductTestForms
  ClosedProductCurrents XiaoComplexProducts IntegrationCurrent TopDegreeDensity
  StronglyPositiveForms CoordinateWedgeAssoc FirstPass.MongeAmpere

variable {n p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (k : ℕ) : NormedSpace ℝ (FormCoefficients n k) :=
  ContinuousAlternatingMap.instNormedSpace

/-- Actual differentiation of the original continuous bilinear exterior product. -/
theorem fderiv_coordinateWedge {A : ComplexModel n → FormCoefficients n p}
    {B : ComplexModel n → FormCoefficients n q} {z : ComplexModel n}
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z) (u : ComplexModel n) :
    fderiv ℝ (fun y => coordinateWedge (A y) (B y)) z u =
      coordinateWedge (A z) (fderiv ℝ B z u) + coordinateWedge (fderiv ℝ A z u) (B z) := by
  have hd := ((exteriorProductCLM n p q).hasFDerivAt.comp z hA.hasFDerivAt).clm_apply hB.hasFDerivAt
  have hu := congrArg (fun L => L u) hd.fderiv
  exact hu

/-- Actual left reassociation of the one-covector exterior product on whole original tensors. -/
theorem oneWedge_coordinateWedge_left (ℓ : ComplexModel n →L[ℝ] ℝ)
    (A : FormCoefficients n p) (B : FormCoefficients n q) :
    oneWedge ℓ (coordinateWedge A B) =
      wedgeTo (show (p + 1) + q = (p + q) + 1 by omega) (oneWedge ℓ A) B := by
  rw [← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 (p + q))]
  change wedgeTo _ (oneForm n ℓ) (wedgeTo rfl A B) = _
  rw [← wedgeTo_assoc (Nat.add_comm 1 p) (by omega) rfl (Nat.add_comm 1 (p + q)),
    wedgeTo_oneForm_eq_oneWedge]

/-- The real graded sign moves the actual one-covector derivative past any entire p-tensor. -/
theorem oneWedge_coordinateWedge_right (ℓ : ComplexModel n →L[ℝ] ℝ)
    (A : FormCoefficients n p) (B : FormCoefficients n q) :
    oneWedge ℓ (coordinateWedge A B) =
      (-1 : ℝ) ^ p • wedgeTo (show p + (q + 1) = (p + q) + 1 by omega) A (oneWedge ℓ B) := by
  rw [oneWedge_coordinateWedge_left, ← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 p),
    wedgeTo_graded_comm (Nat.add_comm 1 p) rfl (oneForm n ℓ) A, wedgeTo_smul_left,
    wedgeTo_assoc rfl (by omega) (Nat.add_comm 1 q) (by omega), wedgeTo_oneForm_eq_oneWedge]
  simp only [Nat.one_mul]

/-- The genuine original arbitrary-degree exterior Leibniz rule on entire coefficient tensors. -/
theorem extDeriv_coordinateWedge {A : ComplexModel n → FormCoefficients n p}
    {B : ComplexModel n → FormCoefficients n q} {z : ComplexModel n}
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z) :
    extDeriv (fun y => coordinateWedge (A y) (B y)) z =
      wedgeTo (show (p + 1) + q = (p + q) + 1 by omega) (extDeriv A z) (B z) +
      (-1 : ℝ) ^ p • wedgeTo (show p + (q + 1) = (p + q) + 1 by omega) (A z) (extDeriv B z) := by
  rw [extDeriv_eq_sum_oneWedge]
  simp_rw [fderiv_coordinateWedge hA hB]
  have hadd (ℓ : ComplexModel n →L[ℝ] ℝ) (F G : FormCoefficients n (p + q)) :
      oneWedge ℓ (F + G) = oneWedge ℓ F + oneWedge ℓ G := by
    rw [← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 (p + q)), wedgeTo_add_right,
      wedgeTo_oneForm_eq_oneWedge, wedgeTo_oneForm_eq_oneWedge]
  simp_rw [hadd]
  rw [Finset.sum_add_distrib]
  simp_rw [oneWedge_coordinateWedge_right (A := A z), oneWedge_coordinateWedge_left (B := B z)]
  rw [← Finset.smul_sum, ← wedgeTo_sum_right, ← wedgeTo_sum_left,
    ← extDeriv_eq_sum_oneWedge, ← extDeriv_eq_sum_oneWedge]
  exact add_comm _ _

/-- The genuine exterior derivative obeys the full product rule on original chart targets. -/
theorem exteriorProduct_derivative_geometricallyEq (A : SmoothRealForm n M p)
    (B : SmoothRealForm n M q) :
    (exteriorProduct A B).exteriorDerivative.GeometricallyEq
      (castSmoothForm (show (p + 1) + q = (p + q) + 1 by omega)
        (exteriorProduct A.exteriorDerivative B) +
      (-1 : ℝ) ^ p • castSmoothForm (show p + (q + 1) = (p + q) + 1 by omega)
        (exteriorProduct A B.exteriorDerivative)) := by
  intro e z hz
  change extDeriv (fun y => coordinateWedge (A.coeff e y) (B.coeff e y)) z =
    (castSmoothForm _ (exteriorProduct A.exteriorDerivative B)).coeff e z +
      (-1 : ℝ) ^ p • (castSmoothForm _ (exteriorProduct A B.exteriorDerivative)).coeff e z
  rw [castSmoothForm_coeff, castSmoothForm_coeff, exteriorProduct_coeff, exteriorProduct_coeff]
  exact extDeriv_coordinateWedge
    (((A.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))
    (((B.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))

theorem topRatio_geometricallyEq (w : SmoothRealForm n M 2)
    {A B : SmoothRealForm n M (2 * n)} (h : A.GeometricallyEq B) :
    topRatio w A = topRatio w B := by
  funext x
  unfold topRatio chartRatio
  rw [h _ ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))]

theorem exteriorProduct_geometricallyEq {A A' : SmoothRealForm n M p}
    {B B' : SmoothRealForm n M q} (hA : A.GeometricallyEq A')
    (hB : B.GeometricallyEq B') :
    (exteriorProduct A B).GeometricallyEq (exteriorProduct A' B') := by
  intro e z hz
  simp only [exteriorProduct_coeff, hA e hz, hB e hz]

theorem exteriorProduct_zero_right (A : SmoothRealForm n M p) :
    exteriorProduct A (0 : SmoothRealForm n M q) = 0 := by
  apply smoothRealForm_ext
  intro e z
  change coordinateWedge (A.coeff e z) 0 = 0
  exact wedgeTo_zero_right rfl _

theorem exteriorProduct_smul_right (c : ℝ) (A : SmoothRealForm n M p)
    (B : SmoothRealForm n M q) :
    exteriorProduct A (c • B) = c • exteriorProduct A B := by
  apply smoothRealForm_ext
  intro e z
  change coordinateWedge (A.coeff e z) (c • B.coeff e z) =
    c • coordinateWedge (A.coeff e z) (B.coeff e z)
  exact wedgeTo_smul_right rfl c _ _

theorem exteriorProduct_cast_right {q' : ℕ} (h : q = q')
    (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    exteriorProduct A (castSmoothForm h B) =
      castSmoothForm (congrArg (fun k => p + k) h) (exteriorProduct A B) := by
  subst h
  rfl

/-- Exact normalization against the original unnormalized top power. -/
theorem metricVolumeDensity_eq_formPow (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) :
    metricVolumeDensity w e z =
      (n.factorial : ℝ)⁻¹ * topDensity ((formPow w n).coeff e z) := by
  rw [metricVolumeDensity_eq, NaturalHermitianTopFormOrientation.normalizedHermitianTopForm_coeff,
    formPow_coeff, topDensity_formPower]
  rfl

/-- The entire original star product has the actual normalized metric top ratio. -/
theorem hodgeProduct_topRatio (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (p : ℕ) (hp : p ≤ 2 * n) (A B : SmoothRealForm n M p) (x : M) :
    topRatio w (castSmoothForm (Nat.add_sub_of_le hp)
      (exteriorProduct A (degreeHodgeStarForm w hw p hp B))) x =
      formMetricCoefficients w (complexChartAt x) ((complexChartAt (n := n) x).val x) p
        (A.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x))
        (B.coeff (complexChartAt x) ((complexChartAt (n := n) x).val x)) *
        (n.factorial : ℝ)⁻¹ := by
  let e := complexChartAt (n := n) x
  let z := e.val x
  have hz : z ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hd := (topDensity_formPow_pos hw hz).ne'
  unfold topRatio chartRatio
  rw [castSmoothForm_coeff, exteriorProduct_coeff, degreeHodgeStarForm_coeff]
  change topDensity (wedgeTo (Nat.add_sub_of_le hp) (A.coeff e z)
    (degreeStar w e z p (B.coeff e z))) / topDensity ((formPow w n).coeff e z) = _
  rw [degreeStar_wedge_identity w hw e z hz p hp, topDensity_smul]
  change _ * metricVolumeDensity w e z / topDensity ((formPow w n).coeff e z) = _
  rw [metricVolumeDensity_eq_formPow]
  field_simp
  rfl

theorem neg_one_pow_complement_product (n p : ℕ) (hp : p ≤ 2 * n) :
    (-1 : ℝ) ^ ((2 * n - p) * p) = (-1 : ℝ) ^ p := by
  rw [neg_one_pow_eq_pow_mod_two ((2 * n - p) * p), neg_one_pow_eq_pow_mod_two p]
  have hmod : (2 * n - p) % 2 = p % 2 := by omega
  rw [Nat.mul_mod, hmod]
  have hpmod : p % 2 = 0 ∨ p % 2 = 1 := by omega
  rcases hpmod with h | h <;> simp [h]

/-- The actual middle squared star gives the even-dimensional integration sign. -/
theorem star_coderivativeSucc_integral_sign (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (B : SmoothRealForm n M (p + 1)) :
    (degreeHodgeStarForm w hw p (by omega) (coderivativeSucc w hw p hp B)).GeometricallyEq
      ((-1 : ℝ) ^ (p + 1) •
        castSmoothForm (show 2 * n - (p + 1) + 1 = 2 * n - p by omega)
          (degreeHodgeStarForm w hw (p + 1) hp B).exteriorDerivative) := by
  have h := star_coderivativeSucc_geometricallyEq w hw p hp B
  have hs : (-1 : ℝ) * (-1 : ℝ) ^ ((2 * n - (p + 1) + 1) * p) =
      (-1 : ℝ) ^ (p + 1) := by
    rw [show 2 * n - (p + 1) + 1 = 2 * n - p by omega,
      neg_one_pow_complement_product n p (by omega), pow_succ, mul_comm]
  rw [hs] at h
  exact h

section Integral

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual integral of an original smooth top form. -/
def topIntegral (w : KahlerBackground n M) (A : SmoothRealForm n M (2 * n)) : ℝ :=
  ∫ x, topRatio w.form.val A x ∂(kahlerVolume w)

omit [BorelSpace M] in
theorem topIntegral_geometricallyEq (w : KahlerBackground n M)
    {A B : SmoothRealForm n M (2 * n)} (h : A.GeometricallyEq B) :
    topIntegral w A = topIntegral w B := by
  unfold topIntegral
  rw [topRatio_geometricallyEq w.form.val h]

omit [BorelSpace M] in
theorem topIntegral_zero (w : KahlerBackground n M) :
    topIntegral w (0 : SmoothRealForm n M (2 * n)) = 0 := by
  simp [topIntegral, topRatio, chartRatio, topDensity]

theorem topIntegral_add (w : KahlerBackground n M) (A B : SmoothRealForm n M (2 * n)) :
    topIntegral w (A + B) = topIntegral w A + topIntegral w B := by
  unfold topIntegral
  simp_rw [topRatio_add]
  exact integral_add (integrable_topRatio w A) (integrable_topRatio w B)

omit [BorelSpace M] in
theorem topIntegral_smul (w : KahlerBackground n M) (c : ℝ)
    (A : SmoothRealForm n M (2 * n)) :
    topIntegral w (c • A) = c * topIntegral w A := by
  unfold topIntegral
  simp_rw [topRatio_smul]
  exact integral_const_mul c _

theorem topIntegral_exteriorDerivative {k : ℕ} (w : KahlerBackground n M)
    (h : k + 1 = 2 * n) (A : SmoothRealForm n M k) :
    topIntegral w (castSmoothForm h A.exteriorDerivative) = 0 := by
  cases n with
  | zero => omega
  | succ m =>
    have hk : k = 2 * m + 1 := by omega
    subst k
    change (∫ x, topRatio w.form.val A.exteriorDerivative x ∂(kahlerVolume w)) = 0
    exact XiaoGlobalStokes.integral_exteriorDerivative_eq_zero w A

/-- Actual global Stokes and the genuine product rule give the original integral signs. -/
theorem integral_exteriorProduct_by_parts (w : KahlerBackground n M)
    (h : p + q + 1 = 2 * n) (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    topIntegral w (castSmoothForm (show (p + 1) + q = 2 * n by omega)
      (exteriorProduct A.exteriorDerivative B)) =
      (-1 : ℝ) ^ (p + 1) * topIntegral w
        (castSmoothForm (show p + (q + 1) = 2 * n by omega)
          (exteriorProduct A B.exteriorDerivative)) := by
  have hg := castSmoothForm_geometricallyEq h (exteriorProduct_derivative_geometricallyEq A B)
  simp only [map_add, map_smul, castSmoothForm_cast] at hg
  have hi := topIntegral_geometricallyEq w hg
  rw [topIntegral_exteriorDerivative, topIntegral_add, topIntegral_smul] at hi
  rw [pow_succ]
  linarith

/-- Actual star pairing against the existing unnormalized Kähler volume. -/
def hodgeIntegralPairing (w : KahlerBackground n M) (p : ℕ)
    (A B : SmoothRealForm n M p) : ℝ :=
  if hp : p ≤ 2 * n then
    topIntegral w (castSmoothForm (Nat.add_sub_of_le hp)
      (exteriorProduct A (degreeHodgeStarForm w.form.val w.isKahler.1 p hp B)))
  else 0

omit [BorelSpace M] in
theorem hodgeIntegralPairing_zero_right (w : KahlerBackground n M) (p : ℕ)
    (A : SmoothRealForm n M p) :
    hodgeIntegralPairing w p A 0 = 0 := by
  unfold hodgeIntegralPairing
  split_ifs <;> simp only [degreeHodgeStarForm_zero, exteriorProduct_zero_right,
    map_zero, topIntegral_zero]

omit [BorelSpace M] in
theorem hodgeIntegralPairing_geometricallyEq_right (w : KahlerBackground n M) (p : ℕ)
    (A : SmoothRealForm n M p) {B B' : SmoothRealForm n M p} (h : B.GeometricallyEq B') :
    hodgeIntegralPairing w p A B = hodgeIntegralPairing w p A B' := by
  unfold hodgeIntegralPairing
  split_ifs with hp
  · exact topIntegral_geometricallyEq w (castSmoothForm_geometricallyEq _
      (exteriorProduct_geometricallyEq (SmoothRealForm.GeometricallyEq.refl A)
        (degreeHodgeStarForm_geometricallyEq w.form.val w.isKahler.1 p hp h)))
  · rfl

/-- The integral adjoint on every admissible original degree, proved from actual Stokes. -/
theorem coderivativeSucc_integral_formal_adjoint (w : KahlerBackground n M)
    (p : ℕ) (hp : p + 1 ≤ 2 * n) (A : SmoothRealForm n M p)
    (B : SmoothRealForm n M (p + 1)) :
    hodgeIntegralPairing w (p + 1) A.exteriorDerivative B =
      hodgeIntegralPairing w p A (coderivativeSucc w.form.val w.isKahler.1 p hp B) := by
  have hp' : p ≤ 2 * n := by omega
  have hg := castSmoothForm_geometricallyEq (Nat.add_sub_of_le hp')
    (exteriorProduct_geometricallyEq (SmoothRealForm.GeometricallyEq.refl A)
      (star_coderivativeSucc_integral_sign w.form.val w.isKahler.1 p hp B))
  have hi := topIntegral_geometricallyEq w hg
  simp only [exteriorProduct_smul_right, map_smul, topIntegral_smul,
    exteriorProduct_cast_right, castSmoothForm_cast] at hi
  unfold hodgeIntegralPairing
  rw [dif_pos hp, dif_pos hp']
  calc
    topIntegral w (castSmoothForm (Nat.add_sub_of_le hp)
      (exteriorProduct A.exteriorDerivative
        (degreeHodgeStarForm w.form.val w.isKahler.1 (p + 1) hp B))) =
        (-1 : ℝ) ^ (p + 1) * topIntegral w
          (castSmoothForm (show p + (2 * n - (p + 1) + 1) = 2 * n by omega)
            (exteriorProduct A
              (degreeHodgeStarForm w.form.val w.isKahler.1 (p + 1) hp B).exteriorDerivative)) :=
      integral_exteriorProduct_by_parts w (by omega) A _
    _ = _ := hi.symm

/-- The genuine original integral formal adjoint, including zero dimension and excessive degrees. -/
theorem coderivative_integral_formal_adjoint (w : KahlerBackground n M)
    (p : ℕ) (A : SmoothRealForm n M p) (B : SmoothRealForm n M (p + 1)) :
    hodgeIntegralPairing w (p + 1) A.exteriorDerivative B =
      hodgeIntegralPairing w p A
        (castSmoothForm (show (p + 1) - 1 = p by omega)
          (coderivativeForm w.form.val w.isKahler.1 (p + 1) B)) := by
  by_cases hp : p + 1 ≤ 2 * n
  · rw [coderivativeForm_succ w.form.val w.isKahler.1 p hp]
    exact coderivativeSucc_integral_formal_adjoint w p hp A B
  · rw [(coderivativeForm_above_source w.form.val w.isKahler.1 (p + 1)
      (Nat.not_le.mp hp) B).2, map_zero, hodgeIntegralPairing_zero_right]
    simp only [hodgeIntegralPairing, dif_neg hp]

end Integral

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFormalAdjoint
