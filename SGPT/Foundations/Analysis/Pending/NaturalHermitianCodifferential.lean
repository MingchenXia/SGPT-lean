import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStarSquare
import SGPT.Foundations.Analysis.FirstPass.ExteriorDerivative

set_option autoImplicit false

/-! The genuine original smooth codifferential in even real dimension. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential

open FirstPass NaturalHermitianHodgeStarSquare NaturalOriginalGradedExteriorProduct
  NaturalHermitianSmoothFormMetric ConstantFormProducts ProductTestForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

/-- Exact scalar linearity of the genuine global star. -/
theorem degreeHodgeStarForm_smul (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) (c : ℝ) (α : SmoothRealForm n M q) :
    degreeHodgeStarForm w hw q hq (c • α) = c • degreeHodgeStarForm w hw q hq α := by
  apply smoothRealForm_ext
  intro e z
  change (degreeHodgeStarForm w hw q hq (c • α)).coeff e z =
    c • (degreeHodgeStarForm w hw q hq α).coeff e z
  rw [degreeHodgeStarForm_coeff, degreeHodgeStarForm_coeff]
  exact map_smul (degreeStar w e z q) c (α.coeff e z)

/-- Exact additive linearity of the genuine global star. -/
theorem degreeHodgeStarForm_add (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) (α β : SmoothRealForm n M q) :
    degreeHodgeStarForm w hw q hq (α + β) =
      degreeHodgeStarForm w hw q hq α + degreeHodgeStarForm w hw q hq β := by
  apply smoothRealForm_ext
  intro e z
  change (degreeHodgeStarForm w hw q hq (α + β)).coeff e z =
    (degreeHodgeStarForm w hw q hq α).coeff e z +
      (degreeHodgeStarForm w hw q hq β).coeff e z
  rw [degreeHodgeStarForm_coeff, degreeHodgeStarForm_coeff, degreeHodgeStarForm_coeff]
  exact map_add (degreeStar w e z q) (α.coeff e z) (β.coeff e z)

/-- The genuine global star sends the original zero smooth form to zero. -/
theorem degreeHodgeStarForm_zero (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) : degreeHodgeStarForm w hw q hq (0 : SmoothRealForm n M q) = 0 := by
  apply smoothRealForm_ext
  intro e z
  rw [degreeHodgeStarForm_coeff]
  exact map_zero (degreeStar w e z q)

/-- The original star respects only the required geometric coefficient equality. -/
theorem degreeHodgeStarForm_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q ≤ 2 * n) {α β : SmoothRealForm n M q}
    (h : α.GeometricallyEq β) :
    (degreeHodgeStarForm w hw q hq α).GeometricallyEq (degreeHodgeStarForm w hw q hq β) := by
  intro e z hz
  rw [degreeHodgeStarForm_coeff, degreeHodgeStarForm_coeff, h e hz]

/-- Original exterior differentiation is genuinely scalar linear, including its zero value. -/
theorem exteriorDerivative_const_smul {q : ℕ} (c : ℝ) (α : SmoothRealForm n M q) :
    (c • α).exteriorDerivative = c • α.exteriorDerivative := by
  apply smoothRealForm_ext
  intro e z
  exact extDeriv_fun_smul c (α.coeff e)

theorem exteriorDerivative_zero {q : ℕ} :
    (0 : SmoothRealForm n M q).exteriorDerivative = 0 := by
  apply smoothRealForm_ext
  intro e z
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
    (fderiv ℝ (fun _ : ComplexModel n => (0 : FormCoefficients n q)) z) = 0
  rw [fderiv_const_apply, map_zero]

theorem exteriorDerivative_add_geometricallyEq {q : ℕ} (α β : SmoothRealForm n M q) :
    (α + β).exteriorDerivative.GeometricallyEq (α.exteriorDerivative + β.exteriorDerivative) := by
  intro e z hz
  exact extDeriv_fun_add
    (((α.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))
    (((β.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))

theorem castSmoothForm_geometricallyEq {a b : ℕ} (h : a = b)
    {α β : SmoothRealForm n M a} (hαβ : α.GeometricallyEq β) :
    (castSmoothForm h α).GeometricallyEq (castSmoothForm h β) := by
  subst h
  exact hαβ

theorem smul_geometricallyEq {q : ℕ} (c : ℝ)
    {α β : SmoothRealForm n M q} (h : α.GeometricallyEq β) :
    (c • α).GeometricallyEq (c • β) := by
  intro e z hz
  exact congrArg (c • ·) (h e hz)

/-- The positive-degree genuine codifferential, with its actual smooth derivative. -/
def coderivativeSucc (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (α : SmoothRealForm n M (q + 1)) : SmoothRealForm n M q :=
  (-1 : ℝ) • castSmoothForm (show 2 * n - (2 * n - (q + 1) + 1) = q by omega)
    (degreeHodgeStarForm w hw (2 * n - (q + 1) + 1) (by omega)
      (degreeHodgeStarForm w hw (q + 1) hq α).exteriorDerivative)

/-- The actual original codifferential in every natural degree, with genuine zero branches. -/
def coderivativeForm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (α : SmoothRealForm n M q) : SmoothRealForm n M (q - 1) :=
  if hzero : q = 0 then 0 else if hq : q ≤ 2 * n then
    coderivativeSucc w hw (q - 1) (by omega)
      (castSmoothForm (show q = q - 1 + 1 by omega) α)
  else 0

theorem coderivativeForm_succ (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (α : SmoothRealForm n M (q + 1)) :
    castSmoothForm (Nat.add_sub_cancel q 1) (coderivativeForm w hw (q + 1) α) =
      coderivativeSucc w hw q hq α := by
  simp only [coderivativeForm, dif_neg (Nat.succ_ne_zero q), dif_pos hq]
  rfl

theorem coderivativeForm_above_source (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : 2 * n < q) (α : SmoothRealForm n M q) :
    α = 0 ∧ coderivativeForm w hw q α = 0 := by
  refine ⟨?_, ?_⟩
  · apply smoothRealForm_ext
    intro e z
    exact (degreeStar_above_source w e z q hq (α.coeff e z)).1
  · simp only [coderivativeForm, dif_neg (show q ≠ 0 by omega), dif_neg (Nat.not_le.mpr hq)]

theorem castSmoothForm_cast {a b c : ℕ} (h : a = b) (h' : b = c)
    (α : SmoothRealForm n M a) :
    castSmoothForm h' (castSmoothForm h α) = castSmoothForm (h.trans h') α := by
  subst h h'
  rfl

theorem exteriorDerivative_cast {a b : ℕ} (h : a = b) (α : SmoothRealForm n M a) :
    (castSmoothForm h α).exteriorDerivative =
      castSmoothForm (congrArg (fun q => q + 1) h) α.exteriorDerivative := by
  subst h
  rfl

theorem degreeHodgeStarForm_cast (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    {a b : ℕ} (h : a = b) (ha : a ≤ 2 * n) (hb : b ≤ 2 * n)
    (α : SmoothRealForm n M a) :
    degreeHodgeStarForm w hw b hb (castSmoothForm h α) =
      castSmoothForm (congrArg (fun q => 2 * n - q) h) (degreeHodgeStarForm w hw a ha α) := by
  subst h
  rfl

theorem coderivativeSucc_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) {α β : SmoothRealForm n M (q + 1)}
    (h : α.GeometricallyEq β) :
    (coderivativeSucc w hw q hq α).GeometricallyEq (coderivativeSucc w hw q hq β) := by
  exact smul_geometricallyEq (-1) (castSmoothForm_geometricallyEq _
    (degreeHodgeStarForm_geometricallyEq w hw _ _
      (degreeHodgeStarForm_geometricallyEq w hw _ _ h).exteriorDerivative))

theorem coderivativeSucc_smul (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (c : ℝ) (α : SmoothRealForm n M (q + 1)) :
    coderivativeSucc w hw q hq (c • α) = c • coderivativeSucc w hw q hq α := by
  simp only [coderivativeSucc, degreeHodgeStarForm_smul, exteriorDerivative_const_smul,
    map_smul, smul_comm (-1 : ℝ) c]

theorem coderivativeSucc_zero (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) :
    coderivativeSucc w hw q hq (0 : SmoothRealForm n M (q + 1)) = 0 := by
  simp only [coderivativeSucc, degreeHodgeStarForm_zero, exteriorDerivative_zero, map_zero, smul_zero]

theorem coderivativeSucc_add_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (α β : SmoothRealForm n M (q + 1)) :
    (coderivativeSucc w hw q hq (α + β)).GeometricallyEq
      (coderivativeSucc w hw q hq α + coderivativeSucc w hw q hq β) := by
  unfold coderivativeSucc
  rw [degreeHodgeStarForm_add]
  have h := degreeHodgeStarForm_geometricallyEq w hw (2 * n - (q + 1) + 1) (by omega)
    (exteriorDerivative_add_geometricallyEq
      (degreeHodgeStarForm w hw (q + 1) hq α) (degreeHodgeStarForm w hw (q + 1) hq β))
  rw [degreeHodgeStarForm_add] at h
  have hc := castSmoothForm_geometricallyEq
    (show 2 * n - (2 * n - (q + 1) + 1) = q by omega) h
  rw [map_add] at hc
  have hs := smul_geometricallyEq (-1) hc
  rw [smul_add] at hs
  exact hs

theorem coderivativeForm_zero (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (q : ℕ) :
    coderivativeForm w hw q (0 : SmoothRealForm n M q) = 0 := by
  unfold coderivativeForm
  split_ifs <;> simp only [map_zero, coderivativeSucc_zero]

theorem coderivativeForm_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) {α β : SmoothRealForm n M q} (h : α.GeometricallyEq β) :
    (coderivativeForm w hw q α).GeometricallyEq (coderivativeForm w hw q β) := by
  unfold coderivativeForm
  split_ifs
  · exact SmoothRealForm.GeometricallyEq.refl _
  · exact coderivativeSucc_geometricallyEq w hw _ _ (castSmoothForm_geometricallyEq _ h)
  · exact SmoothRealForm.GeometricallyEq.refl _

theorem coderivativeForm_smul_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (c : ℝ) (α : SmoothRealForm n M q) :
    (coderivativeForm w hw q (c • α)).GeometricallyEq (c • coderivativeForm w hw q α) := by
  unfold coderivativeForm
  split_ifs
  · simp only [smul_zero]; exact SmoothRealForm.GeometricallyEq.refl _
  · rw [map_smul, coderivativeSucc_smul]; exact SmoothRealForm.GeometricallyEq.refl _
  · simp only [smul_zero]; exact SmoothRealForm.GeometricallyEq.refl _

theorem coderivativeForm_add_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (α β : SmoothRealForm n M q) :
    (coderivativeForm w hw q (α + β)).GeometricallyEq
      (coderivativeForm w hw q α + coderivativeForm w hw q β) := by
  unfold coderivativeForm
  split_ifs
  · simp only [zero_add]; exact SmoothRealForm.GeometricallyEq.refl _
  · rw [map_add]; exact coderivativeSucc_add_geometricallyEq w hw _ _ _ _
  · simp only [zero_add]; exact SmoothRealForm.GeometricallyEq.refl _

/-- The genuine internal squared star identifies the differentiated middle of the codifferential. -/
theorem star_coderivativeSucc_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 1 ≤ 2 * n) (α : SmoothRealForm n M (q + 1)) :
    (degreeHodgeStarForm w hw q (by omega) (coderivativeSucc w hw q hq α)).GeometricallyEq
      (((-1 : ℝ) * (-1 : ℝ) ^ ((2 * n - (q + 1) + 1) * q)) •
        castSmoothForm (show 2 * n - (q + 1) + 1 = 2 * n - q by omega)
          (degreeHodgeStarForm w hw (q + 1) hq α).exteriorDerivative) := by
  let a := 2 * n - (q + 1) + 1
  have ha : a ≤ 2 * n := by dsimp [a]; omega
  have hc : 2 * n - a = q := by dsimp [a]; omega
  have hb : a = 2 * n - q := by dsimp [a]; omega
  let β := (degreeHodgeStarForm w hw (q + 1) hq α).exteriorDerivative
  have hsq := degreeHodgeStarForm_square_geometricallyEq w hw a ha β
  have hcast := castSmoothForm_geometricallyEq hb hsq
  rw [castSmoothForm_cast, map_smul] at hcast
  have hs := smul_geometricallyEq (-1) hcast
  rw [smul_smul] at hs
  unfold coderivativeSucc
  rw [degreeHodgeStarForm_smul, degreeHodgeStarForm_cast w hw hc (Nat.sub_le _ _) (by omega)]
  simpa only [a, hc] using hs

/-- Genuine original codifferential square, proved from the actual star square and actual d-square. -/
theorem coderivativeSucc_square_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (hq : q + 2 ≤ 2 * n) (α : SmoothRealForm n M (q + 2)) :
    (coderivativeSucc w hw q (by omega)
      (coderivativeSucc w hw (q + 1) (by omega) α)).GeometricallyEq 0 := by
  have hstar := star_coderivativeSucc_geometricallyEq w hw (q + 1) (by omega) α
  have hd := hstar.exteriorDerivative
  rw [exteriorDerivative_const_smul, exteriorDerivative_cast] at hd
  have hz := castSmoothForm_geometricallyEq
    (congrArg (fun k => k + 1)
      (show 2 * n - (q + 1 + 1) + 1 = 2 * n - (q + 1) by omega))
    (degreeHodgeStarForm w hw (q + 1 + 1) (by omega) α).exteriorDerivative_sq_geometricallyEq_zero
  rw [show SmoothRealForm.zero =
    (0 : SmoothRealForm n M (2 * n - (q + 1 + 1) + 1 + 1)) from rfl] at hz
  rw [map_zero] at hz
  have hzero := smul_geometricallyEq
    ((-1 : ℝ) * (-1 : ℝ) ^ ((2 * n - (q + 1 + 1) + 1) * (q + 1))) hz
  rw [smul_zero] at hzero
  have hout := degreeHodgeStarForm_geometricallyEq w hw (2 * n - (q + 1) + 1) (by omega)
    (hd.trans hzero)
  rw [degreeHodgeStarForm_zero] at hout
  have hc := castSmoothForm_geometricallyEq
    (show 2 * n - (2 * n - (q + 1) + 1) = q by omega) hout
  rw [map_zero] at hc
  have hs := smul_geometricallyEq (-1) hc
  rw [smul_zero] at hs
  exact hs

/-- The actual original codifferential squares to zero in every natural degree. -/
theorem coderivativeForm_square_geometricallyEq (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (q : ℕ) (α : SmoothRealForm n M q) :
    (coderivativeForm w hw (q - 1) (coderivativeForm w hw q α)).GeometricallyEq 0 := by
  rcases q with _ | q
  · simp only [coderivativeForm]
    exact SmoothRealForm.GeometricallyEq.refl _
  rcases q with _ | q
  · change (coderivativeForm w hw 0 (coderivativeForm w hw 1 α)).GeometricallyEq 0
    simp only [coderivativeForm, dif_pos rfl]
    exact SmoothRealForm.GeometricallyEq.refl _
  by_cases hq : q + 2 ≤ 2 * n
  · change (coderivativeForm w hw (q + 1) (coderivativeForm w hw (q + 2) α)).GeometricallyEq 0
    have hinner := coderivativeForm_succ w hw (q + 1) hq α
    change coderivativeForm w hw (q + 2) α = coderivativeSucc w hw (q + 1) hq α at hinner
    rw [hinner]
    have houter := coderivativeForm_succ w hw q (by omega) (coderivativeSucc w hw (q + 1) hq α)
    change coderivativeForm w hw (q + 1) (coderivativeSucc w hw (q + 1) hq α) =
      coderivativeSucc w hw q (by omega) (coderivativeSucc w hw (q + 1) hq α) at houter
    rw [houter]
    exact coderivativeSucc_square_geometricallyEq w hw q hq α
  · have hzero : coderivativeForm w hw (q + 2) α = 0 := by
      simp only [coderivativeForm, dif_neg (show q + 2 ≠ 0 by omega), dif_neg hq]
    rw [hzero, coderivativeForm_zero]
    exact SmoothRealForm.GeometricallyEq.refl _

end SGPT.Foundations.Analysis.Pending.NaturalHermitianCodifferential
