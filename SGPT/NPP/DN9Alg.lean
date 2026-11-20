import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar inequalities for the assembly of the local joint estimate

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, end of Step 5 and Step 6): the
real-number bookkeeping that turns the Levi bound of the smoothing of the plurisubharmonic
potential `u + q` (in terms of its slopes), the bound of the smooth part `S_q - q`, and the slope
bounds of the clauses into `eq:chern-initial-joint-bound` (`clause3_alg`) and
`eq:chern-improved-joint-bound` (`clause4_alg`).
-/

set_option autoImplicit false

namespace SGPT.NPP.DN9

/-- `√m · V ≤ √α'` when `m V² ≤ α'`. -/
theorem sqrt_mul_le_sqrt {m V α' : ℝ} (hm : 0 ≤ m) (hV : 0 ≤ V) (hα : m * V ^ 2 ≤ α') :
    Real.sqrt m * V ≤ Real.sqrt α' := by
  have h1 : Real.sqrt (m * V ^ 2) = Real.sqrt m * V := by
    rw [Real.sqrt_mul hm, Real.sqrt_sq hV]
  rw [← h1]
  exact Real.sqrt_le_sqrt hα

/-- The conversion of `D₁ a V² + D₂ V H` to the Kähler norm `α' ≥ m V²`. -/
theorem convert_norms {m V Hη α' a D₁ D₂ C : ℝ} (hm : 0 < m) (hV : 0 ≤ V) (hη : 0 ≤ Hη)
    (ha : 0 ≤ a) (hα : m * V ^ 2 ≤ α') (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hC1 : D₁ / m ≤ C)
    (hC2 : D₂ / Real.sqrt m ≤ C) :
    D₁ * a * V ^ 2 ≤ C * a * α' ∧ D₂ * V * Hη ≤ C * Real.sqrt α' * Hη := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hC : 0 ≤ C := (div_nonneg hD₁ hm.le).trans hC1
  constructor
  · have e : D₁ * a * V ^ 2 = D₁ / m * a * (m * V ^ 2) := by field_simp
    rw [e]
    have h1 : D₁ / m * a * (m * V ^ 2) ≤ D₁ / m * a * α' :=
      mul_le_mul_of_nonneg_left hα (mul_nonneg (div_nonneg hD₁ hm.le) ha)
    have h2 : D₁ / m * a * α' ≤ C * a * α' := by
      have hα0 : 0 ≤ α' := (mul_nonneg hm.le (sq_nonneg V)).trans hα
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 ha) hα0
    linarith
  · have e : D₂ * V * Hη = D₂ / Real.sqrt m * (Real.sqrt m * V) * Hη := by field_simp
    rw [e]
    have h1 := sqrt_mul_le_sqrt hm.le hV hα
    have h2 : D₂ / Real.sqrt m * (Real.sqrt m * V) ≤ C * Real.sqrt α' :=
      mul_le_mul hC2 h1 (mul_nonneg hsm.le hV) hC
    exact mul_le_mul_of_nonneg_right h2 hη

/-- **The initial joint bound, scalar form.** -/
theorem clause3_alg {A₁ A₂ Cq Cu K₀ m C a V Hη X1 X2 LH L1 L2 α' : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hCq : 0 ≤ Cq) (hCu : 0 ≤ Cu) (hK₀ : Cq ≤ K₀) (hm : 0 < m)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hV : 0 ≤ V) (hη : 0 ≤ Hη)
    (hL1 : -(A₁ * a ^ 2 * V ^ 2 * (2 * a * X2)) - A₂ * (V ^ 2 + V * Hη) * (a * X1) ≤ L1)
    (hL2 : L2 ≤ Cq * (a ^ 2 * V ^ 2 + a * V * Hη + Hη ^ 2))
    (h1 : 2 * a * X2 ≤ Cu + 4 * Cq * a ^ 2) (h2 : a * X1 ≤ LH + Cq * a ^ 2)
    (h3 : a * X1 ≤ Cu + Cq) (hLH : 0 ≤ LH) (hα : m * V ^ 2 ≤ α')
    (hC1 : (A₁ * (Cu + 4 * Cq) + A₂ * Cq + Cq) / m ≤ C)
    (hC2 : (A₂ * (Cu + Cq) + Cq) / Real.sqrt m ≤ C) :
    -((A₂ / m * LH + C * a) * α') - C * Real.sqrt α' * Hη - C * Hη ^ 2 ≤
      L1 - L2 + K₀ * Hη ^ 2 := by
  have ha2 : a ^ 2 ≤ a := by rw [sq]; exact mul_le_of_le_one_left ha ha1
  have ha4 : a ^ 2 * a ^ 2 ≤ a := (mul_le_of_le_one_left (sq_nonneg a) (ha2.trans ha1)).trans ha2
  have hV2 : 0 ≤ V ^ 2 := sq_nonneg V
  have hVη : 0 ≤ V * Hη := mul_nonneg hV hη
  have hD₁ : 0 ≤ A₁ * (Cu + 4 * Cq) + A₂ * Cq + Cq := by positivity
  have hD₂ : 0 ≤ A₂ * (Cu + Cq) + Cq := by positivity
  have hC : 0 ≤ C := (div_nonneg hD₁ hm.le).trans hC1
  have hT1 : A₁ * a ^ 2 * V ^ 2 * (2 * a * X2) ≤ A₁ * (Cu + 4 * Cq) * a * V ^ 2 := by
    have e1 : A₁ * a ^ 2 * V ^ 2 * (2 * a * X2) ≤ A₁ * a ^ 2 * V ^ 2 * (Cu + 4 * Cq * a ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have f1 : Cu * a ^ 2 ≤ Cu * a := mul_le_mul_of_nonneg_left ha2 hCu
    have f2 : Cq * (a ^ 2 * a ^ 2) ≤ Cq * a := mul_le_mul_of_nonneg_left ha4 hCq
    have e2 : a ^ 2 * (Cu + 4 * Cq * a ^ 2) ≤ a * (Cu + 4 * Cq) := by linarith
    have e3 : A₁ * V ^ 2 * (a ^ 2 * (Cu + 4 * Cq * a ^ 2)) ≤ A₁ * V ^ 2 * (a * (Cu + 4 * Cq)) :=
      mul_le_mul_of_nonneg_left e2 (mul_nonneg hA₁ hV2)
    linarith
  have hT2 : A₂ * (V ^ 2 + V * Hη) * (a * X1) ≤
      A₂ * LH * V ^ 2 + A₂ * Cq * a * V ^ 2 + A₂ * (Cu + Cq) * (V * Hη) := by
    have e1 : A₂ * V ^ 2 * (a * X1) ≤ A₂ * V ^ 2 * (LH + Cq * a ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hA₂ hV2)
    have e2 : A₂ * (V * Hη) * (a * X1) ≤ A₂ * (V * Hη) * (Cu + Cq) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hA₂ hVη)
    have e3 : A₂ * V ^ 2 * (Cq * a ^ 2) ≤ A₂ * V ^ 2 * (Cq * a) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha2 hCq) (mul_nonneg hA₂ hV2)
    linarith
  have hL2' : L2 ≤ Cq * a * V ^ 2 + Cq * (V * Hη) + Cq * Hη ^ 2 := by
    have e1 : Cq * (a ^ 2 * V ^ 2) ≤ Cq * (a * V ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 hV2) hCq
    have e2 : Cq * (a * (V * Hη)) ≤ Cq * (V * Hη) :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hVη ha1) hCq
    linarith
  have hη2 : 0 ≤ (K₀ - Cq) * Hη ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  obtain ⟨hc1, hc2⟩ := convert_norms hm hV hη ha hα hD₁ hD₂ hC1 hC2
  have hc3 : A₂ * LH * V ^ 2 ≤ A₂ / m * LH * α' := by
    have e : A₂ * LH * V ^ 2 = A₂ / m * LH * (m * V ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hα (mul_nonneg (div_nonneg hA₂ hm.le) hLH)
  have hCη : 0 ≤ C * Hη ^ 2 := mul_nonneg hC (sq_nonneg _)
  linarith

/-- **The improved joint bound, scalar form** (`L ≥ 0`, `|w| = a`). -/
theorem clause4_alg {A₁ A₂ Cq C' K₀ m C a V Hη X1 X2 LH L1 L2 α' L : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hCq : 0 ≤ Cq) (hC' : 0 ≤ C') (hK₀ : Cq ≤ K₀) (hm : 0 < m)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hV : 0 ≤ V) (hη : 0 ≤ Hη) (hL : 0 ≤ L)
    (hL1 : -(A₁ * a ^ 2 * V ^ 2 * (2 * a * X2)) - A₂ * (V ^ 2 + V * Hη) * (a * X1) ≤ L1)
    (hL2 : L2 ≤ Cq * (a ^ 2 * V ^ 2 + a * V * Hη + Hη ^ 2))
    (h1 : 2 * a * X2 ≤ C' * (1 + L) * a + 4 * Cq * a ^ 2) (h2 : a * X1 ≤ LH + Cq * a ^ 2)
    (h3 : a * X1 ≤ C' * (1 + L) * a + Cq * a ^ 2) (hLH : 0 ≤ LH) (hα : m * V ^ 2 ≤ α')
    (hC1 : (A₁ * (C' + 4 * Cq) + A₂ * Cq + Cq) / m ≤ C)
    (hC2 : (A₂ * (C' + Cq) + Cq) / Real.sqrt m ≤ C) :
    -((A₂ / m * LH + C * (1 + L) * a ^ 2) * α') - C * (1 + L) * a * Real.sqrt α' * Hη -
      C * (1 + L) * a * Hη ^ 2 ≤ L1 - L2 + K₀ * Hη ^ 2 := by
  have ha2 : a ^ 2 ≤ a := by rw [sq]; exact mul_le_of_le_one_left ha ha1
  have ha3 : a ^ 2 * a ≤ a ^ 2 := mul_le_of_le_one_right (sq_nonneg a) ha1
  have ha4 : a ^ 2 * a ^ 2 ≤ a ^ 2 := mul_le_of_le_one_left (sq_nonneg a) (ha2.trans ha1)
  have hV2 : 0 ≤ V ^ 2 := sq_nonneg V
  have hVη : 0 ≤ V * Hη := mul_nonneg hV hη
  have h1L : 0 ≤ 1 + L := by linarith
  have hLa2 : 0 ≤ L * a ^ 2 := mul_nonneg hL (sq_nonneg a)
  have hLa : 0 ≤ L * a := mul_nonneg hL ha
  have hD₁ : 0 ≤ A₁ * (C' + 4 * Cq) + A₂ * Cq + Cq := by positivity
  have hD₂ : 0 ≤ A₂ * (C' + Cq) + Cq := by positivity
  have hC : 0 ≤ C := (div_nonneg hD₁ hm.le).trans hC1
  -- `b = (1 + L) a`; `a² ≤ b a`, `a ≤ b`
  have hba : a ^ 2 ≤ (1 + L) * a ^ 2 := by linarith
  have hT1 : A₁ * a ^ 2 * V ^ 2 * (2 * a * X2) ≤ A₁ * (C' + 4 * Cq) * ((1 + L) * a ^ 2) * V ^ 2 := by
    have e1 : A₁ * a ^ 2 * V ^ 2 * (2 * a * X2) ≤
        A₁ * a ^ 2 * V ^ 2 * (C' * (1 + L) * a + 4 * Cq * a ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have f1 : C' * (1 + L) * (a ^ 2 * a) ≤ C' * (1 + L) * a ^ 2 :=
      mul_le_mul_of_nonneg_left ha3 (mul_nonneg hC' h1L)
    have f2 : Cq * (a ^ 2 * a ^ 2) ≤ Cq * ((1 + L) * a ^ 2) :=
      mul_le_mul_of_nonneg_left (ha4.trans hba) hCq
    have e2 : a ^ 2 * (C' * (1 + L) * a + 4 * Cq * a ^ 2) ≤ (C' + 4 * Cq) * ((1 + L) * a ^ 2) := by
      linarith
    have e3 : A₁ * V ^ 2 * (a ^ 2 * (C' * (1 + L) * a + 4 * Cq * a ^ 2)) ≤
        A₁ * V ^ 2 * ((C' + 4 * Cq) * ((1 + L) * a ^ 2)) :=
      mul_le_mul_of_nonneg_left e2 (mul_nonneg hA₁ hV2)
    linarith
  have hT2 : A₂ * (V ^ 2 + V * Hη) * (a * X1) ≤
      A₂ * LH * V ^ 2 + A₂ * Cq * ((1 + L) * a ^ 2) * V ^ 2 +
        A₂ * (C' + Cq) * ((1 + L) * a) * (V * Hη) := by
    have e1 : A₂ * V ^ 2 * (a * X1) ≤ A₂ * V ^ 2 * (LH + Cq * a ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hA₂ hV2)
    have e2 : A₂ * (V * Hη) * (a * X1) ≤ A₂ * (V * Hη) * (C' * (1 + L) * a + Cq * a ^ 2) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hA₂ hVη)
    have f1 : C' * (1 + L) * a + Cq * a ^ 2 ≤ (C' + Cq) * ((1 + L) * a) := by
      have : Cq * a ^ 2 ≤ Cq * ((1 + L) * a) := mul_le_mul_of_nonneg_left (by linarith) hCq
      linarith
    have e3 : A₂ * (V * Hη) * (C' * (1 + L) * a + Cq * a ^ 2) ≤
        A₂ * (V * Hη) * ((C' + Cq) * ((1 + L) * a)) :=
      mul_le_mul_of_nonneg_left f1 (mul_nonneg hA₂ hVη)
    have e4 : A₂ * V ^ 2 * (Cq * a ^ 2) ≤ A₂ * V ^ 2 * (Cq * ((1 + L) * a ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hba hCq) (mul_nonneg hA₂ hV2)
    linarith
  have hL2' : L2 ≤ Cq * ((1 + L) * a ^ 2) * V ^ 2 + Cq * ((1 + L) * a) * (V * Hη) +
      Cq * Hη ^ 2 := by
    have e1 : Cq * (a ^ 2 * V ^ 2) ≤ Cq * (((1 + L) * a ^ 2) * V ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hba hV2) hCq
    have e2 : Cq * (a * (V * Hη)) ≤ Cq * (((1 + L) * a) * (V * Hη)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hVη) hCq
    linarith
  have hη2 : 0 ≤ (K₀ - Cq) * Hη ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hb2 : 0 ≤ (1 + L) * a ^ 2 := mul_nonneg h1L (sq_nonneg a)
  obtain ⟨hc1, -⟩ := convert_norms hm hV hη hb2 hα hD₁ hD₂ hC1 hC2
  obtain ⟨-, hc2⟩ := convert_norms hm hV hη ha hα hD₁ hD₂ hC1 hC2
  have hc3 : A₂ * LH * V ^ 2 ≤ A₂ / m * LH * α' := by
    have e : A₂ * LH * V ^ 2 = A₂ / m * LH * (m * V ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hα (mul_nonneg (div_nonneg hA₂ hm.le) hLH)
  have hc4 : (1 + L) * a * ((A₂ * (C' + Cq) + Cq) * V * Hη) ≤
      (1 + L) * a * (C * Real.sqrt α' * Hη) :=
    mul_le_mul_of_nonneg_left hc2 (mul_nonneg h1L ha)
  have hCη : 0 ≤ C * (1 + L) * a * Hη ^ 2 := by positivity
  linarith

end SGPT.NPP.DN9
