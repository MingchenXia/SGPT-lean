import SGPT.PSH.SourceTestCurvePrefixEnergy

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Literal prefixes increase, and their actual finite affine increments
are bounded directly by parameter antitonicity, with no readback at poles. -/
theorem SourceTestCurvePredata.integerPrefix_bounds (Γ : SourceTestCurvePredata θ)
    {d : ℝ} (hd : 0 < d) (t : ℝ) (j : ℤ) :
    sourceTestCurveIntegerPrefix Γ d t j ≤ sourceTestCurveIntegerPrefix Γ d t (j + 1) ∧
    sourceTestCurveIntegerPrefix Γ d t (j + 1) ≤
      fun x ↦ sourceTestCurveIntegerPrefix Γ d t j x + ((t * d : ℝ) : EReal) := by
  constructor
  · intro x
    rw [Γ.integerPrefix_succ d t j]
    exact le_max_left _ _
  · intro x
    apply iSup_le
    intro k
    have hk : k.1 - 1 ≤ j := by have hh : k.1 ≤ j + 1 := k.2; omega
    have hparam : (((k.1 - 1 : ℤ) : ℝ) * d) ≤ (k.1 : ℝ) * d := by
      push_cast
      nlinarith
    have ha := Γ.at_antitone x hparam
    have hcoef : t * (k.1 : ℝ) * d = t * ((k.1 - 1 : ℤ) : ℝ) * d + t * d := by
      push_cast
      ring
    have hsum : sourceTestCurveAt Γ ((k.1 : ℝ) * d) x +
        ((t * (k.1 : ℝ) * d : ℝ) : EReal) ≤
        (sourceTestCurveAt Γ (((k.1 - 1 : ℤ) : ℝ) * d) x +
          ((t * ((k.1 - 1 : ℤ) : ℝ) * d : ℝ) : EReal)) + ((t * d : ℝ) : EReal) := by
      rw [hcoef, EReal.coe_add, add_assoc]
      exact add_le_add ha le_rfl
    apply hsum.trans
    apply add_le_add _ le_rfl
    exact le_iSup (fun q : Iic j ↦ sourceTestCurveAt Γ ((q.1 : ℝ) * d) x +
      ((t * (q.1 : ℝ) * d : ℝ) : EReal)) ⟨k.1 - 1, hk⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Actual finite order bounds control the canonical signed difference,
including both infinite endpoints without realifying a potential there. -/
theorem sourceCanonicalDifference_bounds {a b : EReal} {c : ℝ}
    (hc : 0 ≤ c) (hlo : b ≤ a) (hhi : a ≤ b + (c : EReal)) :
    0 ≤ canonicalERealDiffToReal a b ∧ canonicalERealDiffToReal a b ≤ c := by
  cases a <;> cases b <;>
    simp_all [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      ← EReal.coe_add, ← EReal.coe_sub]
  linarith

/-- The original prefix gain is canonically nonnegative and at most td,
including its actual common poles. -/
theorem SourceTestCurvePredata.integerPrefix_canonicalDifference_bounds
    (Γ : SourceTestCurvePredata θ) {d t : ℝ} (hd : 0 < d) (ht : 0 < t)
    (j : ℤ) (x : M) :
    0 ≤ canonicalERealDiffToReal (sourceTestCurveIntegerPrefix Γ d t (j + 1) x)
      (sourceTestCurveIntegerPrefix Γ d t j x) ∧
    canonicalERealDiffToReal (sourceTestCurveIntegerPrefix Γ d t (j + 1) x)
      (sourceTestCurveIntegerPrefix Γ d t j x) ≤ t * d := by
  have h := Γ.integerPrefix_bounds hd t j
  exact sourceCanonicalDifference_bounds (mul_nonneg ht.le hd.le) (h.1 x) (h.2 x)

end SGPT.PSH.VariableComplexAtlas
