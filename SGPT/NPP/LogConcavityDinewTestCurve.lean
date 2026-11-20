import SGPT.NPP.LogConcavityDinew
import SGPT.PSH.SourceTestCurveMassContinuity

/-!
# Log-concavity of test-curve masses

Source `prop:testcurvmasslogconc`: for a test curve `Γ ∈ TC(X, θ)_{>0}` the map
`τ ↦ log ∫_X θ_{Γ_τ}ⁿ` is concave on `(-∞, Γ_max)` (`concaveOn_log_sourceTestCurveRealMassAt`;
dimension `0`: `concaveOn_log_sourceTestCurveRealMassAt_of_dim_zero`). Its continuity on
`(-∞, Γ_max)` and at `-∞` is already in `SGPT.PSH.SourceTestCurveMassContinuity`
(`sourceTestCurveLogMassAt_continuousAt`, `sourceTestCurveLogMassAt_tendsto_atBot`).

Proof (the source's): `Γ_{ta + (1-t)b} ≥ tΓ_a + (1-t)Γ_b` by concavity of the curve, so by
monotonicity of non-pluripolar masses (`thm:mono`)
`m(ta + (1-t)b) ≥ ∫ θ_{tΓ_a + (1-t)Γ_b}ⁿ ≥ m(a)^t m(b)^{1-t}`, the last step by the first assertion
of `thm:logconc` (`sourceConvexCombMass_logConcave`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.NPP.LogConcavityDinew

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.NPP.LogConcavity SGPT.PSH.VariableComplexAtlas

section General

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [BorelSpace M] in
theorem sourcePotentialNonPluripolarMeasure_congr {u v : M → EReal} (h : u = v)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    sourcePotentialNonPluripolarMeasure θ u hu = sourcePotentialNonPluripolarMeasure θ v hv := by
  subst h
  rfl

omit [BorelSpace M] in
theorem sourceConvexCombMass_zero {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) :
    sourceConvexCombMass θ h₀ h₁ 0 = (sourcePotentialNonPluripolarMeasure θ φ₀ h₀ univ).toReal := by
  rw [sourceConvexCombMass_eq θ h₀ h₁ le_rfl zero_le_one]
  exact congrArg (fun μ : Measure M => (μ univ).toReal)
    (sourcePotentialNonPluripolarMeasure_congr (convexComb_zero φ₁ φ₀) _ h₀)

omit [BorelSpace M] in
theorem sourceConvexCombMass_one {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
    (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) :
    sourceConvexCombMass θ h₀ h₁ 1 = (sourcePotentialNonPluripolarMeasure θ φ₁ h₁ univ).toReal := by
  rw [sourceConvexCombMass_eq θ h₀ h₁ zero_le_one le_rfl]
  exact congrArg (fun μ : Measure M => (μ univ).toReal)
    (sourcePotentialNonPluripolarMeasure_congr (convexComb_one φ₁ φ₀) _ h₁)

/-- The chord inequality `m(b)^{1-t} m(a)^t ≤ m(ta + (1-t)b)` for test-curve masses, from the
log-concavity of masses along convex combinations. -/
theorem sourceTestCurveRealMassAt_logConcave_of (ω : KahlerBackground n M) (Γ : SourceTestCurve θ)
    (hlc : ∀ {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
      (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) {s : ℝ}, s ∈ Icc (0 : ℝ) 1 →
      sourceConvexCombMass θ h₀ h₁ 0 ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ 1 ^ s ≤
        sourceConvexCombMass θ h₀ h₁ s)
    {a b t : ℝ} (ha : a < Γ.max) (hb : b < Γ.max) (ht0 : 0 < t) (ht1 : t < 1) :
    sourceTestCurveRealMassAt ω Γ b ^ (1 - t) * sourceTestCurveRealMassAt ω Γ a ^ t ≤
      sourceTestCurveRealMassAt ω Γ (t * a + (1 - t) * b) := by
  have hs : t * a + (1 - t) * b < Γ.max := by
    nlinarith [mul_pos ht0 (sub_pos.mpr ha), mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hb)]
  have h₁ := Γ.thetaPSH ⟨a, ha⟩
  have h₀ := Γ.thetaPSH ⟨b, hb⟩
  have hconv := hlc h₀ h₁ (s := t) ⟨ht0.le, ht1.le⟩
  rw [sourceConvexCombMass_zero, sourceConvexCombMass_one,
    sourceConvexCombMass_eq θ h₀ h₁ ht0.le ht1.le] at hconv
  have hmono := sourcePotentialNonPluripolarMass_mono ω (isThetaPSH_convexComb h₁ h₀ ht0.le ht1.le)
    (Γ.thetaPSH ⟨_, hs⟩)
    (MoreSingularOn.of_le fun x _ ↦
      Γ.toSourceTestCurvePredata.convexComb_le ⟨a, ha⟩ ⟨b, hb⟩ ht0 ht1 x)
  have hreal := ENNReal.toReal_mono (Γ.mass_lt_top ω ⟨_, hs⟩).ne hmono
  rw [sourceTestCurveRealMassAt_of_lt ω Γ ha, sourceTestCurveRealMassAt_of_lt ω Γ hb,
    sourceTestCurveRealMassAt_of_lt ω Γ hs]
  exact hconv.trans hreal

/-- Concavity of `τ ↦ log ∫ θ_{Γ_τ}ⁿ` on `(-∞, Γ_max)`, from the log-concavity of masses along
convex combinations. -/
theorem concaveOn_log_sourceTestCurveRealMassAt_of (ω : KahlerBackground n M)
    (Γ : SourceTestCurve θ)
    (hlc : ∀ {φ₀ φ₁ : M → EReal} (h₀ : (ofFixedModel n M).IsThetaPSH θ φ₀)
      (h₁ : (ofFixedModel n M).IsThetaPSH θ φ₁) {s : ℝ}, s ∈ Icc (0 : ℝ) 1 →
      sourceConvexCombMass θ h₀ h₁ 0 ^ (1 - s) * sourceConvexCombMass θ h₀ h₁ 1 ^ s ≤
        sourceConvexCombMass θ h₀ h₁ s) :
    ConcaveOn ℝ (Iio Γ.max) (fun τ => Real.log (sourceTestCurveRealMassAt ω Γ τ)) := by
  refine ⟨convex_Iio _, fun x hx y hy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hpos : ∀ τ (hτ : τ < Γ.max), 0 < sourceTestCurveRealMassAt ω Γ τ := fun τ hτ => by
    rw [sourceTestCurveRealMassAt_of_lt ω Γ hτ]
    exact ENNReal.toReal_pos (Γ.mass_positive ω ⟨τ, hτ⟩).ne' (Γ.mass_lt_top ω ⟨τ, hτ⟩).ne
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : b = 1 - a := by linarith
  have ha1 : a < 1 := by linarith
  have h := sourceTestCurveRealMassAt_logConcave_of ω Γ hlc hx hy ha' ha1
  have hx' := hpos x hx
  have hy' := hpos y hy
  calc a * Real.log (sourceTestCurveRealMassAt ω Γ x) +
        (1 - a) * Real.log (sourceTestCurveRealMassAt ω Γ y)
      = Real.log (sourceTestCurveRealMassAt ω Γ y ^ (1 - a) *
          sourceTestCurveRealMassAt ω Γ x ^ a) := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hy' _).ne' (Real.rpow_pos_of_pos hx' _).ne',
          Real.log_rpow hy', Real.log_rpow hx']
        ring
    _ ≤ Real.log (sourceTestCurveRealMassAt ω Γ (a * x + (1 - a) * y)) :=
        Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hy' _) (Real.rpow_pos_of_pos hx' _)) h

end General

/-- **`prop:testcurvmasslogconc`, concavity.** On a compact connected Kähler manifold of dimension
`n = q + 1`, for every test curve `Γ ∈ TC(X, θ)_{>0}`, `τ ↦ log ∫_X θ_{Γ_τ}ⁿ` is concave on
`(-∞, Γ_max)`. -/
theorem concaveOn_log_sourceTestCurveRealMassAt {q : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (q + 1)) M] [IsComplexManifold (q + 1) M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M)} (ω : KahlerBackground (q + 1) M)
    (Γ : SourceTestCurve θ) :
    ConcaveOn ℝ (Iio Γ.max) (fun τ => Real.log (sourceTestCurveRealMassAt ω Γ τ)) :=
  concaveOn_log_sourceTestCurveRealMassAt_of ω Γ fun h₀ h₁ s hs => by
    have h := sourceConvexCombMass_logConcave ω _ h₀ h₁ (t₀ := 0) (t₁ := 1) (s := s)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hs
    simpa only [mul_zero, zero_add, mul_one] using h

/-- **`prop:testcurvmasslogconc`, concavity, dimension `0`.** -/
theorem concaveOn_log_sourceTestCurveRealMassAt_of_dim_zero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M)} (ω : KahlerBackground 0 M)
    (Γ : SourceTestCurve θ) :
    ConcaveOn ℝ (Iio Γ.max) (fun τ => Real.log (sourceTestCurveRealMassAt ω Γ τ)) :=
  concaveOn_log_sourceTestCurveRealMassAt_of ω Γ fun h₀ h₁ s hs => by
    have h := (sourceConvexCombMass_logConcave_of_dim_zero _ h₀ h₁).2.1 (t₀ := 0) (t₁ := 1)
      (s := s) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ hs
    simpa only [mul_zero, zero_add, mul_one] using h

end SGPT.NPP.LogConcavityDinew
