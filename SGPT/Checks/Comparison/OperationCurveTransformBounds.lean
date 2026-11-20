import SGPT.NAPotential.BJPrepDivisorialTransform
import SGPT.PSH.SourceTestCurveClosedness

/-! Actual original transform finiteness and endpoint-inclusive bounds.
Blueprint: operation-sum-legendre.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open scoped ENNReal
open Set SGPT.NAPotential.BJPrep
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

omit [ConnectedSpace X] [MeasurableSpace X] in
/-- The SAME actual original strict-slice transform has a produced finite
real representative, retaining the actual prime and nonnegative real weight. -/
theorem curveDivisorialTransform_finite (C : SourceTestCurvePredata θ)
    (p : PrimePresentation n X) {t : ℝ} (ht : 0 ≤ t) :
    ∃ A : ℝ, curveDivisorialTransform C p t = (A : EReal) := by
  have hmax : curveDivisorialTransform C p t ≤ (C.max : EReal) := by
    refine iSup₂_le fun r hr => ?_
    rw [curveDivisorialTransform_term C p t hr]
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [sliceLelong_nonneg C p r]
  have htop : curveDivisorialTransform C p t ≠ ⊤ :=
    ne_of_lt (hmax.trans_lt (EReal.coe_lt_top C.max))
  have hs : C.max-1 < C.max := by linarith
  have hlo := le_curveDivisorialTransform C p t hs
  rw [curveDivisorialTransform_term C p t hs] at hlo
  have hbot : curveDivisorialTransform C p t ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo
  exact ⟨(curveDivisorialTransform C p t).toReal,(EReal.coe_toReal htop hbot).symm⟩

omit [MeasurableSpace X] in
/-- EVERY original cutoff-inclusive actual term is below the SAME
strict-slice transform. Actual endpoint reader and real bound are internal. -/
theorem curveDivisorialTransform_at_le (C : SourceTestCurvePredata θ)
    (p : PrimePresentation n X) {t : ℝ} (ht : 0 ≤ t) {r : ℝ} (hr : r ≤ C.max) :
    (r : EReal) - (t : EReal) *
      ((presentationReader (sourceTestCurveAt C r) p : ℝ≥0∞) : EReal) ≤
      curveDivisorialTransform C p t := by
  obtain ⟨A,hA⟩ := curveDivisorialTransform_finite C p ht
  have hφ := (source_test_curve_extension_whole C).2.2.2 r hr
  have hν := presentationReader_ne_top hφ p
  rw [← EReal.coe_ennreal_toReal hν, ← EReal.coe_mul, ← EReal.coe_sub,hA]
  apply EReal.coe_le_coe_iff.mpr
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let s : ℝ := r-ε
  have hs : s < C.max := by dsimp only [s]; linarith
  have hreader : presentationReader (C.potential ⟨s,hs⟩) p ≤
      presentationReader (sourceTestCurveAt C r) p := by
    apply presentationReader_anti
    intro x
    rw [← sourceTestCurveAt_of_lt C hs]
    exact C.at_antitone x (by dsimp only [s]; linarith)
  have hreal := ENNReal.toReal_mono hν hreader
  have hterm := le_curveDivisorialTransform C p t hs
  rw [curveDivisorialTransform_term C p t hs,hA] at hterm
  have htermR := EReal.coe_le_coe_iff.mp hterm
  rw [sliceLelong_of_lt C p hs] at htermR
  dsimp only [s] at htermR
  nlinarith [mul_le_mul_of_nonneg_left hreal ht]

end SGPT.NAPotential.OperationComparison
