import SGPT.PSH.SourceTestCurveShift
import SGPT.PSH.SourceTestCurveLegendreCorrespondence

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The ORIGINAL additive parameter convention, on EVERY original test curve. -/
def SourceTestCurve.translate (Γ : SourceTestCurve θ) (C : ℝ) : SourceTestCurve θ :=
  Γ.shift (-C)

/-- Literal original translated cutoff. -/
theorem SourceTestCurve.translate_max (Γ : SourceTestCurve θ) (C : ℝ) :
    (Γ.translate C).max = Γ.max + C := by
  change Γ.max - -C = Γ.max + C
  ring

/-- Literal original sub-cutoff potential, retaining all poles. -/
theorem SourceTestCurve.translate_potential (Γ : SourceTestCurve θ) (C : ℝ)
    (r : Iio (Γ.translate C).max) :
    (Γ.translate C).potential r = Γ.potential
      ⟨r.1 - C, by have h := r.2; change r.1 < Γ.max - -C at h; change r.1 - C < Γ.max; linarith⟩ := rfl

/-- The SAME actual spatial USC limit and hence SAME positive limit mass. -/
theorem SourceTestCurve.translate_limit (Γ : SourceTestCurve θ) (C : ℝ) :
    sourceTestCurveLimit (Γ.translate C).toSourceTestCurvePredata =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata :=
  Γ.toSourceTestCurvePredata.shift_limit (-C)

/-- Zero additive translation preserves the entire actual original object. -/
theorem SourceTestCurve.translate_zero (Γ : SourceTestCurve θ) : Γ.translate 0 = Γ := by
  apply SourceTestCurve.ext_of_max_potential _ Γ
  · simp only [Γ.translate_max 0, add_zero]
  · intro r hr hr'
    change Γ.potential ⟨r + -0, _⟩ = Γ.potential ⟨r, hr'⟩
    congr 1
    apply Subtype.ext
    simp

/-- The WHOLE second original translation-proposition clause, with original
functions and actual objects; no sum-of-curves clause is inferred. -/
theorem SourceTestCurve.translate_translate (Γ : SourceTestCurve θ) (C D : ℝ) :
    (Γ.translate C).translate D = Γ.translate (C + D) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.translate_max]
    ring
  · intro r hr hr'
    change Γ.potential ⟨(r + -D) + -C, _⟩ = Γ.potential ⟨r + -(C + D), _⟩
    congr 1
    apply Subtype.ext
    ring

end SGPT.PSH.VariableComplexAtlas
