import SGPT.PSH.SourceTestCurveBasedness
import SGPT.PSH.SourceIEnvelope
import SGPT.PSH.SourcePMassCharacterization

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- EVERY genuine original open slice is an actual native I-model potential.
This retains genuine theta-PSH and literal I-envelope fixedness. -/
def SourceTestCurveIsIModel (Γ : SourceTestCurve θ) : Prop :=
  ∀ r : Iio Γ.max, IEnvelope.IsIModelPotential (atlasClosedFormToNative θ).val (Γ.potential r)

/-- The original based I-model test-curve collection, with actual basedness. -/
def SourceIModelTestCurves (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (hφ : SourceModelPotential θ φ) : Set (SourceTestCurve θ) :=
  {Γ | Γ ∈ SourceTestCurvesBased θ φ hφ ∧ SourceTestCurveIsIModel Γ}

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal original based membership and ALL open I-model slices. -/
theorem sourceIModelTestCurves_iff {φ : M → EReal} (hφ : SourceModelPotential θ φ)
    (Γ : SourceTestCurve θ) :
    Γ ∈ SourceIModelTestCurves θ φ hφ ↔
      Γ ∈ SourceTestCurvesBased θ φ hφ ∧ SourceTestCurveIsIModel Γ := Iff.rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- The same actual slice satisfies the original all-chart source predicate. -/
theorem sourceIModelTestCurve_slice {φ : M → EReal} {hφ : SourceModelPotential θ φ}
    {Γ : SourceTestCurve θ} (hΓ : Γ ∈ SourceIModelTestCurves θ φ hφ) (r : Iio Γ.max) :
    sourceIModel θ (Γ.potential r) :=
  (sourceIModel_iff_native θ (Γ.potential r)).mpr (hΓ.2 r)

/-- The actual original union over ALL positive ordinary model bases. -/
def SourceIModelTestCurvesPositive (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    Set (SourceTestCurve θ) :=
  {Γ | ∃ (φ : M → EReal) (hφ : SourceModelPotential θ φ), Γ ∈ SourceIModelTestCurves θ φ hφ}

omit [BorelSpace M] [ConnectedSpace M] in
/-- Exact original positive union reader, retaining the same object. -/
theorem sourceIModelTestCurvesPositive_iff (Γ : SourceTestCurve θ) :
    Γ ∈ SourceIModelTestCurvesPositive θ ↔
      ∃ (φ : M → EReal) (hφ : SourceModelPotential θ φ), Γ ∈ SourceIModelTestCurves θ φ hφ := Iff.rfl

/-- Genuine produced limit-model basedness supplies the original union witness. -/
theorem sourceIModelTestCurvesPositive_iff_slices (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    Γ ∈ SourceIModelTestCurvesPositive θ ↔ SourceTestCurveIsIModel Γ := by
  constructor
  · rintro ⟨φ, hφ, hΓ⟩
    exact hΓ.2
  · intro hI
    exact ⟨sourceTestCurveLimit Γ.toSourceTestCurvePredata, Γ.limit_model omega,
      Γ.mem_based_limit omega, hI⟩

/-- Original notation with the base omitted means the SAME actual V_theta. -/
def SourceIModelTestCurvesMinimal (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    Set (SourceTestCurve θ) :=
  SourceIModelTestCurves θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model omega θ hbig)

/-- Literal minimal-model notation, with its positive model produced from bigness. -/
theorem sourceIModelTestCurvesMinimal_iff (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourceTestCurve θ) :
    Γ ∈ SourceIModelTestCurvesMinimal omega θ hbig ↔
      Γ ∈ SourceTestCurvesBased θ (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_model omega θ hbig) ∧ SourceTestCurveIsIModel Γ := Iff.rfl

end SGPT.PSH.VariableComplexAtlas
