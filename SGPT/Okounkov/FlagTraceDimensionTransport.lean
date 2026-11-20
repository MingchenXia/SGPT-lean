import SGPT.Okounkov.FlagDimensionSubmanifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff
variable {a n m : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]

/-- Equality transport commutes with the ACTUAL whole holomorphic tensor
pullback, with the same original point map and native form. -/
theorem changeFlagDimensionForm_pullback (h : n = m) (F : OriginalFlagGeometry.{u} n)
    {f : F.carrier → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel a) ∞ f)
    (θ : ClosedRealOneOneForm a X) :
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    letI : IsComplexManifold m F.carrier := (changeFlagDimension h F).complex
    changeFlagDimensionForm h F (ClosedRealOneOneForm.pullback hf θ) =
      ClosedRealOneOneForm.pullback (contMDiff_changeFlagDimension_to_ambient h F hf) θ := by
  cases h
  rfl

/-- The LITERAL original normalized trace is unchanged pointwise under the
proved equal target dimension. The genuine trace domain, reference, map,
original potential and every pole are retained; this is equality transport,
not a P-equivalent or positive-mass replacement. -/
theorem sourceTraceEnvelope_changeFlagDimension [CompactSpace X]
    (h : n = m) (F : OriginalFlagGeometry.{u} n)
    (omega : KahlerBackground a X) {f : F.carrier → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel a) ∞ f)
    (θ : ClosedRealOneOneForm a X) (u : X → EReal) :
    letI : MeasurableSpace F.carrier := borel _
    letI : BorelSpace F.carrier := ⟨rfl⟩
    ∀ hdefined : SGPT.Trace.HasPositiveSourceTraceAlong omega F.omega hf θ u,
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    letI : IsComplexManifold m F.carrier := (changeFlagDimension h F).complex
    letI : MeasurableSpace (changeFlagDimension h F).carrier := borel _
    letI : BorelSpace (changeFlagDimension h F).carrier := ⟨rfl⟩
    SGPT.Trace.sourceTraceEnvelope omega (changeFlagDimension h F).omega
      (contMDiff_changeFlagDimension_to_ambient h F hf) θ u
      (hasPositiveSourceTraceAlong_changeFlagDimension h F omega hf θ u hdefined) =
      SGPT.Trace.sourceTraceEnvelope omega F.omega hf θ u hdefined := by
  cases h
  intro hdefined
  rfl

end SGPT.Okounkov.ToricTransport
