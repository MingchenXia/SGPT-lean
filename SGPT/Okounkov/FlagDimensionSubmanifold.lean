import SGPT.Okounkov.FlagDimensionTransport
import SGPT.Trace.TraceEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff

variable {a n m : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel a) X] [IsComplexManifold a X]

/-- Equality transport preserves actual holomorphy into the SAME inherited
submanifold atlas. Both regularity proofs describe the original same subset;
after equal dimensions are eliminated they agree by proof irrelevance. -/
theorem contMDiff_changeFlagDimension_to_submanifold
    (h : n = m) (F : OriginalFlagGeometry.{u} n) (S : Set X)
    (hn : n ≤ a) (hSn : ∀ p ∈ S, RegularAtDim (n := a) S p n)
    (hm : m ≤ a) (hSm : ∀ p ∈ S, RegularAtDim (n := a) S p m)
    {f : F.carrier → S}
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hn hSn
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    letI := SubmanifoldChartedSpace.chartedSpace hm hSm
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ f := by
  cases h
  exact hf

/-- Genuine inverse holomorphy under the SAME natural-number equality and
SAME inherited native atlas, retaining the literal original inverse map. -/
theorem contMDiff_changeFlagDimension_from_submanifold
    (h : n = m) (F : OriginalFlagGeometry.{u} n) (S : Set X)
    (hn : n ≤ a) (hSn : ∀ p ∈ S, RegularAtDim (n := a) S p n)
    (hm : m ≤ a) (hSm : ∀ p ∈ S, RegularAtDim (n := a) S p m)
    {f : S → F.carrier}
    (hf : letI := SubmanifoldChartedSpace.chartedSpace hn hSn
      ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    letI := SubmanifoldChartedSpace.chartedSpace hm hSm
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ f := by
  cases h
  exact hf

omit [IsComplexManifold a X] in
/-- The actual original inclusion into X keeps its actual holomorphy when
the independently produced equal source dimension is read back. -/
theorem contMDiff_changeFlagDimension_to_ambient
    (h : n = m) (F : OriginalFlagGeometry.{u} n) {f : F.carrier → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel a) ∞ f) :
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel a) ∞ f := by
  cases h
  exact hf

/-- The ORIGINAL defined-trace domain itself is unchanged by proved equal
target dimensions, with exactly the SAME map, points, reference and u.
There is no supplied trace-presentation or target positivity certificate. -/
theorem hasPositiveSourceTraceAlong_changeFlagDimension
    [CompactSpace X] (h : n = m) (F : OriginalFlagGeometry.{u} n)
    (omega : KahlerBackground a X) {f : F.carrier → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel a) ∞ f)
    (θ : ClosedRealOneOneForm a X) (u : X → EReal) :
    letI : MeasurableSpace F.carrier := borel _
    letI : BorelSpace F.carrier := ⟨rfl⟩
    SGPT.Trace.HasPositiveSourceTraceAlong omega F.omega hf θ u →
    letI : ChartedSpace (ComplexModel m) F.carrier := (changeFlagDimension h F).charts
    letI : IsComplexManifold m F.carrier := (changeFlagDimension h F).complex
    letI : MeasurableSpace (changeFlagDimension h F).carrier := borel _
    letI : BorelSpace (changeFlagDimension h F).carrier := ⟨rfl⟩
    SGPT.Trace.HasPositiveSourceTraceAlong omega (changeFlagDimension h F).omega
      (contMDiff_changeFlagDimension_to_ambient h F hf) θ u := by
  cases h
  exact fun hdefined => hdefined

end SGPT.Okounkov.ToricTransport
