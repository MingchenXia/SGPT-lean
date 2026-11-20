import SGPT.NAPotential.DHFlagAllDimensions
import SGPT.NAPotential.DHOrderContinuity
import SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents

/-! All-dimensional literal source flag continuity; actual canonical zero flag.
Source: SGPT 69360cfd, prop:contDH. Universal positive-dimensional
flag-bearing modification existence is not asserted here. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DHSource
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n F.carrier)}

/-- The actual source flag pushforward as a finite Borel measure. -/
def naFiniteDuistermaatHeckman
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) : FiniteMeasure ℝ :=
  ⟨naDuistermaatHeckman F hbig Γ, naDuistermaatHeckman_finite F hbig Γ⟩

/-- Actual equality, including the true zero-dimensional Lebesgue pushforward. -/
theorem naFiniteDuistermaatHeckman_eq_intrinsic (omega : KahlerBackground n F.carrier)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    naFiniteDuistermaatHeckman F hbig Γ = DH.naIntrinsicFiniteDuistermaatHeckman omega Γ := by
  apply Subtype.ext
  exact naDuistermaatHeckman_eq_intrinsic F omega hbig Γ

/-- Source decreasing continuity for the literal flag formula in every dimension.
The volume convergence is exactly the source's printed additional hypothesis. -/
theorem naDuistermaatHeckman_tendsto_of_order_infimum
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naFiniteDuistermaatHeckman F hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman F hbig Γ)) := by
  simpa only [naFiniteDuistermaatHeckman_eq_intrinsic F F.omega] using
    DH.naIntrinsicDuistermaatHeckman_tendsto_of_order_infimum
      F.omega Γs Γ ha hbound hgreatest hvol

/-- Source increasing continuity for the literal flag formula in every dimension;
no extra volume, slice-mass or weak-limit convergence is assumed. -/
theorem naDuistermaatHeckman_tendsto_of_order_supremum
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckman F hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckman F hbig Γ)) := by
  simpa only [naFiniteDuistermaatHeckman_eq_intrinsic F F.omega] using
    DH.naIntrinsicDuistermaatHeckman_tendsto_of_order_supremum
      F.omega Γs Γ hmono hbound hleast

section OriginalZero
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel 0) M]
  [IsComplexManifold 0 M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] {θ' : AtlasClosedRealOneOneForm (ofFixedModel 0 M)}

/-- The actual whole original zero-dimensional manifold is its unique flag level. -/
def zeroFlag : Fin (0 + 1) → Set M := fun _ => univ

omit [IsComplexManifold 0 M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Genuine ambient regularity proves the canonical original flag smooth. -/
theorem zeroFlag_isSmooth : IsSmoothFlag (zeroFlag (M := M)) := by
  refine ⟨rfl, fun _ _ _ => subset_rfl, ?_⟩
  intro i
  refine ⟨isClosed_univ, isConnected_univ, ?_⟩
  intro x _
  simpa only [zeroFlag, Nat.zero_sub] using
    SGPT.Foundations.Analysis.Pending.AnalyticIrreducibleComponents.regularAtDim_univ
      (n := 0) x

/-- An actual original zero flag, without a supplied flag or modification premise. -/
def zeroFlagGeometry (omega : KahlerBackground 0 M) : OriginalFlagGeometry.{u} 0 :=
  OriginalFlagGeometry.ofOriginal omega zeroFlag zeroFlag_isSmooth

local instance zeroFlagGeometryMeasurable (omega : KahlerBackground 0 M) :
    MeasurableSpace (zeroFlagGeometry omega).carrier := ‹MeasurableSpace M›
local instance zeroFlagGeometryBorel (omega : KahlerBackground 0 M) :
    BorelSpace (zeroFlagGeometry omega).carrier := ‹BorelSpace M›

/-- Literal source DH on arbitrary original dimension-zero manifolds;
the actual flag is constructed internally. -/
def naFiniteDuistermaatHeckmanOriginalZero (omega : KahlerBackground 0 M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (Γ : SourcePositiveIModelTestCurve θ') : FiniteMeasure ℝ :=
  naFiniteDuistermaatHeckman (zeroFlagGeometry omega) hbig Γ

/-- The constructed original flag measure is the original intrinsic measure. -/
theorem naFiniteDuistermaatHeckmanOriginalZero_eq_intrinsic (omega : KahlerBackground 0 M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (Γ : SourcePositiveIModelTestCurve θ') :
    naFiniteDuistermaatHeckmanOriginalZero omega hbig Γ =
      DH.naIntrinsicFiniteDuistermaatHeckman omega Γ := by
  exact naFiniteDuistermaatHeckman_eq_intrinsic (zeroFlagGeometry omega) omega hbig Γ

/-- The complete decreasing source conclusion in dimension zero on the original X,
with its actual flag constructed rather than supplied. -/
theorem naDuistermaatHeckmanOriginalZero_tendsto_of_order_infimum
    (omega : KahlerBackground 0 M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (Γs : ℕ → SourcePositiveIModelTestCurve θ') (Γ : SourcePositiveIModelTestCurve θ')
    (ha : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs j))
      (sourcePositiveTestCurveToNA (Γs i)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i)))
    (hgreatest : ∀ Ξ : SourceNAPotential θ',
      (∀ i, SourceNAPOrder Ξ (sourcePositiveTestCurveToNA (Γs i))) →
      SourceNAPOrder Ξ (sourcePositiveTestCurveToNA Γ))
    (hvol : Tendsto (fun i => sourceNAVolume (sourcePositiveTestCurveToNA (Γs i))) atTop
      (𝓝 (sourceNAVolume (sourcePositiveTestCurveToNA Γ)))) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanOriginalZero omega hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOriginalZero omega hbig Γ)) := by
  exact naDuistermaatHeckman_tendsto_of_order_infimum
    (zeroFlagGeometry omega) hbig Γs Γ ha hbound hgreatest hvol

/-- The complete increasing source conclusion in dimension zero on the original X. -/
theorem naDuistermaatHeckmanOriginalZero_tendsto_of_order_supremum
    (omega : KahlerBackground 0 M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ')))
    (Γs : ℕ → SourcePositiveIModelTestCurve θ') (Γ : SourcePositiveIModelTestCurve θ')
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ',
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanOriginalZero omega hbig (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOriginalZero omega hbig Γ)) := by
  exact naDuistermaatHeckman_tendsto_of_order_supremum
    (zeroFlagGeometry omega) hbig Γs Γ hmono hbound hleast
end OriginalZero
end SGPT.NAPotential.DHSource
