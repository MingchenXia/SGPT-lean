import SGPT.NAPotential.DHSourceContinuity
import SGPT.NAPotential.DHGeneral

/-! Genuine all-dimensional supplied-modification DH tails and original-index
weak continuity. The existence of a flag-bearing modification is not assumed
as a certificate for a universal source theorem. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DHSource
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)}
  (F : OriginalFlagGeometry.{u} n) [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {π : F.carrier → X}

/-- The genuine positive pulled-back limit mass produces its big background. -/
theorem positiveCurveModificationPullback_isBig
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (θ.nativeHolomorphicPullback hπ.1))) := by
  let G := DH.positiveCurveModificationPullback hπ F.omega Γ
  exact sourcePositiveMass_isBig F.omega G.val.limit_thetaPSH G.val.positiveLimitMass

/-- Literal source eq:DHmgeneral on the actual given modification and flag,
with the actual original curve pulled back, in every dimension. -/
def naDuistermaatHeckmanOnModification
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ) :
    Measure ℝ :=
  naDuistermaatHeckman F (positiveCurveModificationPullback_isBig F hπ Γ)
    (DH.positiveCurveModificationPullback hπ F.omega Γ)

instance naDuistermaatHeckmanOnModification_finite
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ) :
    IsFiniteMeasure (naDuistermaatHeckmanOnModification F hπ Γ) := by
  unfold naDuistermaatHeckmanOnModification
  infer_instance

/-- Genuine all-dimensional flag measure tail is the same original slice mass.
No tail identity or measure equality is supplied by the caller. -/
theorem naDuistermaatHeckmanOnModification_Ici
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ)
    (t : ℝ) (ht : t < Γ.val.max) :
    naDuistermaatHeckmanOnModification F hπ Γ (Ici t) =
      sourcePotentialNonPluripolarMeasure θ (Γ.val.potential ⟨t, ht⟩)
        (Γ.val.thetaPSH ⟨t, ht⟩) univ := by
  unfold naDuistermaatHeckmanOnModification
  rw [naDuistermaatHeckman_eq_intrinsic F F.omega]
  rw [DH.naIntrinsicDuistermaatHeckman_Ici F.omega
    (DH.positiveCurveModificationPullback hπ F.omega Γ) ⟨t, ht⟩]
  exact DH.positiveCurveModificationPullback_slice_mass hπ F.omega Γ t ht

/-- The literal upstairs measure vanishes above the same original cutoff. -/
theorem naDuistermaatHeckmanOnModification_Ioi_max
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanOnModification F hπ Γ (Ioi Γ.val.max) = 0 := by
  unfold naDuistermaatHeckmanOnModification
  rw [naDuistermaatHeckman_eq_intrinsic F F.omega]
  exact DH.naIntrinsicDuistermaatHeckman_Ioi_max F.omega _

/-- All-dimensional actual modification comparison from original slice masses
and cutoff, retaining the original downstairs intrinsic measure. -/
theorem naDuistermaatHeckmanOnModification_eq_intrinsic
    (omega : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanOnModification F hπ Γ = DH.naIntrinsicDuistermaatHeckman omega Γ := by
  apply DH.measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact naDuistermaatHeckmanOnModification_Ioi_max F hπ Γ
  · exact DH.naIntrinsicDuistermaatHeckman_Ioi_max omega Γ
  · intro t ht
    rw [naDuistermaatHeckmanOnModification_Ici F hπ Γ t ht,
      DH.naIntrinsicDuistermaatHeckman_Ici omega Γ ⟨t, ht⟩]

/-- Genuine source independence of any two actually supplied modifications,
including dimension zero, without supplying equality of their measures. -/
theorem naDuistermaatHeckmanOnModification_independent
    (omega : KahlerBackground n X)
    {F₁ F₂ : OriginalFlagGeometry.{u} n}
    [MeasurableSpace F₁.carrier] [BorelSpace F₁.carrier]
    [MeasurableSpace F₂.carrier] [BorelSpace F₂.carrier]
    {π₁ : F₁.carrier → X} {π₂ : F₂.carrier → X}
    (hπ₁ : IsAnalyticModification (n := n) π₁)
    (hπ₂ : IsAnalyticModification (n := n) π₂)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naDuistermaatHeckmanOnModification F₁ hπ₁ Γ =
      naDuistermaatHeckmanOnModification F₂ hπ₂ Γ := by
  exact (naDuistermaatHeckmanOnModification_eq_intrinsic F₁ omega hπ₁ Γ).trans
    (naDuistermaatHeckmanOnModification_eq_intrinsic F₂ omega hπ₂ Γ).symm

/-- Original source measure on an actual model, with its produced finite mass. -/
def naFiniteDuistermaatHeckmanOnModification
    (hπ : IsAnalyticModification (n := n) π) (Γ : SourcePositiveIModelTestCurve θ) :
    FiniteMeasure ℝ :=
  ⟨naDuistermaatHeckmanOnModification F hπ Γ,
    naDuistermaatHeckmanOnModification_finite F hπ Γ⟩

theorem naFiniteDuistermaatHeckmanOnModification_eq_intrinsic
    (omega : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naFiniteDuistermaatHeckmanOnModification F hπ Γ =
      DH.naIntrinsicFiniteDuistermaatHeckman omega Γ := by
  apply Subtype.ext
  exact naDuistermaatHeckmanOnModification_eq_intrinsic F omega hπ Γ

/-- Actual all-dimensional decreasing source continuity on a given model,
using the original sequence, original infimum and printed volume hypothesis. -/
theorem naDuistermaatHeckmanOnModification_tendsto_of_order_infimum
    (omega : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
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
    Tendsto (fun i => naFiniteDuistermaatHeckmanOnModification F hπ (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOnModification F hπ Γ)) := by
  simpa only [naFiniteDuistermaatHeckmanOnModification_eq_intrinsic F omega hπ] using
    DH.naIntrinsicDuistermaatHeckman_tendsto_of_order_infimum
      omega Γs Γ ha hbound hgreatest hvol

/-- Actual all-dimensional increasing source continuity on a given model;
no extra volume or tail-convergence premise is added. -/
theorem naDuistermaatHeckmanOnModification_tendsto_of_order_supremum
    (omega : KahlerBackground n X) (hπ : IsAnalyticModification (n := n) π)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanOnModification F hπ (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOnModification F hπ Γ)) := by
  simpa only [naFiniteDuistermaatHeckmanOnModification_eq_intrinsic F omega hπ] using
    DH.naIntrinsicDuistermaatHeckman_tendsto_of_order_supremum
      omega Γs Γ hmono hbound hleast
end SGPT.NAPotential.DHSource
