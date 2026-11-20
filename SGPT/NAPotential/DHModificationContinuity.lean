import SGPT.NAPotential.DHOrderContinuity
import SGPT.NAPotential.DHIntrinsicModification

/-! order-theoretic continuity for the actual DH measures
of a supplied flag-bearing modification. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DH
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)}
  {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {π : F.carrier → X}

/-- The source formula on an actual supplied modification, as a finite measure. -/
def naFiniteDuistermaatHeckmanOnModification
    (hπ : IsAnalyticModification (n := m + 1) π) (Γ : SourcePositiveIModelTestCurve θ) :
    FiniteMeasure ℝ :=
  ⟨naDuistermaatHeckmanOnModification (F := F) hπ Γ,
    naDuistermaatHeckmanOnModification_finite (F := F) hπ Γ⟩

theorem naFiniteDuistermaatHeckmanOnModification_eq_intrinsic
    (omega : KahlerBackground (m + 1) X) (hπ : IsAnalyticModification (n := m + 1) π)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naFiniteDuistermaatHeckmanOnModification (F := F) hπ Γ =
      naIntrinsicFiniteDuistermaatHeckman omega Γ := by
  apply Subtype.ext
  exact (naIntrinsicDuistermaatHeckman_eq_onModification (F := F) omega hπ Γ).symm

/-- Decreasing source continuity on an actually supplied modification. -/
theorem naDuistermaatHeckmanOnModification_tendsto_of_order_infimum
    (omega : KahlerBackground (m + 1) X) (hπ : IsAnalyticModification (n := m + 1) π)
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
    Tendsto (fun i => naFiniteDuistermaatHeckmanOnModification (F := F) hπ (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOnModification (F := F) hπ Γ)) := by
  simpa only [naFiniteDuistermaatHeckmanOnModification_eq_intrinsic (F := F) omega hπ] using
    naIntrinsicDuistermaatHeckman_tendsto_of_order_infimum omega Γs Γ ha hbound hgreatest hvol

/-- Increasing source continuity on an actually supplied modification. -/
theorem naDuistermaatHeckmanOnModification_tendsto_of_order_supremum
    (omega : KahlerBackground (m + 1) X) (hπ : IsAnalyticModification (n := m + 1) π)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (hmono : ∀ i j, i ≤ j → SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA (Γs j)))
    (hbound : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ))
    (hleast : ∀ Ξ : SourceNAPotential θ,
      (∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i)) Ξ) →
      SourceNAPOrder (sourcePositiveTestCurveToNA Γ) Ξ) :
    Tendsto (fun i => naFiniteDuistermaatHeckmanOnModification (F := F) hπ (Γs i)) atTop
      (𝓝 (naFiniteDuistermaatHeckmanOnModification (F := F) hπ Γ)) := by
  simpa only [naFiniteDuistermaatHeckmanOnModification_eq_intrinsic (F := F) omega hπ] using
    naIntrinsicDuistermaatHeckman_tendsto_of_order_supremum omega Γs Γ hmono hbound hleast

end SGPT.NAPotential.DH
