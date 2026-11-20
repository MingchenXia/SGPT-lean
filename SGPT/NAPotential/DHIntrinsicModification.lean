import SGPT.NAPotential.DHIntrinsicCore
import SGPT.NAPotential.DHGeneral

/-! Identification with a supplied actual flag-bearing modification.
No existence of such a modification is asserted. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DH
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

section Comparison

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) X)}
  {F : OriginalFlagGeometry.{u} (m + 1)} [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {π : F.carrier → X}

theorem naIntrinsicDuistermaatHeckman_eq_onModification
    (omega : KahlerBackground (m + 1) X) (hπ : IsAnalyticModification (n := m + 1) π)
    (Γ : SourcePositiveIModelTestCurve θ) :
    naIntrinsicDuistermaatHeckman omega Γ = naDuistermaatHeckmanOnModification (F := F) hπ Γ := by
  apply measure_eq_of_Ici_of_Ioi_eq_zero _ _ Γ.val.max
  · exact naIntrinsicDuistermaatHeckman_Ioi_max omega Γ
  · exact naDuistermaatHeckmanOnModification_Ioi_max (F := F) hπ Γ
  · intro t ht
    rw [naIntrinsicDuistermaatHeckman_Ici omega Γ ⟨t, ht⟩,
      naDuistermaatHeckmanOnModification_Ici (F := F) hπ Γ t ht]

end Comparison
end SGPT.NAPotential.DH
