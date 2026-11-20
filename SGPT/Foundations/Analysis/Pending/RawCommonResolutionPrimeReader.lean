import SGPT.Foundations.Analysis.Pending.RawProperStrictTransformLelongReader
import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy

set_option autoImplicit false

/-! # Literal whole raw prime readers agree on genuine common resolutions over the same space -/

open Set Filter
open scoped Topology ENNReal Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawCommonResolutionPrimeReader

open FirstPass FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  AnalyticModificationLocalDiscrepancy

noncomputable section

/-- Genuine common-resolution geometry over the same original manifold internally
identifies the two whole raw prime readers, with no Lelong compatibility premise. -/
theorem iInf_lelongNumber_eq_of_common_resolution
    {n : ℕ} {X Y₀ Y₁ Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hπ₀ : IsAnalyticModification (n := n) π₀)
    (hπ₁ : IsAnalyticModification (n := n) π₁)
    (hg₀ : IsAnalyticModification (n := n) g₀)
    (hg₁ : IsAnalyticModification (n := n) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁)
    {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (V₀ : ClosedIrreducibleAnalyticSubvariety n Y₀)
    (V₁ : ClosedIrreducibleAnalyticSubvariety n Y₁)
    (W : ClosedIrreducibleAnalyticSubvariety n Z)
    (hstrict₀ : W.carrier = strictTransform n g₀ V₀.carrier)
    (hstrict₁ : W.carrier = strictTransform n g₁ V₁.carrier) :
    (⨅ y ∈ V₀.carrier, lelongNumber (n := n) (fun y => u (π₀ y)) y) =
      ⨅ y ∈ V₁.carrier, lelongNumber (n := n) (fun y => u (π₁ y)) y := by
  have hu₀ := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ₀.1 hu
  have hu₁ := GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp hπ₁.1 hu
  have h₀ := RawProperStrictTransformLelongReader.iInf_lelongNumber_comp_eq_of_strictTransform
    hg₀.1 hg₀.2.1 hu₀ V₀ W hstrict₀
  have h₁ := RawProperStrictTransformLelongReader.iInf_lelongNumber_comp_eq_of_strictTransform
    hg₁.1 hg₁.2.1 hu₁ V₁ W hstrict₁
  have hf : (fun z => u (π₀ (g₀ z))) = fun z => u (π₁ (g₁ z)) := by
    funext z
    exact congrArg u (congrFun hcomm z)
  rw [hf] at h₀
  exact h₀.symm.trans h₁

end
end SGPT.Foundations.Analysis.Pending.RawCommonResolutionPrimeReader
