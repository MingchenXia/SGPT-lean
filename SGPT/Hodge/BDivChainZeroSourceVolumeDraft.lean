import SGPT.Hodge.BDivChainZeroCofinalDraft

/-!
# Actual model-volume net at zero dimension

The source `def:volb` defines volume by the limit of actual
model class volumes for pseudo-effective b-divisors. Here the zero-dimensional
net is shown constant using actual class volumes; this is stronger evidence
than the formula for a conditional infimum alone. No pre-existing zero-
dimensional source b-divisor-volume constant is claimed to exist.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
open scoped Topology ENNReal

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

/-- The book's actual model class-volume net converges to the proposed
conditional infimum; pseudo-effectivity and its value are separately derived. -/
theorem tendsto_actualModelVolume_zero {S : ModelSystem 0 X} (D : WeilFamilyAny S) :
    IsPseudoeffectiveAny D ∧
      Tendsto (fun π : S.Model => Modification.classVolume π.1 (D.val π)) atTop
        (𝓝 (volumeAny D)) := by
  refine ⟨isPseudoeffectiveAny_of_dim_zero D, ?_⟩
  rw [volumeAny_eq_one_of_dim_zero D]
  have heq : (fun π : S.Model => Modification.classVolume π.1 (D.val π)) =
      (fun _ : S.Model => (1 : ℝ≥0∞)) := by
    funext π
    exact modelClassVolume_eq_one_of_dim_zero π.1 (D.val π)
  rw [heq]
  exact tendsto_const_nhds

/-- In particular, use the book's actual blowup model system and the same
literal directed net, including the genuine nonempty root. -/
theorem tendsto_bookModelVolume_zero
    (D : WeilFamilyAny (ModelSystem.blowup 0 X)) :
    Tendsto (fun π : (ModelSystem.blowup 0 X).Model =>
      Modification.classVolume π.1 (D.val π)) atTop (𝓝 (volumeAny D)) :=
  (tendsto_actualModelVolume_zero D).2

/-- The same conclusion for the separate actual system of all analytic
modifications. This does not equate arbitrary families on two systems; it
uses the actual zero-dimensional mass on every model. -/
theorem tendsto_allModelVolume_zero
    (D : WeilFamilyAny (ModelSystem.all 0 X)) :
    Tendsto (fun π : (ModelSystem.all 0 X).Model =>
      Modification.classVolume π.1 (D.val π)) atTop (𝓝 (volumeAny D)) :=
  (tendsto_actualModelVolume_zero D).2

end SGPT.Hodge.BDivChain.NativeDraft

namespace SGPT.Hodge.BDivChain.NativeDraft

open Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending SGPT.BDivisor
open scoped Topology ENNReal

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [ConnectedSpace X]

/-- The positive-dimensional original book-model volume net is transported
along the actual family comparison and the existing source limit theorem. -/
theorem tendsto_bookModelVolume_pos
    (hK : Nonempty (KahlerBackground (m + 1) X))
    (D : WeilFamilyAny (ModelSystem.blowup (m + 1) X))
    (hD : IsPseudoeffectiveAny D) :
    Tendsto (fun π : (ModelSystem.blowup (m + 1) X).Model =>
      Modification.classVolume π.1 (D.val π)) atTop (𝓝 (volumeAny D)) := by
  rw [volumeAny_eq_existing (Nat.succ_pos m) D]
  simpa only [toExisting_onModel] using
    (WeilBDivisorOn.tendsto_vol_blowup hK
      ((isPseudoeffectiveAny_iff_existing (Nat.succ_pos m) D).mp hD))

end SGPT.Hodge.BDivChain.NativeDraft
