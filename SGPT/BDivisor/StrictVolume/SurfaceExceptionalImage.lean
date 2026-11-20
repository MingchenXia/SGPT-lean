import SGPT.BDivisor.Modification
import SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
import Mathlib.Data.Set.Finite.Basic

/-! Actual finite exceptional images, using already proved codimension and isolated-point APIs. -/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.BDivisor.MovingCentresNext

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticDimensionBasics
open scoped Topology

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 2) X]
  [IsComplexManifold 2 X] [TopologicalSpace Y] [ChartedSpace (ComplexModel 2) Y]
  [IsComplexManifold 2 Y]

theorem originalSurfaceModification_exceptionalImage_dim_zero {g : Y → X}
    (hg : IsAnalyticModification (n := 2) g) :
    DimLE (n := 2) (g '' exceptionalLocus 2 g) 0 := by
  intro x d hx
  have h := AnalyticModificationExceptionalImageCodimension.add_one_le_pred_of_regularAtDim_image hg hx
  omega

variable [CompactSpace X]

theorem originalSurfaceModification_exceptionalImage_finite {g : Y → X}
    (hg : IsAnalyticModification (n := 2) g) :
    (g '' exceptionalLocus 2 g).Finite := by
  have hA := AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hg
  have hdim := originalSurfaceModification_exceptionalImage_dim_zero hg
  have hdisc : DiscreteTopology (g '' exceptionalLocus 2 g) := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    have h := not_accPt_of_locDimLE_zero hA hx (hdim.locDimLE x)
    rw [AccPt, not_neBot] at h
    exact h
  exact hA.isClosed.isCompact.finite ⟨hdisc⟩

theorem originalSurfaceModel_badPoints_finite (pi : Modification 2 X) :
    (pi.map '' exceptionalLocus 2 pi.map).Finite :=
  originalSurfaceModification_exceptionalImage_finite pi.isAnalyticModification

theorem originalSurfaceModel_eventually_isomorphism_near (pi : Modification 2 X)
    (p : ℕ → X) (hp : Function.Injective p) :
    ∀ᶠ i : ℕ in atTop, ∃ U : Set X, IsOpen U ∧ p i ∈ U ∧
      IsIsomorphismOver 2 pi.map U := by
  classical
  let B : Set X := pi.map '' exceptionalLocus 2 pi.map
  have hB : B.Finite := originalSurfaceModel_badPoints_finite pi
  have hindices : (p ⁻¹' B).Finite := Set.Finite.preimage hp.injOn hB
  obtain ⟨N, hN⟩ := hindices.bddAbove
  refine eventually_atTop.mpr ⟨N + 1, ?_⟩
  intro i hi
  have havoid : p i ∉ B := by
    intro hbad
    have hbound : i ≤ N := hN hbad
    omega
  exact ⟨Bᶜ, (AnalyticModificationExceptionalFibres.isClosed_image_exceptionalLocus
      pi.isAnalyticModification).isOpen_compl, havoid,
    AnalyticModificationExceptionalFibres.isIsomorphismOver_compl_image_exceptionalLocus
      pi.isAnalyticModification⟩

end SGPT.BDivisor.MovingCentresNext
