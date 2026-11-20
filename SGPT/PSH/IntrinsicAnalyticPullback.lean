import SGPT.PSH.OriginalAnalyticConventions
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.AnalyticTypeRestriction
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false
noncomputable section

universe u

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped ContDiff Manifold

variable {n m : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ChartedSpace (ComplexModel m) Y] [IsComplexManifold m Y]

/-- Consume genuine all-chart pullback, then the existing original connected producer. -/
theorem HasRationalAnalyticType.comp_holomorphic {u : X → EReal} {f : Y → X}
    (hu : (ofFixedModel n X).HasRationalAnalyticType u)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (ofFixedModel m Y).HasRationalAnalyticType (u ∘ f) := by
  have hnative : HasManifoldAnalyticSingularityType (n := n) u :=
    hasRationalAnalyticType_iff_chartType.mp hu
  exact hasRationalAnalyticType_iff_chartType.mpr
    (AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hf hnative)

/-- Retain exactly c and the actual pulled-back coherent ideal at every original stalk. -/
theorem HasCoherentRationalAnalyticType.pullback {u : X → EReal} {c : ℚ}
    {I : GermIdeal n X} {f : Y → X}
    (hu : (ofFixedModel n X).HasCoherentRationalAnalyticType u c I)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (ofFixedModel m Y).HasCoherentRationalAnalyticType (u ∘ f) c
      (GermIdeal.pullback (m := m) f I) :=
  hasCoherentRationalAnalyticType_iff_native.mpr
    (AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hf
      (hasCoherentRationalAnalyticType_iff_native.mp hu))

section Modification

variable {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel n) Z] [IsComplexManifold n Z]

/-- Strong native pullback internally gives upstairs nondegeneracy for original QPSH. -/
theorem IsQPSH.comp_analyticModification {u : X → EReal} {π : Z → X}
    (hu : (ofFixedModel n X).IsQPSH u) (hπ : IsAnalyticModification (n := n) π) :
    (ofFixedModel n Z).IsQPSH (u ∘ π) := by
  obtain ⟨θ, hθ⟩ := hu
  let a := atlasClosedFormToNative θ
  have hnative := (isThetaPSH_iff_nativeThetaPotential θ u).mp hθ
  have hp := AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ a hnative
  let b := ClosedRealOneOneForm.pullback hπ.1 a
  refine ⟨nativeClosedFormToAtlas b,
    (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas b) (u ∘ π)).mpr ?_⟩
  have hback : atlasClosedFormToNative (nativeClosedFormToAtlas b) = b := by
    rcases b with ⟨b, hb⟩
    cases b
    rfl
  rw [hback]
  exact hp

/-- Pair actual global QPSH and original connected analytic type for the same composition. -/
theorem IsQPSH.comp_intrinsic_analyticModification {u : X → EReal} {π : Z → X}
    (hu : (ofFixedModel n X).IsQPSH u)
    (han : (ofFixedModel n X).HasRationalAnalyticType u)
    (hπ : IsAnalyticModification (n := n) π) :
    (ofFixedModel n Z).IsQPSH (u ∘ π) ∧
      (ofFixedModel n Z).HasRationalAnalyticType (u ∘ π) :=
  ⟨hu.comp_analyticModification hπ, han.comp_holomorphic hπ.1⟩

end Modification
end SGPT.PSH.VariableComplexAtlas
