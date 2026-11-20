import SGPT.PSH.VariableComponentConverse
import SGPT.PSH.GeometricQDivisor

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- A genuine native irreducible carrier on the SAME original component
has genuine ORIGINAL all-chart analytic irreducibility. The arbitrary
component anchor need not lie in the carrier. No native structure is an input. -/
theorem hasIrreducibleAnalyticChartEquations_componentImage
    [T2Space X] [ParacompactSpace X] (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ S : Set (A.componentOpen x), IsComplexAnalyticallyIrreducible (n := A.pointDimension x) S →
      A.HasIrreducibleAnalyticChartEquations (Subtype.val '' S) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro S hS
  refine ⟨A.hasAnalyticChartEquations_componentImage x S hS.analytic,
    hS.nonempty.image Subtype.val, ?_⟩
  intro B C hB hC hBS hCS hcover
  have hpre (D : Set X) (hDS : D ⊆ Subtype.val '' S) :
      (Subtype.val ⁻¹' D : Set (A.componentOpen x)) ⊆ S := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := hDS hq
    exact (Subtype.val_injective hpq) ▸ hp
  have hsplit : S = (Subtype.val : A.componentOpen x → X) ⁻¹' B ∪ Subtype.val ⁻¹' C := by
    calc
      S = (Subtype.val : A.componentOpen x → X) ⁻¹' (Subtype.val '' S) := by
        ext q
        simp only [mem_preimage, mem_image, Subtype.val_inj, exists_eq_right]
      _ = _ := by rw [hcover, preimage_union]
  rcases hS.eq_left_or_eq_right (hB.componentAnalytic x) (hC.componentAnalytic x)
    (hpre B hBS) (hpre C hCS) hsplit with h | h
  · left
    apply Subset.antisymm _ hBS
    rintro z ⟨q, hq, rfl⟩
    rw [h] at hq
    exact hq
  · right
    apply Subset.antisymm _ hCS
    rintro z ⟨q, hq, rfl⟩
    rw [h] at hq
    exact hq

/-- The literal image of ANY genuine canonical component prime is
irreducible for EVERY original varying-dimension chart and analytic cut. -/
theorem geometricPrimeCarrier_componentImage_original_irreducible
    [T2Space X] [ParacompactSpace X] (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ P : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
      A.HasIrreducibleAnalyticChartEquations (Subtype.val '' P.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro P
  apply A.hasIrreducibleAnalyticChartEquations_componentImage x P.val
  rw [← P.subvariety_carrier]
  exact P.subvariety.irreducible_carrier

end SGPT.PSH.VariableComplexAtlas
