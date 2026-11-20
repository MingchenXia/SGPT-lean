import SGPT.Foundations.Analysis.Pending.SourceGenericSubmanifoldMinimum
import SGPT.Foundations.Analysis.Pending.ConnectedJacobianCoefficient
import SGPT.Foundations.Analysis.Pending.IntrinsicModelJacobian


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.IntrinsicJacobianCoefficient

open Set Filter
open scoped Topology Manifold ContDiff
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong AnalyticModificationLocalDiscrepancy
  FixedGermNormalOrder ActualFlatNormalOrder ConnectedJacobianCoefficient

universe u

/-- Original common-model geometry INTERNALLY produces equality of the genuine whole coefficients. -/
theorem actualRelativeJacobianCoefficient_eq_of_common_resolution {m : ℕ} {X Y₀ Y₁ Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀] [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁] [IsComplexManifold (m + 1) Y₁]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hπ₀ : IsAnalyticModification (n := m + 1) π₀)
    (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    (hg₀ : IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : IsAnalyticModification (n := m + 1) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁)
    {E₀ : Set Y₀} {E₁ : Set Y₁}
    (hE₀ : IsClosedConnectedSubmanifold (m + 1) E₀ m)
    (hE₁ : IsClosedConnectedSubmanifold (m + 1) E₁ m)
    (hstrict : strictTransform (m + 1) g₀ E₀ = strictTransform (m + 1) g₁ E₁) :
    actualRelativeJacobianCoefficient hπ₀ hE₀ = actualRelativeJacobianCoefficient hπ₁ hE₁ := by
  obtain ⟨V₀, hV₀, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hE₀
  obtain ⟨V₁, hV₁, _⟩ :=
    SourceGenericSubmanifoldMinimum.exists_subvariety_carrier_eq_of_submanifold hE₁
  subst E₀
  subst E₁
  obtain ⟨z, Φ₀, Φ₁, hz₀, hz₁, hJ⟩ :=
    IntrinsicModelJacobian.exists_common_localJacobianOrder_eq hπ₀.1 hπ₁.1 hg₀ hg₁ hcomm
      V₀ V₁ hE₀.2.2 hE₁.2.2 hstrict
  apply ENat.natCast_inj.mp
  exact (flatJacobianOrder_eq_actualRelativeJacobianCoefficient hπ₀ hE₀ (g₀ z) hz₀ Φ₀).symm.trans
    (hJ.trans (flatJacobianOrder_eq_actualRelativeJacobianCoefficient hπ₁ hE₁ (g₁ z) hz₁ Φ₁))

section Represented
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y}

/-- ONE PLUS the genuinely produced exact relative-Jacobian coefficient, not a chosen local upper bound. -/
def representedLogDiscrepancy (hπ : IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) : ℕ :=
  actualRelativeJacobianCoefficient hπ hE + 1

/-- Positivity is produced from the actual natural coefficient. -/
theorem representedLogDiscrepancy_pos (hπ : IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m) : 0 < representedLogDiscrepancy hπ hE :=
  Nat.succ_pos _

/-- The actual strict-margin factorization exponent plus one is the local original order plus exact represented discrepancy. -/
theorem weightedTest_order_add_one_eq_localOrder_add_logDiscrepancy
    (hπ : IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    {y : Y} (Φ : DivisorFlattening (m := m) E y) (f : X → ℂ)
    (hf : HolomorphicAt (m + 1) f (π y)) (a : Fin (m + 1) → ℕ)
    (H : ComplexModel (m + 1) → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ H z)
    (hfactor : (fun z => f ((complexChartAt (n := m + 1) (π y)).val.symm (flatCoordMap π Φ z)) *
      DivisorialChangeOfVariables.complexJacobian (flatCoordMap π Φ) z) =ᶠ[𝓝 0]
        (fun z => H z * ∏ j, z j ^ a j))
    (hnot : ¬HolGerm.mk (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate (Fin.last m)) ∣ HolGerm.mk H hH) :
    (a (Fin.last m) : ℕ∞) + 1 = pullbackNormalOrder hπ Φ f hf +
      (representedLogDiscrepancy hπ hE : ℕ∞) := by
  have hy : y ∈ E := (IdealPowerNormalOrder.regularAtDim_of_divisorFlattening Φ).2.1
  have horder := weightedTest_order_eq_factorization hπ Φ f hf a H hH hfactor hnot
  rw [flatJacobianOrder_eq_actualRelativeJacobianCoefficient hπ hE y hy Φ] at horder
  rw [horder, representedLogDiscrepancy, ENat.natCast_add, ENat.natCast_one]
  exact add_assoc _ _ _
end Represented

/-- The exact represented log discrepancies agree for every original literal common-resolution witness. -/
theorem representedLogDiscrepancy_eq_of_common_resolution {m : ℕ} {X Y₀ Y₁ Z : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel (m + 1)) Y₀] [IsComplexManifold (m + 1) Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel (m + 1)) Y₁] [IsComplexManifold (m + 1) Y₁]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]
    {π₀ : Y₀ → X} {π₁ : Y₁ → X} {g₀ : Z → Y₀} {g₁ : Z → Y₁}
    (hπ₀ : IsAnalyticModification (n := m + 1) π₀)
    (hπ₁ : IsAnalyticModification (n := m + 1) π₁)
    (hg₀ : IsAnalyticModification (n := m + 1) g₀)
    (hg₁ : IsAnalyticModification (n := m + 1) g₁)
    (hcomm : π₀ ∘ g₀ = π₁ ∘ g₁)
    {E₀ : Set Y₀} {E₁ : Set Y₁}
    (hE₀ : IsClosedConnectedSubmanifold (m + 1) E₀ m)
    (hE₁ : IsClosedConnectedSubmanifold (m + 1) E₁ m)
    (hstrict : strictTransform (m + 1) g₀ E₀ = strictTransform (m + 1) g₁ E₁) :
    representedLogDiscrepancy hπ₀ hE₀ = representedLogDiscrepancy hπ₁ hE₁ := by
  unfold representedLogDiscrepancy
  rw [actualRelativeJacobianCoefficient_eq_of_common_resolution hπ₀ hπ₁ hg₀ hg₁ hcomm hE₀ hE₁ hstrict]

end SGPT.Foundations.Analysis.Pending.IntrinsicJacobianCoefficient
