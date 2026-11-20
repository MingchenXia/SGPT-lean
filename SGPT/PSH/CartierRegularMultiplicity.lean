import SGPT.Foundations.Analysis.Pending.HironakaDivisorPowers
import SGPT.Foundations.Analysis.Pending.RegularLocusComponent
import SGPT.Foundations.Analysis.Pending.ActualCodimensionOneDivisorCurrent
import SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
import SGPT.Foundations.Analysis.Pending.GermIdealTotalTransform
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open DivisorExponent HironakaDivisorPowers RegularLocusComponent
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal integer order of an actual invertible divisor ideal is
locally constant on an actual regular stratum, even for a singular carrier. -/
theorem isLocallyConstant_cartierOrder_regularLocus (D : EffectiveDivisor n M)
    (A : Set M) (k : ℕ) :
    IsLocallyConstant (fun x : regularLocus (n := n) A k =>
      divExp n D.ideal A (x : M)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hlocal := eventually_divExp_eq
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) x.property
    (Eventually.of_forall fun y => isNonzeroAt_of_isInvertible D.isInvertible y)
  have hincl : Tendsto (Subtype.val : regularLocus (n := n) A k → M)
      (𝓝 x) (𝓝 (x : M)) := continuous_subtype_val.continuousAt.tendsto
  filter_upwards [hincl.eventually hlocal] with y hy
  exact hy y.property.2.1

/-- The actual connected regular component retains one integer order of
the same original divisor ideal; the carrier need not be globally smooth. -/
theorem cartierOrder_eq_on_regularComponent (D : EffectiveDivisor n M)
    {A : Set M} {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k)
    {y : M} (hy : y ∈ component (n := n) A c) :
    divExp n D.ideal A y = divExp n D.ideal A c := by
  let C := component (n := n) A c
  let ι : C → regularLocus (n := n) A k := fun z =>
    ⟨z, regularAtDim_of_mem_component hc z.property⟩
  have hi : Continuous ι := continuous_subtype_val.subtype_mk _
  have hloc := (isLocallyConstant_cartierOrder_regularLocus D A k).comp_continuous hi
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp
    isPreconnected_connectedComponentIn
  exact hloc.apply_eq_of_preconnectedSpace (⟨y, hy⟩ : C) (⟨c, mem_component_self hc⟩ : C)

/-- An actual component internally supplies the integer and every finite
divisibility equivalence of the same literal divisor ideal. -/
theorem exists_cartierOrder_on_regularComponent (D : EffectiveDivisor n M)
    {A : Set M} {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k) :
    ∃ a : ℕ, a = divExp n D.ideal A c ∧
      ∀ y ∈ component (n := n) A c, ∀ r : ℕ,
        IsDivNear n D.ideal A r y ↔ r ≤ a := by
  refine ⟨divExp n D.ideal A c, rfl, fun y hy r => ?_⟩
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  exact (isDivNear_iff_le_divExp hhol (component_subset A c hy)
    (isNonzeroAt_of_isInvertible D.isInvertible y)).trans
      (by rw [cartierOrder_eq_on_regularComponent D hc hy])

section Modification

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The actual inverse geometry, rather than a caller Jacobian condition,
supplies thinness of the differential exceptional locus. -/
theorem interior_exceptionalLocus_eq_empty_of_native_analyticModification {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    interior (FirstPass.BlowupSequences.exceptionalLocus n π) = ∅ := by
  obtain ⟨A, _, _, hint, _, hnonexc⟩ :=
    AnalyticModificationLocalDiscrepancy.exists_analytic_exceptional_set_of_isAnalyticModification hπ
  have hsub : FirstPass.BlowupSequences.exceptionalLocus n π ⊆ A := by
    intro y hy
    by_contra hyA
    exact hnonexc y hyA hy
  exact subset_empty_iff.mp ((interior_mono hsub).trans_eq hint)

end Modification

section Prime

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- The literal ideal-image total transform of the genuine reduced prime
ideal. Singular points and nonvanishing of composed generators are included. -/
def primeTotalTransform (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X)
    (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    EffectiveDivisor (m + 1) Y :=
  GermIdealTotalTransform.EffectiveDivisor.totalTransform hπ.1
    (interior_exceptionalLocus_eq_empty_of_native_analyticModification hπ)
    (ActualCodimensionOneDivisorCurrent.effectiveDivisor P hdim)

/-- Every actual regular component of the SAME literal total transform of
a singular original geometric prime internally supplies its integer order. -/
theorem exists_prime_totalTransform_regularComponent_order
    (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {c : Y} {k : ℕ}
    (hc : RegularAtDim (n := m + 1) (primeTotalTransform P hdim hπ).support c k) :
    let D := primeTotalTransform P hdim hπ
    ∃ a : ℕ, a = divExp (m + 1) D.ideal D.support c ∧
      ∀ y ∈ component (n := m + 1) D.support c, ∀ r : ℕ,
        IsDivNear (m + 1) D.ideal D.support r y ↔ r ≤ a :=
  exists_cartierOrder_on_regularComponent (primeTotalTransform P hdim hπ) hc

end Prime
end SGPT.PSH
