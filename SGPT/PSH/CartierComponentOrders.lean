import SGPT.PSH.CartierRegularMultiplicity
import SGPT.Foundations.Analysis.Pending.GlobalComponents

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending DivisorExponent RegularLocusComponent
open scoped Topology Manifold ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Equality of the actual closed component carriers identifies the integer
orders produced from any of their original regular base points. -/
theorem cartierOrder_eq_of_regularComponent_closure_eq (D : EffectiveDivisor n M)
    {A : Set M} {c d : M} {k l : ℕ}
    (hc : RegularAtDim (n := n) A c k) (hd : RegularAtDim (n := n) A d l)
    (heq : closure (component (n := n) A c) = closure (component (n := n) A d)) :
    divExp n D.ideal A c = divExp n D.ideal A d := by
  have hdc : d ∈ closure (component (n := n) A c) :=
    heq.symm ▸ subset_closure (mem_component_self hd)
  have hlocal := eventually_divExp_eq
    (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hd
    (Eventually.of_forall fun y => HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible y)
  obtain ⟨U, hUsub, hU, hdU⟩ := _root_.mem_nhds_iff.mp hlocal
  obtain ⟨z, hzU, hzC⟩ := _root_.mem_closure_iff.mp hdc U hU hdU
  exact (cartierOrder_eq_on_regularComponent D hc hzC).symm.trans
    (hUsub hzU (component_subset A c hzC))

/-- The coefficient is chosen from an actual regular base point of the
literal global component, rather than stored as an assumed order. -/
def regularComponentOrder (D : EffectiveDivisor n M) (A : Set M)
    (B : GlobalComponents.globalComponents (n := n) A) : ℕ :=
  divExp n D.ideal A (Classical.choose B.property)

/-- The same internally defined coefficient is read by every original
regular point whose actual component closure is the same closed carrier. -/
theorem regularComponentOrder_eq (D : EffectiveDivisor n M) (A : Set M)
    (B : GlobalComponents.globalComponents (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k)
    (hB : (B : Set M) = closure (component (n := n) A c)) :
    regularComponentOrder D A B = divExp n D.ideal A c := by
  change divExp n D.ideal A (Classical.choose B.property) = _
  obtain ⟨l, hd⟩ := (Classical.choose_spec B.property).1
  exact cartierOrder_eq_of_regularComponent_closure_eq D hd hc
    ((Classical.choose_spec B.property).2.symm.trans hB)

/-- Every finite original divisibility reader uses the SAME produced
integer on the SAME literal global component carrier. -/
theorem regularComponentOrder_divisibility (D : EffectiveDivisor n M) (A : Set M)
    (B : GlobalComponents.globalComponents (n := n) A) {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k)
    (hB : (B : Set M) = closure (component (n := n) A c))
    {y : M} (hy : y ∈ component (n := n) A c) (r : ℕ) :
    IsDivNear n D.ideal A r y ↔ r ≤ regularComponentOrder D A B := by
  obtain ⟨a, ha, hdiv⟩ := exists_cartierOrder_on_regularComponent D hc
  have hcoef : a = regularComponentOrder D A B :=
    ha.trans (regularComponentOrder_eq D A B hc hB).symm
  simpa only [hcoef] using hdiv y hy r

section Prime

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- The actual pulled reduced ideal has the literal preimage support,
including exceptional points over singular original prime points. -/
theorem primeTotalTransform_support
    (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    (primeTotalTransform P hdim hπ).support = π ⁻¹' P.carrier := by
  change (GermIdeal.pullback (m := m + 1) π
    (ActualCodimensionOneDivisorCurrent.effectiveDivisor P hdim).ideal).zeroLocus = _
  rw [BlowupExceptionalDivisor.zeroLocus_pullback hπ.1
    (DivisorMetric.isCoherent_of_isInvertible
      (ActualCodimensionOneDivisorCurrent.effectiveDivisor P hdim).isInvertible)]
  exact congrArg (fun S : Set X => π ⁻¹' S)
    (ActualCodimensionOneDivisorCurrent.support_effectiveDivisor P hdim)

/-- Actual global carrier coefficients of the literal total transform are
internally produced by its own ideal orders. -/
def primeTransformComponentOrder
    (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (B : GlobalComponents.globalComponents (n := m + 1) (primeTotalTransform P hdim hπ).support) : ℕ :=
  regularComponentOrder (primeTotalTransform P hdim hπ) (primeTotalTransform P hdim hπ).support B

/-- All actual regular-base-point readers on a fixed closed carrier use the
same coefficient of the same literal total transform, with no supplied order. -/
theorem primeTransformComponentOrder_divisibility
    (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (B : GlobalComponents.globalComponents (n := m + 1) (primeTotalTransform P hdim hπ).support)
    {c : Y} {k : ℕ}
    (hc : RegularAtDim (n := m + 1) (primeTotalTransform P hdim hπ).support c k)
    (hB : (B : Set Y) = closure (component (n := m + 1) (primeTotalTransform P hdim hπ).support c))
    {y : Y} (hy : y ∈ component (n := m + 1) (primeTotalTransform P hdim hπ).support c) (r : ℕ) :
    IsDivNear (m + 1) (primeTotalTransform P hdim hπ).ideal
      (primeTotalTransform P hdim hπ).support r y ↔ r ≤ primeTransformComponentOrder P hdim hπ B :=
  regularComponentOrder_divisibility (primeTotalTransform P hdim hπ)
    (primeTotalTransform P hdim hπ).support B hc hB hy r

end Prime
end SGPT.PSH
