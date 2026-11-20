import SGPT.PSH.LocalIntegralGeometricQDivisor

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every actual global component of an ORIGINAL prime is that SAME literal
carrier, by the existing irreducible closure-of-regular-component producer. -/
theorem geometricPrimeCarrier_globalComponent_eq (P : GeometricPrimeCarrier n M)
    (B : GlobalComponents.globalComponents (n := n) P.val) : B.val = P.val := by
  obtain ⟨c, ⟨k, hc⟩, hB⟩ := B.property
  have hP : IsComplexAnalyticallyIrreducible (n := n) P.val := by
    rw [← P.subvariety_carrier]
    exact P.subvariety.irreducible_carrier
  exact hB.trans (StrictTransformSubvariety.eq_closure_component hP hc).symm

/-- Actual original prime geometry supplies its original global component;
no component index or connected-regular-locus certificate is an input. -/
theorem geometricPrimeCarrier_mem_globalComponents (P : GeometricPrimeCarrier n M) :
    P.val ∈ GlobalComponents.globalComponents (n := n) P.val := by
  obtain ⟨c, _hcP, hc⟩ := P.subvariety.exists_regular_point
  have hc' : RegularAtDim (n := n) P.val c P.subvariety.dim := by
    rw [← P.subvariety_carrier]
    exact hc
  let B : GlobalComponents.globalComponents (n := n) P.val :=
    ⟨closure (RegularLocusComponent.component (n := n) P.val c),
      GlobalComponents.closure_component_mem_globalComponents hc'⟩
  have hmem : B.val ∈ GlobalComponents.globalComponents (n := n) P.val := B.property
  rwa [geometricPrimeCarrier_globalComponent_eq P B] at hmem

section Cartier
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- The internally produced actual reduced Cartier component has exactly
its original prime carrier as its literal index. -/
def geometricPrimeCarrierComponent (P : GeometricPrimeCarrier (m + 1) X) :
    GlobalComponents.globalComponents (n := m + 1)
      (geometricPrimeCarrierEffectiveDivisor P).support :=
  ⟨P.val, by rw [geometricPrimeCarrierEffectiveDivisor_support]
             exact geometricPrimeCarrier_mem_globalComponents P⟩

/-- The actual component subvariety is the SAME original geometric prime,
including its actual certified codimension-one dimension. -/
theorem geometricPrimeCarrierComponent_subvariety (P : GeometricPrimeCarrier (m + 1) X) :
    cartierPrimeComponent (geometricPrimeCarrierEffectiveDivisor P)
      (geometricPrimeCarrierComponent P) = P.subvariety := by
  apply ClosedIrreducibleAnalyticSubvariety.ext
  · rw [cartierPrimeComponent_carrier]
    exact P.subvariety_carrier.symm
  · rw [cartierPrimeComponent_dim]
    have h := P.subvariety_codimension
    omega

end Cartier
end SGPT.PSH
