import SGPT.PSH.GroupedGeometricQDivisor

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- The original canonical prime retains its genuine reduced ideal-image
Cartier transform, including all singular and exceptional points. -/
def geometricPrimeCarrierTotalTransform (P : GeometricPrimeCarrier (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    EffectiveDivisor (m + 1) Y :=
  primeTotalTransform P.subvariety
    (by have h := P.subvariety_codimension; omega) hπ

theorem geometricPrimeCarrierTotalTransform_support (P : GeometricPrimeCarrier (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    (geometricPrimeCarrierTotalTransform P hπ).support = π ⁻¹' P.val := by
  rw [geometricPrimeCarrierTotalTransform, primeTotalTransform_support, P.subvariety_carrier]

/-- ALL original positive prime indices and ALL actual components of their
literal transforms; no component list or coefficients are an input. -/
def GeometricPrimeTransformIndex (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :=
  (P : {P // 0 < D.coefficient P}) ×
    GlobalComponents.globalComponents (n := m + 1)
      (geometricPrimeCarrierTotalTransform P.val hπ).support

/-- The actual transformed Cartier component is indexed by its SAME literal carrier. -/
def geometricPrimeTransformCarrier (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (t : GeometricPrimeTransformIndex D hπ) : GeometricPrimeCarrier (m + 1) Y :=
  let Δ := geometricPrimeCarrierTotalTransform t.1.val hπ
  ⟨(cartierPrimeComponent Δ t.2).carrier,
    cartierPrimeComponent Δ t.2, rfl, by rw [cartierPrimeComponent_dim]⟩

/-- The original rational coefficient times the actual positive original
integer order of the SAME transformed Cartier prime. -/
def geometricPrimeTransformContribution (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (t : GeometricPrimeTransformIndex D hπ) : ℚ :=
  D.coefficient t.1.val *
    (regularComponentOrder (geometricPrimeCarrierTotalTransform t.1.val hπ)
      (geometricPrimeCarrierTotalTransform t.1.val hπ).support t.2 : ℚ)

theorem geometricPrimeTransformContribution_pos (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (t : GeometricPrimeTransformIndex D hπ) :
    0 < geometricPrimeTransformContribution D hπ t := by
  apply mul_pos t.1.property
  exact_mod_cast regularComponentOrder_pos (geometricPrimeCarrierTotalTransform t.1.val hπ) t.2

/-- Original local finiteness, actual holomorphic continuity, and the existing
Cartier component producer internally make the ENTIRE raw family locally finite. -/
theorem locallyFinite_geometricPrimeTransformCarriers (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    LocallyFinite (fun t : GeometricPrimeTransformIndex D hπ =>
      (geometricPrimeTransformCarrier D hπ t).val) := by
  have houter : LocallyFinite (fun P : {P // 0 < D.coefficient P} => π ⁻¹' P.val.val) :=
    D.locallyFinite_positive.preimage_continuous hπ.1.continuous
  apply locallyFinite_sigma_of_subordinate
    (fun P : {P // 0 < D.coefficient P} => π ⁻¹' P.val.val)
    (fun P B => (cartierPrimeComponent (geometricPrimeCarrierTotalTransform P.val hπ) B).carrier)
    houter (fun P => locallyFinite_cartierPrimeComponents
      (geometricPrimeCarrierTotalTransform P.val hπ))
  intro P B y hy
  rw [cartierPrimeComponent_carrier] at hy
  have hyΔ := GlobalComponents.subset_of_mem_globalComponents
    (cartierSupport_isComplexAnalytic (geometricPrimeCarrierTotalTransform P.val hπ)) B.property hy
  rwa [geometricPrimeCarrierTotalTransform_support] at hyΔ

/-- The ORIGINAL geometric rational divisor and actual modification internally
produce the global geometric pullback by grouping every SAME-carrier contribution. -/
def geometricQDivisorModificationPullback (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    EffectiveGeometricQDivisor (m + 1) Y :=
  geometricQDivisorOfLocallyFiniteFamily (geometricPrimeTransformCarrier D hπ)
    (geometricPrimeTransformContribution D hπ) (geometricPrimeTransformContribution_pos D hπ)
    (locallyFinite_geometricPrimeTransformCarriers D hπ)

/-- The SAME original reduced vanishing ideal is pulled by the literal
ideal-image operation, rather than inferred from the support equality. -/
theorem geometricPrimeCarrierTotalTransform_ideal (P : GeometricPrimeCarrier (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    (geometricPrimeCarrierTotalTransform P hπ).ideal =
      GermIdeal.pullback (m := m + 1) π (vanishingIdeal (n := m + 1) P.val) := by
  change GermIdeal.pullback (m := m + 1) π
    (vanishingIdeal (n := m + 1) P.subvariety.carrier) = _
  rw [P.subvariety_carrier]

/-- Every global coefficient is the literal finite sum of ALL original
rational weights times the genuine Cartier orders on this SAME actual carrier. -/
theorem geometricQDivisorModificationPullback_coefficient
    (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (A : GeometricPrimeCarrier (m + 1) Y) :
    (geometricQDivisorModificationPullback D hπ).coefficient A =
      ∑ t ∈ (geometricPrimeCarrier_fiber_finite (geometricPrimeTransformCarrier D hπ)
        (locallyFinite_geometricPrimeTransformCarriers D hπ) A).toFinset,
          D.coefficient t.1.val *
            (regularComponentOrder (geometricPrimeCarrierTotalTransform t.1.val hπ)
              (geometricPrimeCarrierTotalTransform t.1.val hπ).support t.2 : ℚ) := rfl

/-- ALL actual transformed components preserve exactly the literal original
support preimage, including singular and exceptional points. -/
theorem geometricQDivisorModificationPullback_support
    (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π) :
    (geometricQDivisorModificationPullback D hπ).support = π ⁻¹' D.support := by
  rw [geometricQDivisorModificationPullback, geometricQDivisorOfLocallyFiniteFamily_support]
  ext y
  constructor
  · intro hy
    obtain ⟨t, hyt⟩ := mem_iUnion.mp hy
    change y ∈ (cartierPrimeComponent (geometricPrimeCarrierTotalTransform t.1.val hπ) t.2).carrier at hyt
    rw [cartierPrimeComponent_carrier] at hyt
    have hyΔ := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (geometricPrimeCarrierTotalTransform t.1.val hπ)) t.2.property hyt
    rw [geometricPrimeCarrierTotalTransform_support] at hyΔ
    exact (D.mem_support (π y)).mpr ⟨t.1.val, t.1.property, hyΔ⟩
  · intro hy
    obtain ⟨P, hP, hyP⟩ := (D.mem_support (π y)).mp hy
    let PP : {P // 0 < D.coefficient P} := ⟨P, hP⟩
    have hyΔ : y ∈ (geometricPrimeCarrierTotalTransform P hπ).support := by
      rw [geometricPrimeCarrierTotalTransform_support]
      exact hyP
    have hyunion : y ∈ ⋃ B, (cartierPrimeComponent
        (geometricPrimeCarrierTotalTransform P hπ) B).carrier :=
      (cartierPrimeComponents_cover (geometricPrimeCarrierTotalTransform P hπ)).symm ▸ hyΔ
    obtain ⟨B, hyB⟩ := mem_iUnion.mp hyunion
    exact mem_iUnion.mpr ⟨⟨PP, B⟩, hyB⟩

end SGPT.PSH
