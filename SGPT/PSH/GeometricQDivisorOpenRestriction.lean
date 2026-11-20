import SGPT.PSH.ReducedCartierComponents

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- ALL original positive primes and ALL actual components of their genuine
reduced open restrictions; no splitting or irreducibility certificate is supplied. -/
def GeometricPrimeRestrictionIndex (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M) :=
  (P : {P // 0 < D.coefficient P}) × GlobalComponents.globalComponents (n := m + 1)
    (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U).support

def geometricPrimeRestrictionCarrier (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M)
    (t : GeometricPrimeRestrictionIndex D U) : GeometricPrimeCarrier (m + 1) U :=
  cartierComponentGeometricPrime (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor t.1.val) U) t.2

/-- The original rational coefficient times the actual restricted component order. -/
def geometricPrimeRestrictionContribution (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M)
    (t : GeometricPrimeRestrictionIndex D U) : ℚ :=
  D.coefficient t.1.val *
    (regularComponentOrder (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor t.1.val) U)
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor t.1.val) U).support t.2 : ℚ)

theorem geometricPrimeRestrictionContribution_eq (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M)
    (t : GeometricPrimeRestrictionIndex D U) :
    geometricPrimeRestrictionContribution D U t = D.coefficient t.1.val := by
  rw [geometricPrimeRestrictionContribution, geometricPrimeOpenRestriction_component_order_one,
    Nat.cast_one, mul_one]

theorem geometricPrimeRestrictionContribution_pos (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M)
    (t : GeometricPrimeRestrictionIndex D U) : 0 < geometricPrimeRestrictionContribution D U t := by
  rw [geometricPrimeRestrictionContribution_eq]
  exact t.1.property

/-- Actual original local finiteness and subordinate Cartier component families
give local finiteness of the ENTIRE dependent restricted family. -/
theorem locallyFinite_geometricPrimeRestrictionCarriers
    (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M) :
    LocallyFinite (fun t : GeometricPrimeRestrictionIndex D U =>
      (geometricPrimeRestrictionCarrier D U t).val) := by
  have houter : LocallyFinite (fun P : {P // 0 < D.coefficient P} =>
      (Subtype.val : U → M) ⁻¹' P.val.val) :=
    D.locallyFinite_positive.preimage_continuous continuous_subtype_val
  change LocallyFinite (fun t : GeometricPrimeRestrictionIndex D U => t.2.val)
  apply locallyFinite_sigma_of_subordinate
    (fun P : {P // 0 < D.coefficient P} => (Subtype.val : U → M) ⁻¹' P.val.val)
    (fun P (B : GlobalComponents.globalComponents (n := m + 1)
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U).support) => B.val)
    houter (fun P => by simpa only [cartierPrimeComponent_carrier] using
      locallyFinite_cartierPrimeComponents (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U))
  intro P B y hy
  have hyD := GlobalComponents.subset_of_mem_globalComponents
    (cartierSupport_isComplexAnalytic (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P.val) U))
    B.property hy
  rwa [cartierOpenRestriction_support, geometricPrimeCarrierEffectiveDivisor_support] at hyD

/-- ORIGINAL D,U alone produce the genuine locally finite geometric rational
restriction by grouping every actual restricted prime and its original order. -/
def geometricQDivisorOpenRestriction (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M) :
    EffectiveGeometricQDivisor (m + 1) U :=
  geometricQDivisorOfLocallyFiniteFamily (geometricPrimeRestrictionCarrier D U)
    (geometricPrimeRestrictionContribution D U) (geometricPrimeRestrictionContribution_pos D U)
    (locallyFinite_geometricPrimeRestrictionCarriers D U)

/-- EVERY genuine split component has actual order one, so every grouped
coefficient is the finite sum of exactly the original rational contributions. -/
theorem geometricQDivisorOpenRestriction_coefficient
    (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M)
    (A : GeometricPrimeCarrier (m + 1) U) :
    (geometricQDivisorOpenRestriction D U).coefficient A =
      ∑ t ∈ (geometricPrimeCarrier_fiber_finite (geometricPrimeRestrictionCarrier D U)
        (locallyFinite_geometricPrimeRestrictionCarriers D U) A).toFinset,
          D.coefficient t.1.val := by
  rw [geometricQDivisorOpenRestriction, geometricQDivisorOfLocallyFiniteFamily_coefficient]
  exact Finset.sum_congr rfl (fun t _ => geometricPrimeRestrictionContribution_eq D U t)

/-- Literal full original support preimage, including every singular point
and every empty or split open restriction. -/
theorem geometricQDivisorOpenRestriction_support
    (D : EffectiveGeometricQDivisor (m + 1) M) (U : Opens M) :
    (geometricQDivisorOpenRestriction D U).support =
      (Subtype.val : U → M) ⁻¹' D.support := by
  rw [geometricQDivisorOpenRestriction, geometricQDivisorOfLocallyFiniteFamily_support]
  ext y
  constructor
  · intro hy
    obtain ⟨t, hyt⟩ := mem_iUnion.mp hy
    change y ∈ t.2.val at hyt
    have hyD := GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor t.1.val) U))
      t.2.property hyt
    rw [cartierOpenRestriction_support, geometricPrimeCarrierEffectiveDivisor_support] at hyD
    exact (D.mem_support (y : M)).mpr ⟨t.1.val, t.1.property, hyD⟩
  · intro hy
    obtain ⟨P, hP, hyP⟩ := (D.mem_support (y : M)).mp hy
    let PP : {P // 0 < D.coefficient P} := ⟨P, hP⟩
    let E := cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U
    have hyE : y ∈ E.support := by
      change y ∈ (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U).support
      rwa [cartierOpenRestriction_support, geometricPrimeCarrierEffectiveDivisor_support]
    have hyunion : y ∈ ⋃ B, (cartierPrimeComponent E B).carrier := (cartierPrimeComponents_cover E).symm ▸ hyE
    obtain ⟨B, hyB⟩ := mem_iUnion.mp hyunion
    rw [cartierPrimeComponent_carrier] at hyB
    exact mem_iUnion.mpr ⟨⟨PP, B⟩, hyB⟩

end SGPT.PSH
