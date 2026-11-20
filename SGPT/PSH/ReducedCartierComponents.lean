import SGPT.PSH.CartierOpenRestriction

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending DivisorExponent RegularLocusComponent
open scoped Topology Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- FULL local ideal membership preserves actual finite Cartier orders.
Both nonzero original stalks are supplied internally by invertibility. -/
theorem cartierOrder_eq_of_ideal_eventuallyEq (D E : EffectiveDivisor n M)
    {A : Set M} {x : M} (hx : x ∈ A)
    (hI : ∀ᶠ y in 𝓝 x, ∀ g, D.ideal.mem y g ↔ E.ideal.mem y g) :
    divExp n D.ideal A x = divExp n E.ideal A x := by
  have hD : ∀ y g, D.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem D.isInvertible hg
  have hE : ∀ y g, E.ideal.mem y g → HolomorphicAt n g y :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem E.isInvertible hg
  have hdiv (r : ℕ) : IsDivNear n D.ideal A r x ↔ IsDivNear n E.ideal A r x := by
    constructor
    · intro h
      filter_upwards [h, hI] with y hy heq hyA
      exact ⟨(hy hyA).1, fun g hg => (hy hyA).2 g ((heq g).mpr hg)⟩
    · intro h
      filter_upwards [h, hI] with y hy heq hyA
      exact ⟨(hy hyA).1, fun g hg => (hy hyA).2 g ((heq g).mp hg)⟩
  apply Nat.le_antisymm
  · exact (isDivNear_iff_le_divExp hE hx
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible E.isInvertible x)).mp
        ((hdiv _).mp (isDivNear_divExp hD x))
  · exact (isDivNear_iff_le_divExp hD hx
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible x)).mp
        ((hdiv _).mpr (isDivNear_divExp hE x))

section Reduced
variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- EVERY actual component of an original reduced Cartier ideal has genuine
order one, by existing reduced-prime geometry and full local ideal equality. -/
theorem reduced_cartier_regularComponentOrder_one (D : EffectiveDivisor (m + 1) X)
    (hred : D.ideal = vanishingIdeal (n := m + 1) D.support)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    regularComponentOrder D D.support B = 1 := by
  obtain ⟨c, ⟨k, hc⟩, hB⟩ := B.property
  have hk := cartierSupport_regular_dimension D hc
  subst k
  let P := cartierComponentGeometricPrime D B
  have hcP : RegularAtDim (n := m + 1) P.val c m := by
    change RegularAtDim (n := m + 1) B.val c m
    rw [hB]
    exact regularAtDim_closure_component hc (mem_component_self hc)
  obtain ⟨W, hW, hcW, hWC, _hregW, _hclW⟩ :=
    exists_isOpen_inter_subset (mem_component_self hc) hc
  have hlocal : ∀ᶠ z in 𝓝 c, z ∈ P.val ↔ z ∈ D.support := by
    filter_upwards [hW.mem_nhds hcW] with z hzW
    constructor
    · intro hzP
      change z ∈ B.val at hzP
      exact GlobalComponents.subset_of_mem_globalComponents (cartierSupport_isComplexAnalytic D) B.property hzP
    · intro hzD
      change z ∈ B.val
      rw [hB]
      exact subset_closure (hWC ⟨hzD, hzW⟩)
  have hI : ∀ᶠ y in 𝓝 c, ∀ g, D.ideal.mem y g ↔
      (geometricPrimeCarrierEffectiveDivisor P).ideal.mem y g := by
    filter_upwards [hlocal.eventually_nhds] with y hy g
    rw [hred, geometricPrimeCarrierEffectiveDivisor_ideal]
    constructor
    · rintro ⟨hg, hvan⟩
      refine ⟨hg, ?_⟩
      filter_upwards [hvan, hy] with z hz heq hzP
      exact hz (heq.mp hzP)
    · rintro ⟨hg, hvan⟩
      refine ⟨hg, ?_⟩
      filter_upwards [hvan, hy] with z hz heq hzD
      exact hz (heq.mpr hzD)
  rw [regularComponentOrder_eq D D.support B hc hB]
  calc
    _ = divExp (m + 1) D.ideal P.val c :=
      cartierOrder_eq_of_carrier_eventuallyEq D hc.2.1 hcP.2.1 (hlocal.mono fun _ hz => hz.symm)
    _ = divExp (m + 1) (geometricPrimeCarrierEffectiveDivisor P).ideal P.val c :=
      cartierOrder_eq_of_ideal_eventuallyEq D (geometricPrimeCarrierEffectiveDivisor P) hcP.2.1 hI
    _ = 1 := geometricPrimeCarrier_order_one_at_regular P hcP

/-- ORIGINAL P,U and any actual internally constructed restricted component
retain coefficient one, even when the original prime splits on U. -/
theorem geometricPrimeOpenRestriction_component_order_one
    (P : GeometricPrimeCarrier (m + 1) X) (U : TopologicalSpace.Opens X)
    (B : GlobalComponents.globalComponents (n := m + 1)
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U).support) :
    regularComponentOrder (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U)
      (cartierOpenRestriction (geometricPrimeCarrierEffectiveDivisor P) U).support B = 1 := by
  apply reduced_cartier_regularComponentOrder_one
  rw [geometricPrimeOpenRestriction_ideal, cartierOpenRestriction_support,
    geometricPrimeCarrierEffectiveDivisor_support]

end Reduced
end SGPT.PSH
