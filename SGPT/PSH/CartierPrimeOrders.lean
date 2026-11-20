import SGPT.PSH.CartierPrimeComponents

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

/-- Local equality of the actual carriers identifies their finite integer
orders for the same actual divisor ideal. -/
theorem cartierOrder_eq_of_carrier_eventuallyEq (D : EffectiveDivisor n M)
    {H K : Set M} {x : M} (hxH : x ∈ H) (hxK : x ∈ K)
    (hHK : ∀ᶠ z in 𝓝 x, z ∈ H ↔ z ∈ K) :
    divExp n D.ideal H x = divExp n D.ideal K x := by
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  have hdiv (r : ℕ) : IsDivNear n D.ideal H r x ↔ IsDivNear n D.ideal K r x := by
    constructor
    · intro h
      filter_upwards [h, hHK] with z hz heq hzK
      exact hz (heq.mpr hzK)
    · intro h
      filter_upwards [h, hHK] with z hz heq hzH
      exact hz (heq.mp hzH)
  have hne := HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible x
  apply Nat.le_antisymm
  · exact (isDivNear_iff_le_divExp hhol hxK hne).mp
      ((hdiv _).mp (isDivNear_divExp hhol x))
  · exact (isDivNear_iff_le_divExp hhol hxH hne).mp
      ((hdiv _).mpr (isDivNear_divExp hhol x))

/-- Order-one cosupport is the literal divisor support, so each actual
support point has a positive finite order with no positivity certificate. -/
theorem cartierOrder_pos_of_mem_support (D : EffectiveDivisor n M)
    {x : M} (hx : x ∈ D.support) : 0 < divExp n D.ideal D.support x := by
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  have hdiv : IsDivNear n D.ideal D.support 1 x := by
    refine Eventually.of_forall fun z hz => ?_
    rw [GermIdealOrder.cosupport_one hhol]
    exact ⟨mem_univ z, hz⟩
  exact lt_of_lt_of_le Nat.zero_lt_one
    ((isDivNear_iff_le_divExp hhol hx
      (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible x)).mp hdiv)

/-- Every coefficient chosen from the actual support component is positive;
the integer is internally defined by the original divisor order. -/
theorem regularComponentOrder_pos (D : EffectiveDivisor n M)
    (B : GlobalComponents.globalComponents (n := n) D.support) :
    0 < regularComponentOrder D D.support B := by
  change 0 < divExp n D.ideal D.support (Classical.choose B.property)
  obtain ⟨k, hk⟩ := (Classical.choose_spec B.property).1
  exact cartierOrder_pos_of_mem_support D hk.2.1

section Prime

variable {m : ℕ} {Z : Type u} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel (m + 1)) Z] [IsComplexManifold (m + 1) Z]

/-- The produced coefficient reads the order along the ACTUAL geometric
prime, rather than only the union support, on every original regular component. -/
theorem cartierPrimeComponent_order_eq (D : EffectiveDivisor (m + 1) Z)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) {c : Z} {k : ℕ}
    (hc : RegularAtDim (n := m + 1) D.support c k)
    (hB : (B : Set Z) = closure (component (n := m + 1) D.support c))
    {y : Z} (hy : y ∈ component (n := m + 1) D.support c) :
    divExp (m + 1) D.ideal (cartierPrimeComponent D B).carrier y =
      regularComponentOrder D D.support B := by
  obtain ⟨W, hW, hyW, hWC, _, _⟩ :=
    exists_isOpen_inter_subset hy (regularAtDim_of_mem_component hc hy)
  have hsub : (B : Set Z) ⊆ D.support :=
    GlobalComponents.subset_of_mem_globalComponents (cartierSupport_isComplexAnalytic D) B.property
  have hyB : y ∈ (B : Set Z) := by
    rw [hB]
    exact subset_closure hy
  have hlocal : ∀ᶠ z in 𝓝 y, z ∈ (B : Set Z) ↔ z ∈ D.support := by
    filter_upwards [hW.mem_nhds hyW] with z hzW
    refine ⟨fun hzB => hsub hzB, fun hzD => ?_⟩
    rw [hB]
    exact subset_closure (hWC ⟨hzD, hzW⟩)
  rw [cartierPrimeComponent_carrier]
  exact (cartierOrder_eq_of_carrier_eventuallyEq D hyB
    (component_subset D.support c hy) hlocal).trans
      ((cartierOrder_eq_on_regularComponent D hc hy).trans
        (regularComponentOrder_eq D D.support B hc hB).symm)

/-- Every finite divisibility test along the SAME actual geometric prime
uses the same positive integer of the SAME original divisor ideal. -/
theorem cartierPrimeComponent_divisibility (D : EffectiveDivisor (m + 1) Z)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) {c : Z} {k : ℕ}
    (hc : RegularAtDim (n := m + 1) D.support c k)
    (hB : (B : Set Z) = closure (component (n := m + 1) D.support c))
    {y : Z} (hy : y ∈ component (n := m + 1) D.support c) (r : ℕ) :
    IsDivNear (m + 1) D.ideal (cartierPrimeComponent D B).carrier r y ↔
      r ≤ regularComponentOrder D D.support B := by
  have hhol : ∀ x g, D.ideal.mem x g → HolomorphicAt (m + 1) g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      (DivisorMetric.isCoherent_of_isInvertible D.isInvertible) hg
  have hyP : y ∈ (cartierPrimeComponent D B).carrier := by
    rw [cartierPrimeComponent_carrier, hB]
    exact subset_closure hy
  rw [isDivNear_iff_le_divExp hhol hyP
    (HironakaDivisorPowers.isNonzeroAt_of_isInvertible D.isInvertible y),
    cartierPrimeComponent_order_eq D B hc hB hy]

/-- The internally constructed geometric primes cover the entire literal
support, including every singular support point. -/
theorem cartierPrimeComponents_cover (D : EffectiveDivisor (m + 1) Z) :
    (⋃ B : GlobalComponents.globalComponents (n := m + 1) D.support,
      (cartierPrimeComponent D B).carrier) = D.support := by
  ext x
  constructor
  · intro hx
    obtain ⟨B, hxB⟩ := mem_iUnion.mp hx
    rw [cartierPrimeComponent_carrier] at hxB
    exact GlobalComponents.subset_of_mem_globalComponents
      (cartierSupport_isComplexAnalytic D) B.property hxB
  · intro hx
    obtain ⟨B, hB, hxB⟩ := mem_sUnion.mp
      ((GlobalComponents.sUnion_globalComponents (cartierSupport_isComplexAnalytic D)).symm ▸ hx)
    exact mem_iUnion.mpr ⟨⟨B, hB⟩, by simpa only [cartierPrimeComponent_carrier] using hxB⟩

end Prime

section Modification

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- The SAME literal total transform of a possibly singular original prime
has internally positive component coefficients, including exceptional primes. -/
theorem primeTransformComponentOrder_pos
    (P : ClosedIrreducibleAnalyticSubvariety (m + 1) X) (hdim : P.dim = m) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (B : GlobalComponents.globalComponents (n := m + 1) (primeTotalTransform P hdim hπ).support) :
    0 < primeTransformComponentOrder P hdim hπ B :=
  regularComponentOrder_pos (primeTotalTransform P hdim hπ) B

end Modification
end SGPT.PSH
