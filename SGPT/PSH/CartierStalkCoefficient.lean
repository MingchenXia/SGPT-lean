import SGPT.PSH.CanonicalCartierCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition
open scoped Topology Manifold ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- ORIGINAL P and the PRESCRIBED original x∈P internally produce a
genuine SAME-P chart branch. Reuses the existing reduced equation at x;
the only additional selection is pure UFD factorization of that equation. -/
theorem exists_original_prime_chart_branch_at (P : GeometricPrimeCarrier (m + 1) M)
    (x : M) (hxP : x ∈ P.val) :
    ∃ (q : ComplexModel (m + 1) → ℂ) (hq : OkaRelationSheaf.HolAt q 0),
      Prime (HolGerm.mk q hq) ∧ AnalyticGermDecomposition.vanishingIdeal
        (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
          Ideal.span {HolGerm.mk q hq} := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨r, hr, hR, _hsR, hI, hzero⟩ := exists_reduced_cartierPrimeComponent_equation
    (geometricPrimeCarrierEffectiveDivisor P) (geometricPrimeCarrierComponent P) x
  rw [geometricPrimeCarrierComponent_subvariety, P.subvariety_carrier] at hI hzero
  let e := (complexChartAt (n := m + 1) x).val
  have hxE : x ∈ e.source := mem_complexChartAt_source x
  have h0P : (0 : ComplexModel (m + 1)) ∈
      AnalyticDescendingChain.chartGerm (n := m + 1) P.val x := by
    change 0 + e x ∈ e.target ∧ e.symm (0 + e x) ∈ P.val
    simpa only [zero_add, e.left_inv hxE] using And.intro (e.map_source hxE) hxP
  have hr0 : r 0 = 0 := (Filter.eventuallyEq_set.mp hzero).self_of_nhds.mp h0P
  have hnonunit : ¬IsUnit (HolGerm.mk r hr) := by
    intro hunit
    have hne := (HolGerm.isUnit_iff_eval_ne_zero _).mp hunit
    simp only [HolGerm.eval_mk, hr0, ne_eq, not_true_eq_false] at hne
  obtain ⟨Q, hQ, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hnonunit hR
  obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk Q
  refine ⟨q, hq, hQ.prime, ?_⟩
  rw [hI]
  exact Ideal.span_le.mpr (by rintro _ rfl; exact Ideal.mem_span_singleton.mpr hdiv)

/-- Equality of FULL original Cartier stalks at a PRESCRIBED point of
the SAME actual prime gives its genuine canonical coefficient equality,
including absent-component zero. No regular-point or branch certificate. -/
theorem cartierGeometricPrimeCoefficient_eq_of_stalk_ideal_eq
    (D E : EffectiveDivisor (m + 1) M) (P : GeometricPrimeCarrier (m + 1) M)
    (x : M) (hxP : x ∈ P.val) (hideal : ∀ b, D.ideal.mem x b ↔ E.ideal.mem x b) :
    cartierGeometricPrimeCoefficient D P = cartierGeometricPrimeCoefficient E P := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨q, hq, hQ, hPI⟩ := exists_original_prime_chart_branch_at P x hxP
  obtain ⟨gD, hfD, hFD, hgenD, hzeroD⟩ := exists_cartier_centered_stalk_generator D x
  obtain ⟨gE, hfE, hFE, hgenE, hzeroE⟩ := exists_cartier_centered_stalk_generator E x
  have hEgenD (b : M → ℂ) : D.ideal.mem x b ↔ IsInSpanAt (n := m + 1) (· = gE) x b :=
    (hideal b).trans (hgenE.self_of_nhds.2 b)
  obtain ⟨v, hv, hv0, _hvnear, htrans⟩ := exists_centered_unit_transition_of_cartier_generators
    D x gD gE hgenD.self_of_nhds.1 hgenE.self_of_nhds.1 hgenD.self_of_nhds.2 hEgenD
  let e := (complexChartAt (n := m + 1) x).val
  let center := fun g : M → ℂ => fun z : ComplexModel (m + 1) => g (e.symm (z + e x))
  have hunit : IsUnit (HolGerm.mk v hv) := (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    (by simpa only [HolGerm.eval_mk] using hv0)
  have hproduct : HolGerm.mk (center gD) hfD = HolGerm.mk (center gE) hfE * HolGerm.mk v hv := by
    rw [← HolGerm.mk_mul (center gE) v hfE hv]
    exact HolGerm.mk_eq_mk_iff.mpr htrans
  rw [cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity D P x gD hfD hFD hgenD hzeroD q hq hQ hPI,
    cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity E P x gE hfE hFE hgenE hzeroE q hq hQ hPI]
  change multiplicity (HolGerm.mk q hq) (HolGerm.mk (center gD) hfD) = _
  have hfinite := FiniteMultiplicity.of_prime_left hQ (mul_ne_zero hFE hunit.ne_zero)
  rw [hproduct, multiplicity_mul hQ hfinite, multiplicity_of_isUnit_right hQ.not_isUnit hunit, add_zero]

end SGPT.PSH
