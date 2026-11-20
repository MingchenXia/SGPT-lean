import SGPT.PSH.CanonicalCartierCoefficients

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition HironakaEffectiveDivisorSum
open scoped Topology Manifold ContDiff Classical

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem exists_original_prime_chart_branch (P : GeometricPrimeCarrier (m + 1) M) :
    ∃ (x : M) (q : ComplexModel (m + 1) → ℂ)
      (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z), Prime (HolGerm.mk q hq) ∧
      AnalyticGermDecomposition.vanishingIdeal
        (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
          Ideal.span {HolGerm.mk q hq} := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨x, hxP⟩ := P.nonempty
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
  refine ⟨x, q, hq, hQ.prime, ?_⟩
  rw [hI]
  exact Ideal.span_le.mpr (by rintro _ rfl; exact Ideal.mem_span_singleton.mpr hdiv)

theorem cartierGeometricPrimeCoefficient_zero (P : GeometricPrimeCarrier (m + 1) M) :
    cartierGeometricPrimeCoefficient (0 : EffectiveDivisor (m + 1) M) P = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [cartierGeometricPrimeCoefficient_pos_iff]
  intro hmem
  obtain ⟨x, hxP⟩ := P.nonempty
  have hx0 := GlobalComponents.subset_of_mem_globalComponents
    (cartierSupport_isComplexAnalytic (0 : EffectiveDivisor (m + 1) M)) hmem hxP
  simp only [support_zero, mem_empty_iff_false] at hx0

/-- Actual original divisors and canonical prime ALONE produce coefficient
additivity through genuine whole-ideal products and nonzero germ multiplicities. -/
theorem cartierGeometricPrimeCoefficient_add (D E : EffectiveDivisor (m + 1) M)
    (P : GeometricPrimeCarrier (m + 1) M) :
    cartierGeometricPrimeCoefficient (D + E) P =
      cartierGeometricPrimeCoefficient D P + cartierGeometricPrimeCoefficient E P := by
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨x, q, hq, hQ, hPI⟩ := exists_original_prime_chart_branch P
  obtain ⟨g, hf, hF, hgen, hzero⟩ := exists_cartier_centered_stalk_generator D x
  obtain ⟨k, hk, hK, hkgen, hkzero⟩ := exists_cartier_centered_stalk_generator E x
  obtain ⟨b, hb, hB, hbgen, hbzero⟩ := exists_cartier_centered_stalk_generator (D + E) x
  let e := (complexChartAt (n := m + 1) x).val
  let center := fun f : M → ℂ => fun z : ComplexModel (m + 1) => f (e.symm (z + e x))
  let G : M → ℂ := fun y => g y * k y
  have hGhol : HolomorphicAt (m + 1) G x := hgen.self_of_nhds.1.mul hkgen.self_of_nhds.1
  have hGgen : ∀ f, (D + E).ideal.mem x f ↔ IsInSpanAt (n := m + 1) (· = G) x f := by
    intro f
    exact MemberPullback.mul_mem_iff_of_generators hgen.self_of_nhds.2 hkgen.self_of_nhds.2
      hgen.self_of_nhds.1 hkgen.self_of_nhds.1 f
  obtain ⟨u, hu, hu0, _hunear, htransition⟩ := exists_centered_unit_transition_of_cartier_generators
    (D + E) x b G hbgen.self_of_nhds.1 hGhol hbgen.self_of_nhds.2 hGgen
  have hunit : IsUnit (HolGerm.mk u hu) := (HolGerm.isUnit_iff_eval_ne_zero _).mpr
    (by simpa only [HolGerm.eval_mk] using hu0)
  have heq : HolGerm.mk (center b) hb =
      (HolGerm.mk (center g) hf * HolGerm.mk (center k) hk) * HolGerm.mk u hu := by
    rw [← HolGerm.mk_mul (center g) (center k) hf hk,
      ← HolGerm.mk_mul (fun z => center g z * center k z) u
        (eventually_differentiableAt_mul hf hk) hu]
    exact HolGerm.mk_eq_mk_iff.mpr htransition
  rw [cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity (D + E) P x b hb hB hbgen hbzero q hq hQ hPI,
    cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity D P x g hf hF hgen hzero q hq hQ hPI,
    cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity E P x k hk hK hkgen hkzero q hq hQ hPI]
  change multiplicity (HolGerm.mk q hq) (HolGerm.mk (center b) hb) = _
  have hprod := FiniteMultiplicity.of_prime_left hQ (mul_ne_zero hF hK)
  have hall := FiniteMultiplicity.of_prime_left hQ (mul_ne_zero (mul_ne_zero hF hK) hunit.ne_zero)
  rw [heq, multiplicity_mul hQ hall, multiplicity_mul hQ hprod,
    multiplicity_of_isUnit_right hQ.not_isUnit hunit, add_zero]

theorem cartierGeometricPrimeCoefficient_nsmul (D : EffectiveDivisor (m + 1) M)
    (P : GeometricPrimeCarrier (m + 1) M) (a : ℕ) :
    cartierGeometricPrimeCoefficient (a • D) P = a * cartierGeometricPrimeCoefficient D P := by
  induction a with
  | zero => rw [zero_nsmul, cartierGeometricPrimeCoefficient_zero, zero_mul]
  | succ a ih => rw [succ_nsmul, cartierGeometricPrimeCoefficient_add, ih, Nat.succ_mul]

theorem cartierGeometricPrimeCoefficient_finset_sum {ι : Type*} (s : Finset ι)
    (D : ι → EffectiveDivisor (m + 1) M) (a : ι → ℕ) (P : GeometricPrimeCarrier (m + 1) M) :
    cartierGeometricPrimeCoefficient (∑ i ∈ s, a i • D i) P =
      ∑ i ∈ s, a i * cartierGeometricPrimeCoefficient (D i) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cartierGeometricPrimeCoefficient_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, cartierGeometricPrimeCoefficient_add,
      cartierGeometricPrimeCoefficient_nsmul, ih]

end SGPT.PSH
