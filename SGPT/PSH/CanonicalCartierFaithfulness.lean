import SGPT.PSH.CanonicalCartierCoefficients
import SGPT.Foundations.Analysis.Pending.HolomorphicBoundedQuotient
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition HolomorphicBoundedQuotient
open scoped Topology Manifold ContDiff

private theorem singleton_span_of_centered_dvd {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (x : M) (g h : M → ℂ) (hh : HolomorphicAt n h x)
    (hF : OkaRelationSheaf.HolAt (fun z => g (rechartSymm n x z)) 0)
    (hG : OkaRelationSheaf.HolAt (fun z => h (rechartSymm n x z)) 0)
    (hdiv : HolGerm.mk (fun z => g (rechartSymm n x z)) hF ∣
      HolGerm.mk (fun z => h (rechartSymm n x z)) hG) :
    IsInSpanAt (n := n) (· = g) x h := by
  obtain ⟨c, hc⟩ := hdiv
  obtain ⟨C, hC, hCrep⟩ := HolGerm.exists_eq_mk c
  have heq : (fun z => h (rechartSymm n x z)) =ᶠ[𝓝 0]
      fun z => g (rechartSymm n x z) * C z := by
    apply HolGerm.mk_eq_mk_iff.mp (show HolGerm.mk
      (fun z => h (rechartSymm n x z)) hG = HolGerm.mk
        (fun z => g (rechartSymm n x z) * C z)
        (eventually_differentiableAt_mul hF hC) from ?_)
    rw [HolGerm.mk_mul (fun z => g (rechartSymm n x z)) C hF hC, ← hCrep]
    exact hc
  refine isInSpanAt_eq_iff.mpr ⟨hh, (fun y => C (rechart n x y)),
    holomorphicAt_comp_rechart (n := n) (x := x) hC, ?_⟩
  filter_upwards [tendsto_rechart (n := n) x heq,
    eventually_rechartSymm_rechart (n := n) x] with y hy hxy
  change h (rechartSymm n x (rechart n x y)) =
    g (rechartSymm n x (rechart n x y)) * C (rechart n x y) at hy
  rw [hxy] at hy
  exact hy.trans (mul_comm _ _)

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Actual coefficient comparison on primes MEETING the original set
gives the FULL contravariant ideal inclusion at every point of that set.
Actual branch carriers, nonzero equations and cofactors are produced internally. -/
theorem cartierIdeal_le_on_of_geometricPrimeCoefficient_le
    (D E : EffectiveDivisor (m + 1) M)
    (V : Set M) (hcoeff : ∀ P, (P.val ∩ V).Nonempty →
      cartierGeometricPrimeCoefficient D P ≤ cartierGeometricPrimeCoefficient E P) :
    ∀ x ∈ V, ∀ b, E.ideal.mem x b → D.ideal.mem x b := by
  classical
  let : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  intro x hxV b hb
  obtain ⟨gD, hfD, hFD, hgenD, hzeroD⟩ := exists_cartier_centered_stalk_generator D x
  obtain ⟨gE, hfE, hFE, hgenE, hzeroE⟩ := exists_cartier_centered_stalk_generator E x
  let e := (complexChartAt (n := m + 1) x).val
  let fD : ComplexModel (m + 1) → ℂ := fun z => gD (e.symm (z + e x))
  let fE : ComplexModel (m + 1) → ℂ := fun z => gE (e.symm (z + e x))
  have hdiv : HolGerm.mk fD hfD ∣ HolGerm.mk fE hfE := by
    apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hFD).mpr
    intro Q hQ
    by_cases hQD : Q ∣ HolGerm.mk fD hfD
    · obtain ⟨q, hq, rfl⟩ := HolGerm.exists_eq_mk Q
      have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → fD z = 0 := by
        have hmem : HolGerm.mk fD hfD ∈ AnalyticGermDecomposition.vanishingIdeal {z | q z = 0} := by
          rw [(ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
          exact Ideal.mem_span_singleton.mpr hQD
        exact mem_vanishingIdeal_mk.mp hmem
      have hsub : {z | q z = 0} ≤ᶠ[𝓝 0]
          AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
        filter_upwards [hvan, Filter.eventuallyEq_set.mp hzeroD] with z hz heq hzq
        exact heq.mpr (hz hzq)
      obtain ⟨B, hB, _huniq⟩ := exists_unique_cartierPrimeComponent_of_chart_prime D x q hq hQ hsub
      let P := cartierComponentGeometricPrime D B
      have hq0 : q 0 = 0 := by
        by_contra hne
        apply hQ.not_isUnit
        exact (HolGerm.isUnit_iff_eval_ne_zero _).mpr (by simpa only [HolGerm.eval_mk] using hne)
      have hxP : x ∈ P.val := by
        change x ∈ B.val
        have hz := hB.1.self_of_nhds hq0
        change (0 : ComplexModel (m + 1)) + e x ∈ e.target ∧
          e.symm (0 + e x) ∈ (cartierPrimeComponent D B).carrier at hz
        have hxE : x ∈ e.source := mem_complexChartAt_source x
        simpa only [zero_add, e.left_inv hxE, cartierPrimeComponent_carrier] using hz.2
      have hPI : AnalyticGermDecomposition.vanishingIdeal
          (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
          Ideal.span {HolGerm.mk q hq} := by
        change AnalyticGermDecomposition.vanishingIdeal
          (AnalyticDescendingChain.chartGerm (n := m + 1) B.val x) ≤ _
        simpa only [cartierPrimeComponent_carrier] using hB.2
      have hDread := cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity
        D P x gD hfD hFD hgenD hzeroD q hq hQ hPI
      have hEread := cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity
        E P x gE hfE hFE hgenE hzeroE q hq hQ hPI
      have hmul : multiplicity (HolGerm.mk q hq) (HolGerm.mk fD hfD) ≤
          multiplicity (HolGerm.mk q hq) (HolGerm.mk fE hfE) := by
        rw [← hDread, ← hEread]
        exact hcoeff P ⟨x, hxP, hxV⟩
      rw [(FiniteMultiplicity.of_prime_left hQ hFD).emultiplicity_eq_multiplicity,
        (FiniteMultiplicity.of_prime_left hQ hFE).emultiplicity_eq_multiplicity]
      exact_mod_cast hmul
    · rw [emultiplicity_eq_zero.mpr hQD]
      exact zero_le
  have hEspan : IsInSpanAt (n := m + 1) (· = gD) x gE := by
    apply singleton_span_of_centered_dvd x gD gE hgenE.self_of_nhds.1
      (by simpa only [rechartSymm, complexChartAt] using hfD)
      (by simpa only [rechartSymm, complexChartAt] using hfE)
    simpa only [fD, fE, e, rechartSymm, complexChartAt] using hdiv
  obtain ⟨_, c, hc, hge⟩ := isInSpanAt_eq_iff.mp hEspan
  obtain ⟨hbhol, t, ht, hbt⟩ := isInSpanAt_eq_iff.mp ((hgenE.self_of_nhds.2 b).mp hb)
  apply (hgenD.self_of_nhds.2 b).mpr
  refine isInSpanAt_eq_iff.mpr ⟨hbhol, (fun y => t y * c y), ht.mul hc, ?_⟩
  filter_upwards [hbt, hge] with y hby hgy
  rw [hby, hgy]
  ring

/-- EVERY actual canonical coefficient comparison gives the FULL original
ideal inclusion at EVERY original stalk, including absent components. -/
theorem cartierIdeal_le_of_geometricPrimeCoefficient_le
    (D E : EffectiveDivisor (m + 1) M)
    (hcoeff : ∀ P, cartierGeometricPrimeCoefficient D P ≤ cartierGeometricPrimeCoefficient E P) :
    E.ideal.Le D.ideal := by
  intro x b hb
  exact cartierIdeal_le_on_of_geometricPrimeCoefficient_le D E Set.univ
    (fun P _ => hcoeff P) x (mem_univ x) b hb

/-- The ENTIRE actual canonical coefficient function faithfully determines
the genuine Cartier divisor by BOTH full original stalk inclusions. -/
theorem cartier_eq_of_geometricPrimeCoefficient_eq
    (D E : EffectiveDivisor (m + 1) M)
    (hcoeff : ∀ P, cartierGeometricPrimeCoefficient D P = cartierGeometricPrimeCoefficient E P) :
    D = E := by
  apply HironakaEffectiveDivisorSum.effectiveDivisor_eq_of_ideal_eq
  have hED := cartierIdeal_le_of_geometricPrimeCoefficient_le D E (fun P => (hcoeff P).le)
  have hDE := cartierIdeal_le_of_geometricPrimeCoefficient_le E D (fun P => (hcoeff P).symm.le)
  exact GermIdeal.ext (funext fun x => funext fun b => propext ⟨hDE x b, hED x b⟩)

end SGPT.PSH
