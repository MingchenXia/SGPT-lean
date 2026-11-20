import SGPT.PSH.SharedPrimeGlobalEquality

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending AnalyticGermDecomposition
open scoped Topology Manifold ContDiff Classical

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The SAME literal actual Cartier component, as a canonical geometric prime. -/
def cartierComponentGeometricPrime (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    GeometricPrimeCarrier (m + 1) M :=
  ⟨B.val, cartierPrimeComponent D B, cartierPrimeComponent_carrier D B,
    by rw [cartierPrimeComponent_dim]⟩

/-- The actual original component order, or zero if the original carrier
is absent. No coefficient catalog or geometric output is supplied. -/
def cartierGeometricPrimeCoefficient (D : EffectiveDivisor (m + 1) M)
    (P : GeometricPrimeCarrier (m + 1) M) : ℕ :=
  if h : P.val ∈ GlobalComponents.globalComponents (n := m + 1) D.support then
    regularComponentOrder D D.support ⟨P.val, h⟩ else 0

theorem cartierGeometricPrimeCoefficient_component (D : EffectiveDivisor (m + 1) M)
    (B : GlobalComponents.globalComponents (n := m + 1) D.support) :
    cartierGeometricPrimeCoefficient D (cartierComponentGeometricPrime D B) =
      regularComponentOrder D D.support B := by
  change (if h : B.val ∈ GlobalComponents.globalComponents (n := m + 1) D.support then
    regularComponentOrder D D.support ⟨B.val, h⟩ else 0) = _
  rw [dif_pos B.property]

theorem cartierGeometricPrimeCoefficient_pos_iff (D : EffectiveDivisor (m + 1) M)
    (P : GeometricPrimeCarrier (m + 1) M) :
    0 < cartierGeometricPrimeCoefficient D P ↔
      P.val ∈ GlobalComponents.globalComponents (n := m + 1) D.support := by
  classical
  unfold cartierGeometricPrimeCoefficient
  split_ifs with h
  · exact iff_of_true (regularComponentOrder_pos D ⟨P.val, h⟩) h
  · simp only [lt_self_iff_false, false_iff]
    exact h

theorem cartierGeometricPrimeCoefficient_reduced (P Q : GeometricPrimeCarrier (m + 1) M) :
    cartierGeometricPrimeCoefficient (geometricPrimeCarrierEffectiveDivisor P) Q =
      if Q = P then 1 else 0 := by
  classical
  by_cases hQP : Q = P
  · subst Q
    rw [if_pos rfl, cartierGeometricPrimeCoefficient]
    have hmem : P.val ∈ GlobalComponents.globalComponents (n := m + 1)
        (geometricPrimeCarrierEffectiveDivisor P).support := (geometricPrimeCarrierComponent P).property
    rw [dif_pos hmem]
    exact geometricPrimeCarrierComponent_order_one P
  · rw [if_neg hQP, cartierGeometricPrimeCoefficient]
    apply dif_neg
    intro hQ
    have hQ' : Q.val ∈ GlobalComponents.globalComponents (n := m + 1) P.val := by
      rwa [geometricPrimeCarrierEffectiveDivisor_support] at hQ
    exact hQP (GeometricPrimeCarrier.ext
      (geometricPrimeCarrier_globalComponent_eq P ⟨Q.val, hQ'⟩))

private theorem branch_of_actual_prime_ideal
    (P : GeometricPrimeCarrier (m + 1) M) (x : M)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (hPI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
      Ideal.span {HolGerm.mk q hq}) :
    {z | q z = 0} ≤ᶠ[𝓝 0] AnalyticDescendingChain.chartGerm (n := m + 1) P.val x := by
  obtain ⟨r, hr, _hR, _hsR, hI, hzero⟩ := exists_reduced_cartierPrimeComponent_equation
    (geometricPrimeCarrierEffectiveDivisor P) (geometricPrimeCarrierComponent P) x
  rw [geometricPrimeCarrierComponent_subvariety, P.subvariety_carrier] at hI hzero
  have hrmem : HolGerm.mk r hr ∈ vanishingIdeal
      (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) := by
    rw [hI]
    exact Ideal.mem_span_singleton_self _
  have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → r z = 0 := by
    have hmem : HolGerm.mk r hr ∈ AnalyticGermDecomposition.vanishingIdeal {z | q z = 0} := by
      rw [(ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
      exact hPI hrmem
    exact mem_vanishingIdeal_mk.mp hmem
  filter_upwards [hvan, Filter.eventuallyEq_set.mp hzero] with z hz heq hzq
  exact heq.mpr (hz hzq)

/-- A genuine branch of the SAME original prime reads the actual original
Cartier coefficient, including literal coefficient zero for absent components. -/
theorem cartierGeometricPrimeCoefficient_eq_primeGerm_multiplicity
    (D : EffectiveDivisor (m + 1) M) (P : GeometricPrimeCarrier (m + 1) M)
    (x : M) (g : M → ℂ)
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ
      (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) z)
    (hF : HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
      (z + (complexChartAt (n := m + 1) x).val x))) hf ≠ 0)
    (hgen : ∀ᶠ y in 𝓝 x, HolomorphicAt (m + 1) g y ∧ ∀ b,
      D.ideal.mem y b ↔ IsInSpanAt (n := m + 1) (· = g) y b)
    (hzero : AnalyticDescendingChain.chartGerm (n := m + 1) D.support x =ᶠ[𝓝 0]
      {z | g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x)) = 0})
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ q z)
    (hQ : Prime (HolGerm.mk q hq))
    (hPI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) P.val x) ≤
      Ideal.span {HolGerm.mk q hq}) :
    cartierGeometricPrimeCoefficient D P = multiplicity (HolGerm.mk q hq)
      (HolGerm.mk (fun z => g ((complexChartAt (n := m + 1) x).val.symm
        (z + (complexChartAt (n := m + 1) x).val x))) hf) := by
  classical
  let f : ComplexModel (m + 1) → ℂ := fun z => g ((complexChartAt (n := m + 1) x).val.symm
    (z + (complexChartAt (n := m + 1) x).val x))
  have hPbranch := branch_of_actual_prime_ideal P x q hq hQ hPI
  have hread (B : GlobalComponents.globalComponents (n := m + 1) D.support)
      (hBP : B.val = P.val) : HolGerm.mk q hq ∣ HolGerm.mk f hf := by
    apply Ideal.mem_span_singleton.mp
    rw [← (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [hPbranch, Filter.eventuallyEq_set.mp hzero] with z hz heq hzq
    apply heq.mp
    have hzP := hz hzq
    refine ⟨hzP.1, ?_⟩
    apply GlobalComponents.subset_of_mem_globalComponents (cartierSupport_isComplexAnalytic D) B.property
    rw [hBP]
    exact hzP.2
  by_cases hdiv : HolGerm.mk q hq ∣ HolGerm.mk f hf
  · have hvan : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), q z = 0 → f z = 0 := by
      have hmem : HolGerm.mk f hf ∈ AnalyticGermDecomposition.vanishingIdeal {z | q z = 0} := by
        rw [(ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible q hq hQ).1]
        exact Ideal.mem_span_singleton.mpr hdiv
      exact mem_vanishingIdeal_mk.mp hmem
    have hDbranch : {z | q z = 0} ≤ᶠ[𝓝 0]
        AnalyticDescendingChain.chartGerm (n := m + 1) D.support x := by
      filter_upwards [hvan, Filter.eventuallyEq_set.mp hzero] with z hz heq hzq
      exact heq.mpr (hz hzq)
    obtain ⟨B, hB, _huniq⟩ := exists_unique_cartierPrimeComponent_of_chart_prime
      D x q hq hQ hDbranch
    have hBP : cartierComponentGeometricPrime D B = P := by
      apply geometricPrimeCarrier_eq_of_common_chart_prime _ _ x q hq hQ
      · change AnalyticGermDecomposition.vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) B.val x) ≤ _
        simpa only [cartierPrimeComponent_carrier] using hB.2
      · exact hPI
    rw [← hBP, cartierGeometricPrimeCoefficient_component]
    exact regularComponentOrder_eq_primeGerm_multiplicity D x g hf hF hgen hzero q hq hQ B hB.1
  · rw [multiplicity_eq_zero.mpr hdiv, cartierGeometricPrimeCoefficient]
    apply dif_neg
    intro hmem
    exact hdiv (hread ⟨P.val, hmem⟩ rfl)

end SGPT.PSH
