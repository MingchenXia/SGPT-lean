import SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorAssignment
import SGPT.Foundations.Analysis.Pending.ActualCodimensionOneLocalEquations
import SGPT.Foundations.Analysis.Pending.ActualReducedHolomorphicEquation

set_option autoImplicit false

/-!
# The original common prime occurs once in the selected reduced global equation

Complete natural mathematical statement and ENTIRE proof precede the
import-only baseline. The equation and cofactor will be produced internally.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalReducedEquationFactor

open FirstPass FirstPass.NumericalRestrictedVolumeScaffold AnalyticGermDecomposition
  ActualPrimeGlobalPolarComponentAssignment

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The original common-prime data produce a genuine global polar divisor's
actual reduced equation, with this original prime occurring exactly once. -/
theorem exists_global_reduced_equation_with_original_prime_once [CompactSpace M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (p : M) (P : ComplexAnalyticPresentationAt (n := m + 1) (poleSet u) p)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hdiv : ∀ i, HolGerm.mk q hq ∣ centredGeneratorGerm P i) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) M,
      V.carrier ∈ GlobalComponents.globalComponents (n := m + 1) (poleSet u) ∧
      V.carrier ⊆ poleSet u ∧ V.dim = m ∧
      ∃ (r t : ComplexModel (m + 1) → ℂ)
        (hr : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ r w)
        (ht : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ t w),
        HolGerm.mk r hr ≠ 0 ∧ Squarefree (HolGerm.mk r hr) ∧
        vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) =
          Ideal.span {HolGerm.mk r hr} ∧
        (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p =ᶠ[𝓝 0] {w | r w = 0}) ∧
        HolGerm.mk r hr = HolGerm.mk q hq * HolGerm.mk t ht ∧
        (¬HolGerm.mk q hq ∣ HolGerm.mk t ht) ∧
        r =ᶠ[𝓝 0] (fun w => q w * t w) := by
  obtain ⟨V, hglobal, hpolar, hdim, _hsub, hideal⟩ :=
    ActualPrimeGlobalPolarDivisorAssignment.exists_global_polar_divisor_of_common_prime
      hu han p P q hq hQ hdiv
  obtain ⟨f, hf, hF, hVf⟩ :=
    ActualCodimensionOneLocalEquations.exists_nonzero_local_equation V hdim p
  obtain ⟨r, hr, hR, hRsf, hIf, hfr⟩ :=
    ActualReducedHolomorphicEquation.exists_reduced_equation f hf hF
  have hI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) =
      Ideal.span {HolGerm.mk r hr} := (vanishingIdeal_congr hVf).trans hIf
  have hVr : AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p =ᶠ[𝓝 0]
      {w | r w = 0} := hVf.trans (Filter.eventuallyEq_set.mpr hfr)
  have hQR : HolGerm.mk q hq ∣ HolGerm.mk r hr :=
    Ideal.mem_span_singleton.mp
      (hideal (hI.symm ▸ Ideal.mem_span_singleton_self (HolGerm.mk r hr)))
  obtain ⟨T, hRT⟩ := hQR
  obtain ⟨t, ht, hT⟩ := HolGerm.exists_eq_mk T
  rw [hT] at hRT
  have hnot : ¬HolGerm.mk q hq ∣ HolGerm.mk t ht := by
    rintro ⟨a, ha⟩
    apply hQ.not_isUnit
    apply hRsf
    exact ⟨a, by rw [hRT, ha, mul_assoc]⟩
  have hmul : HolGerm.mk r hr = HolGerm.mk (fun w => q w * t w)
      (eventually_differentiableAt_mul hq ht) := by
    rw [HolGerm.mk_mul]
    exact hRT
  exact ⟨V, hglobal, hpolar, hdim, r, t, hr, ht, hR, hRsf, hI, hVr, hRT, hnot,
    HolGerm.mk_eq_mk_iff.mp hmul⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalReducedEquationFactor
