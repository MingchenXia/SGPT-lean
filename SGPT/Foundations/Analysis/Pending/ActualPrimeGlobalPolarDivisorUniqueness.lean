import SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalReducedEquationFactor
import SGPT.Foundations.Analysis.Pending.ActualPrimeRegularFiniteAvoidance
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus

set_option autoImplicit false

/-!
# Unique global divisor assignment of an original local common prime

The complete natural mathematical statement and ENTIRE proof precede this
baseline. The common open piece and global equality are internally produced.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorUniqueness

open FirstPass FirstPass.NumericalRestrictedVolumeScaffold AnalyticGermDecomposition
  ActualPrimeGlobalPolarComponentAssignment

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem exists_reduced_cofactor
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) M) (hdim : V.dim = m) (p : M)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hideal : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ≤
      Ideal.span {HolGerm.mk q hq}) :
    ∃ (r t : ComplexModel (m + 1) → ℂ)
      (_hr : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ r w)
      (ht : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ t w),
      (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p =ᶠ[𝓝 0] {w | r w = 0}) ∧
      (r =ᶠ[𝓝 0] (fun w => q w * t w)) ∧ ¬HolGerm.mk q hq ∣ HolGerm.mk t ht := by
  obtain ⟨f, hf, hF, hVf⟩ :=
    ActualCodimensionOneLocalEquations.exists_nonzero_local_equation V hdim p
  obtain ⟨r, hr, _hR, hRsf, hIf, hfr⟩ :=
    ActualReducedHolomorphicEquation.exists_reduced_equation f hf hF
  have hI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) =
      Ideal.span {HolGerm.mk r hr} := (vanishingIdeal_congr hVf).trans hIf
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
  exact ⟨r, t, hr, ht, hVf.trans (Filter.eventuallyEq_set.mpr hfr),
    HolGerm.mk_eq_mk_iff.mp hmul, hnot⟩

private theorem eq_of_common_prime_ideal
    (V W : ClosedIrreducibleAnalyticSubvariety (m + 1) M)
    (hVdim : V.dim = m) (hWdim : W.dim = m) (p : M)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hVI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ≤
      Ideal.span {HolGerm.mk q hq})
    (hWI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) W.carrier p) ≤
      Ideal.span {HolGerm.mk q hq}) : V = W := by
  obtain ⟨rV, tV, _hrV, htV, hVr, hVm, hVnot⟩ :=
    exists_reduced_cofactor V hVdim p q hq hQ hVI
  obtain ⟨rW, tW, _hrW, htW, hWr, hWm, hWnot⟩ :=
    exists_reduced_cofactor W hWdim p q hq hQ hWI
  let e := (complexChartAt (n := m + 1) p).val
  have htarget : ∀ᶠ w in 𝓝 (0 : ComplexModel (m + 1)), w + e p ∈ e.target :=
    ((continuous_add_const (e p)).tendsto' 0 _ (zero_add _))
      (e.open_target.mem_nhds (e.map_source (mem_complexChartAt_source p)))
  have hconditions : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p ↔ rV z = 0) ∧
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) W.carrier p ↔ rW z = 0) ∧
      rV z = q z * tV z ∧ rW z = q z * tW z ∧
      DifferentiableAt ℂ tV z ∧ DifferentiableAt ℂ tW z ∧ z + e p ∈ e.target := by
    filter_upwards [Filter.eventuallyEq_set.mp hVr, Filter.eventuallyEq_set.mp hWr,
      hVm, hWm, htV, htW, htarget] with z hV hW hmV hmW hdV hdW ht
    exact ⟨hV, hW, hmV, hmW, hdV, hdW, ht⟩
  obtain ⟨A, hAsub, hAo, hA0⟩ := mem_nhds_iff.mp hconditions
  let a : Fin 2 → ComplexModel (m + 1) → ℂ := ![tV, tW]
  have ha : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a i) z := by
    intro i
    fin_cases i
    · exact htV
    · exact htW
  have hnot : ∀ i, ¬HolGerm.mk q hq ∣ HolGerm.mk (a i) (ha i) := by
    intro i
    fin_cases i
    · exact hVnot
    · exact hWnot
  have hfreq := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
    q hq hQ a ha hnot
  obtain ⟨w, hwA, hqw, _hwreg, hwtests⟩ :=
    Filter.frequently_iff.mp hfreq (hAo.mem_nhds hA0)
  have hnV : tV w ≠ 0 := hwtests 0
  have hnW : tW w ≠ 0 := hwtests 1
  have hdV : DifferentiableAt ℂ tV w := (hAsub hwA).2.2.2.2.1
  have hdW : DifferentiableAt ℂ tW w := (hAsub hwA).2.2.2.2.2.1
  have hlocal : ∀ᶠ z in 𝓝 w, z ∈ A ∧ tV z ≠ 0 ∧ tW z ≠ 0 := by
    filter_upwards [hAo.mem_nhds hwA, hdV.continuousAt.eventually_ne hnV,
      hdW.continuousAt.eventually_ne hnW] with z hz hnVz hnWz
    exact ⟨hz, hnVz, hnWz⟩
  obtain ⟨O, hOsub, hOo, hwO⟩ := mem_nhds_iff.mp hlocal
  have hboth : ∀ z ∈ O,
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p ↔ q z = 0) ∧
      (z ∈ AnalyticDescendingChain.chartGerm (n := m + 1) W.carrier p ↔ q z = 0) := by
    intro z hz
    obtain ⟨hVz, hWz, hVmz, hWmz, _hdVz, _hdWz, _htz⟩ := hAsub (hOsub hz).1
    refine ⟨hVz.trans ?_, hWz.trans ?_⟩
    · rw [hVmz, mul_eq_zero]
      exact or_iff_left (hOsub hz).2.1
    · rw [hWmz, mul_eq_zero]
      exact or_iff_left (hOsub hz).2.2
  let U : Set M := e.source ∩ e ⁻¹' ((fun z => z - e p) ⁻¹' O)
  have hUo : IsOpen U :=
    e.isOpen_inter_preimage (hOo.preimage (continuous_id.sub continuous_const))
  have hpointV := (hboth w hwO).1.mpr hqw
  have hpointW := (hboth w hwO).2.mpr hqw
  have ht : w + e p ∈ e.target := (hAsub hwA).2.2.2.2.2.2
  have hyU : e.symm (w + e p) ∈ U := by
    refine ⟨e.map_target ht, ?_⟩
    change e (e.symm (w + e p)) - e p ∈ O
    simpa only [e.right_inv ht, add_sub_cancel_right] using hwO
  have hbridge : ∀ y ∈ U, (y ∈ V.carrier ↔ y ∈ W.carrier) := by
    intro y hy
    have hVchart : e y - e p ∈ AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p ↔
        y ∈ V.carrier := by
      change (e y - e p + e p ∈ e.target ∧ e.symm (e y - e p + e p) ∈ V.carrier) ↔ _
      rw [sub_add_cancel, e.left_inv hy.1]
      exact and_iff_right (e.map_source hy.1)
    have hWchart : e y - e p ∈ AnalyticDescendingChain.chartGerm (n := m + 1) W.carrier p ↔
        y ∈ W.carrier := by
      change (e y - e p + e p ∈ e.target ∧ e.symm (e y - e p + e p) ∈ W.carrier) ↔ _
      rw [sub_add_cancel, e.left_inv hy.1]
      exact and_iff_right (e.map_source hy.1)
    exact hVchart.symm.trans (((hboth _ hy.2).1).trans
      (((hboth _ hy.2).2).symm.trans hWchart))
  have hVW : V.carrier ⊆ W.carrier :=
    StrictTransformLocus.subset_of_inter_isOpen_subset V W.analytic hUo
      ⟨e.symm (w + e p), hpointV.2, hyU⟩
      (fun y hy => (hbridge y hy.2).mp hy.1)
  have hWV : W.carrier ⊆ V.carrier :=
    StrictTransformLocus.subset_of_inter_isOpen_subset W V.analytic hUo
      ⟨e.symm (w + e p), hpointW.2, hyU⟩
      (fun y hy => (hbridge y hy.2).mpr hy.1)
  exact ClosedIrreducibleAnalyticSubvariety.ext (Subset.antisymm hVW hWV)
    (hVdim.trans hWdim.symm)

/-- Genuine original data determine a unique global polar divisor for the
original common prime, independently of every finite-cover selection. -/
theorem exists_unique_global_polar_divisor_of_common_prime [CompactSpace M]
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (p : M) (P : ComplexAnalyticPresentationAt (n := m + 1) (poleSet u) p)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hdiv : ∀ i, HolGerm.mk q hq ∣ centredGeneratorGerm P i) :
    ∃! V : ClosedIrreducibleAnalyticSubvariety (m + 1) M,
      V.carrier ∈ GlobalComponents.globalComponents (n := m + 1) (poleSet u) ∧
      V.carrier ⊆ poleSet u ∧ V.dim = m ∧
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ≤
        Ideal.span {HolGerm.mk q hq} := by
  obtain ⟨V, hglobal, hpolar, hdim, r, t, hr, ht, _hR, _hRsf, hI, _hzero, hRT, _hnot, _hmul⟩ :=
    ActualPrimeGlobalReducedEquationFactor.exists_global_reduced_equation_with_original_prime_once
      hu han p P q hq hQ hdiv
  have hVI : vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ≤
      Ideal.span {HolGerm.mk q hq} := by
    rw [hI]
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.mem_span_singleton.mpr ⟨HolGerm.mk t ht, hRT⟩
  refine ⟨V, ⟨hglobal, hpolar, hdim, hVI⟩, ?_⟩
  intro W hW
  exact eq_of_common_prime_ideal W V hW.2.2.1 hdim p q hq hQ hW.2.2.2 hVI

end SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorUniqueness
