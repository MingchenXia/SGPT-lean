import SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarComponentAssignment
import SGPT.Foundations.Analysis.Pending.ActualPrimeRegularFiniteAvoidance
import SGPT.Foundations.Analysis.Pending.DimensionMonotone
import SGPT.Foundations.Analysis.Pending.PureDimension

set_option autoImplicit false

/-!
# An original common prime selects a genuine codimension-one global component

Complete natural mathematical statement and ENTIRE proof precede this
import-only baseline. Regular points and the dimension equality are produced.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorAssignment

open FirstPass FirstPass.NumericalRestrictedVolumeScaffold AnalyticGermDecomposition
  ActualPrimeGlobalPolarComponentAssignment

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem le_dim_of_prime_zero_germ_subset
    (V : ClosedIrreducibleAnalyticSubvariety (m + 1) M) (p : M)
    (q : ComplexModel (m + 1) → ℂ)
    (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hsub : {w | q w = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) : m ≤ V.dim := by
  let e := (complexChartAt (n := m + 1) p).val
  have htarget : ∀ᶠ w in 𝓝 (0 : ComplexModel (m + 1)), w + e p ∈ e.target :=
    ((continuous_add_const (e p)).tendsto' 0 _ (zero_add _))
      (e.open_target.mem_nhds (e.map_source (mem_complexChartAt_source p)))
  obtain ⟨U, hUsub, hUo, hU0⟩ := mem_nhds_iff.mp (hsub.and htarget)
  let B : Set M := e.source ∩ e ⁻¹' {z | q (z - e p) = 0 ∧ z - e p ∈ U}
  have hBV : B ⊆ V.carrier := by
    intro y hy
    have hz := (hUsub hy.2.2).1 hy.2.1
    have hmem := hz.2
    change e.symm (e y - e p + e p) ∈ V.carrier at hmem
    simpa only [sub_add_cancel, e.left_inv hy.1] using hmem
  have heq : AnalyticDescendingChain.chartGerm (n := m + 1) B p ∩ U =
      {w | q w = 0} ∩ U := by
    ext w
    constructor
    · rintro ⟨hwB, hwU⟩
      have ht : w + e p ∈ e.target := (hUsub hwU).2
      have hright : e (e.symm (w + e p)) = w + e p := e.right_inv ht
      have hzero := hwB.2.2.1
      change q (e (e.symm (w + e p)) - e p) = 0 at hzero
      refine ⟨?_, hwU⟩
      change q w = 0
      rwa [hright, add_sub_cancel_right] at hzero
    · rintro ⟨hqw, hwU⟩
      have ht : w + e p ∈ e.target := (hUsub hwU).2
      refine ⟨⟨ht, e.map_target ht, ?_, ?_⟩, hwU⟩
      · change q (e (e.symm (w + e p)) - e p) = 0
        rw [e.right_inv ht, add_sub_cancel_right]
        exact hqw
      · change e (e.symm (w + e p)) - e p ∈ U
        simpa only [e.right_inv ht, add_sub_cancel_right] using hwU
  have hfreq := ActualPrimeRegularFiniteAvoidance.frequently_regular_zero_avoiding_finite_family
    q hq hQ (fun i : Fin 0 => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  obtain ⟨w, hwU, _hqw, hwreg, _htests⟩ :=
    Filter.frequently_iff.mp hfreq (hUo.mem_nhds hU0)
  have hwB : RegularAtDim (n := m + 1)
      (AnalyticDescendingChain.chartGerm (n := m + 1) B p) w m :=
    RegularPointDimension.regularAtDim_of_inter_eq hUo hwU heq.symm hwreg
  have hyB := DimensionMonotone.regularAtDim_of_chartGerm hwB
  obtain ⟨y, _hy, d, hmd, hyd⟩ :=
    DimensionMonotone.locDimGE_of_regularAtDim_subset V.analytic hBV hyB univ univ_mem
  exact (PureDimension.eq_dim_of_regularAtDim V hyd) ▸ hmd

/-- The same original common-prime data internally produce a genuine global
polar component of codimension one, with the original ideal relation. -/
theorem exists_global_polar_divisor_of_common_prime [CompactSpace M] {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := m + 1) u)
    (p : M) (P : ComplexAnalyticPresentationAt (n := m + 1) (poleSet u) p)
    (q : ComplexModel (m + 1) → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hdiv : ∀ i, HolGerm.mk q hq ∣ centredGeneratorGerm P i) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) M,
      V.carrier ∈ GlobalComponents.globalComponents (n := m + 1) (poleSet u) ∧
      V.carrier ⊆ poleSet u ∧ V.dim = m ∧
      ({w | q w = 0} ≤ᶠ[𝓝 0] AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ∧
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := m + 1) V.carrier p) ≤
        Ideal.span {HolGerm.mk q hq} := by
  obtain ⟨V, hglobal, hpolar, hdim, hsub, hideal⟩ :=
    exists_global_polar_component_of_common_prime hu han p P q hq hQ hdiv
  have hle := le_dim_of_prime_zero_germ_subset V p q hq hQ hsub
  have heq : V.dim = m := by omega
  exact ⟨V, hglobal, hpolar, heq, hsub, hideal⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarDivisorAssignment
