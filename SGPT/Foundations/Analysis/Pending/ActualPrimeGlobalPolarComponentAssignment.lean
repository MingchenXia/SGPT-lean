import SGPT.Foundations.Analysis.Pending.ActualPrimeGermFiniteCover
import SGPT.Foundations.Analysis.Pending.ActualAnalyticPoleSubvarieties
import SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain

set_option autoImplicit false

/-!
# Original common prime factors select actual global polar components

The complete mathematical statement and ENTIRE proof precede this import
baseline. The original finite presentation supplies the coarse cover; the
global component and its ideal containment will be internally selected.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarComponentAssignment

open FirstPass FirstPass.NumericalRestrictedVolumeScaffold AnalyticGermDecomposition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Supporting original data: a centred generator's actual holomorphic germ.
Its holomorphicity is derived from the original presentation fields. -/
def centredGeneratorGerm {A : Set M} {p : M}
    (P : ComplexAnalyticPresentationAt (n := n) A p) (i : Fin P.generatorCount) :
    HolGerm (ComplexModel n) :=
  HolGerm.mk (fun w => P.generator i (w + (complexChartAt (n := n) p).val p)) (by
    have hN : ∀ᶠ w in 𝓝 (0 : ComplexModel n),
        w + (complexChartAt (n := n) p).val p ∈ P.coordinateNeighborhood :=
      ((continuous_add_const ((complexChartAt (n := n) p).val p)).tendsto' 0 _
        (zero_add _))
        (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
    filter_upwards [hN] with w hw
    exact ((P.generator_holomorphic i).differentiableAt
      (P.isOpen_coordinateNeighborhood.mem_nhds hw)).comp w
      (differentiableAt_id.add_const _))

/-- The original raw presentation and ordinary common-prime divisibility
internally select a genuine global polar component and its ideal relation. -/
theorem exists_global_polar_component_of_common_prime [CompactSpace M] {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u)
    (p : M) (P : ComplexAnalyticPresentationAt (n := n) (poleSet u) p)
    (q : ComplexModel n → ℂ) (hq : ∀ᶠ w in 𝓝 0, DifferentiableAt ℂ q w)
    (hQ : Prime (HolGerm.mk q hq))
    (hdiv : ∀ i, HolGerm.mk q hq ∣ centredGeneratorGerm P i) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
      V.carrier ∈ GlobalComponents.globalComponents (n := n) (poleSet u) ∧
      V.carrier ⊆ poleSet u ∧ V.dim < n ∧
      ({w | q w = 0} ≤ᶠ[𝓝 0] AnalyticDescendingChain.chartGerm (n := n) V.carrier p) ∧
      vanishingIdeal (AnalyticDescendingChain.chartGerm (n := n) V.carrier p) ≤
        Ideal.span {HolGerm.mk q hq} := by
  have hzero := (ActualPrimeGermGenericAvoidance.vanishingIdeal_zeroSet_eq_and_irreducible
    q hq hQ).1
  have hvan : ∀ i, ∀ᶠ w in 𝓝 (0 : ComplexModel n),
      q w = 0 → P.generator i (w + (complexChartAt (n := n) p).val p) = 0 := by
    intro i
    have hmem : centredGeneratorGerm P i ∈ vanishingIdeal {w | q w = 0} := by
      rw [hzero]
      exact Ideal.mem_span_singleton.mpr (hdiv i)
    exact mem_vanishingIdeal_mk.mp hmem
  have hvan' := Filter.eventually_all.mpr hvan
  let e := (complexChartAt (n := n) p).val
  have hN : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + e p ∈ P.coordinateNeighborhood :=
    ((continuous_add_const (e p)).tendsto' 0 _ (zero_add _))
      (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
  have hsub : {w | q w = 0} ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := n) (poleSet u) p := by
    filter_upwards [hN, hvan'] with w hw hv
    intro hqw
    have ht : w + e p ∈ e.target := P.coordinateNeighborhood_subset_target hw
    have hy : e.symm (w + e p) ∈ e.source := e.map_target ht
    have hz := P.zeroLocus hy (by rwa [e.right_inv ht])
    rw [e.right_inv ht] at hz
    exact ⟨ht, hz.mpr (fun i => hv i hqw)⟩
  obtain ⟨N, V, _hinj, hrange, hV, hunion⟩ :=
    ActualAnalyticPoleSubvarieties.exists_finite_polar_subvarieties hu han
  have hcover : {w | q w = 0} ≤ᶠ[𝓝 0]
      (⋃ j, AnalyticDescendingChain.chartGerm (n := n) (V j).carrier p) := by
    filter_upwards [hsub] with w hw
    intro hqw
    obtain ⟨ht, hy⟩ := hw hqw
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hunion.symm ▸ hy)
    exact mem_iUnion.mpr ⟨j, ht, hj⟩
  obtain ⟨j, hj, hideal⟩ := ActualPrimeGermFiniteCover.exists_member_and_vanishingIdeal_le
    q hq hQ (fun j => AnalyticDescendingChain.chartGerm (n := n) (V j).carrier p)
    (fun j => AnalyticDescendingChain.isAnalyticGerm_chartGerm (V j).irreducible_carrier.analytic p)
    hcover
  exact ⟨V j, hrange ▸ mem_range_self j, (hV j).1, (hV j).2, hj, hideal⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimeGlobalPolarComponentAssignment
