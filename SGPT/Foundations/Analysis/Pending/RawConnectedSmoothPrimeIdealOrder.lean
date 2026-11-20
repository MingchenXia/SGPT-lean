import SGPT.Foundations.Analysis.Pending.RawGlobalPrimeMultiplierOrderConverse
import SGPT.Foundations.Analysis.Pending.RawIdealOrderModificationGenericComparison
import SGPT.Foundations.Analysis.Pending.RawMultiplierIdealOrderModificationDescent
import SGPT.Foundations.Analysis.Pending.GlobalSmoothHypersurfacePrimeComponent
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

set_option autoImplicit false

/-! # Original raw all-chart ideal order and connected smooth whole prime presentations -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawConnectedSmoothPrimeIdealOrder

open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves
  FirstPass.IEnvelope FirstPass.NonKahlerLocus
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

private theorem iOrder_of_multiplierIdeals_le
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hpreferred : ∀ c : ℝ, 0 < c →
      (multiplierIdeal (n := m + 1) c u).Le (multiplierIdeal (n := m + 1) c v)) :
    IOrderOnManifold (n := m + 1) u v := by
  intro c hc d z hz g _ hint'
  have hint : MultiplierIntegrableAt (chartFunction u d) c g z volume :=
    (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr hint'
  let x := d.val.symm z
  let F : X → ℂ := fun t => g (d.val t)
  have hx : x ∈ d.val.source := d.val.map_target hz
  have hxz : d.val x = z := d.val.right_inv hz
  have hgnear : ∀ᶠ t in 𝓝 z, DifferentiableAt ℂ g t := by
    obtain ⟨_, U, hU, hzU, hgd, _⟩ := hint
    filter_upwards [hU.mem_nhds hzU] with t ht
    exact (hgd t ht).differentiableAt (hU.mem_nhds ht)
  have hFhol : HolomorphicAt (m + 1) F x := by
    have hgnear' : ∀ᶠ t in 𝓝 (d.val x), DifferentiableAt ℂ g t := by rwa [hxz]
    filter_upwards [d.val.open_source.mem_nhds hx,
      (d.val.continuousAt hx).eventually hgnear'] with t ht hgt
    exact hgt.mdifferentiableAt.comp t
      (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (m + 1))) d.property ht)
  have hgF : g =ᶠ[𝓝 z] fun t => F (d.val.symm t) := by
    filter_upwards [d.val.open_target.mem_nhds hz] with t ht
    simp only [F, d.val.right_inv ht]
  have hdInt : MultiplierIntegrableAt (chartFunction u d) c
      (fun t => F (d.val.symm t)) (d.val x) volume := by
    rw [hxz]
    exact hint.congr (EventuallyEq.refl _ _) hgF
  let e := complexChartAt (n := m + 1) x
  have hue : UpperSemicontinuousOn (chartFunction u e) (ChartWeightedL2.overlapDomain e d) :=
    (hu e).upperSemicontinuousOn.mono fun _ ht => ht.1
  have hFmem : (multiplierIdeal (n := m + 1) c u).mem x F :=
    ⟨hFhol, ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
      e d (mem_complexChartAt_source x) hx hue hc.ne' hdInt⟩
  have hVmem := hpreferred c hc x F hFmem
  have hvd : UpperSemicontinuousOn (chartFunction v d) (ChartWeightedL2.overlapDomain d e) :=
    (hv d).upperSemicontinuousOn.mono fun _ ht => ht.1
  have hVInt := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
    d e hx (mem_complexChartAt_source x) hvd hc.ne' hVmem.2
  rw [hxz] at hVInt
  apply (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp
  exact hVInt.congr (EventuallyEq.refl _ _) hgF.symm

/-- Original raw all-chart order is exactly comparison on every genuine connected
smooth whole prime over the same original manifold. -/
theorem iOrder_iff_all_connected_smooth_prime_orders
    {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v) :
    IOrderOnManifold (n := m + 1) u v ↔
      ∀ (Y : Type u) [TopologicalSpace Y]
        [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y] (π : Y → X),
        AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π →
        ∀ E : Set Y, IsClosed E → IsConnected E →
          (∀ z ∈ E, RegularAtDim (n := m + 1) E z m) →
            (⨅ z ∈ E, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
              ⨅ z ∈ E, lelongNumber (n := m + 1) (fun w => u (π w)) z := by
  constructor
  · intro hI Y _ _ _ π hπ E hclosed hconn hreg
    obtain ⟨c, hc⟩ := hconn.1
    obtain ⟨V, hdim, hcomp, _hcV, _hVA, _hconnV, _hregV, _hloc⟩ :=
      GlobalSmoothHypersurfacePrimeComponent.exists_global_prime_component hclosed hreg hc
    have hVE : V.carrier = E := hcomp.trans (hconn.2.connectedComponentIn hc)
    have h := RawIdealOrderModificationGenericComparison.divisorialLelongNumber_comp_le_of_iOrder
      hπ hu hv hI V hdim
    change (⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => v (π w)) z) ≤
      ⨅ z ∈ V.carrier, lelongNumber (n := m + 1) (fun w => u (π w)) z at h
    simpa only [hVE] using h
  · intro horder
    apply iOrder_of_multiplierIdeals_le hu hv
    intro c hc
    apply RawGlobalPrimeMultiplierOrderConverse.multiplierIdeal_le_of_all_global_prime_orders hu hv
    · intro Y _ _ _ π hπ V _hdim hreg
      have hconn : IsConnected V.carrier :=
        ⟨V.nonempty, CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible
          V.irreducible_carrier⟩
      exact horder Y π hπ V.carrier V.isClosed_carrier hconn hreg
    · exact hc

end
end SGPT.Foundations.Analysis.Pending.RawConnectedSmoothPrimeIdealOrder
