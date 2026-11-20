import SGPT.Foundations.Analysis.Pending.AnalyticModificationJacobianMultiplierGerms
import SGPT.Foundations.Analysis.Pending.MultiplierIdealBergmanNadelManifold
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.FirstPass.IEnvelope

set_option autoImplicit false

/-! # Raw all-level multiplier order descends on genuine global modifications -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RawMultiplierIdealOrderModificationDescent

open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves FirstPass.IEnvelope
  DivisorialChangeOfVariables DemaillyApproximantDivisorialLelong

noncomputable section

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X}

/-- Actual all-level pullback order yields every literal original preferred germ inclusion. -/
theorem multiplierIdeal_le_of_pullback_iOrder
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hIp : IOrderOnManifold (n := m + 1) (fun y => u (π y)) (fun y => v (π y)))
    {c : ℝ} (hc : 0 < c) :
    (multiplierIdeal (n := m + 1) c u).Le (multiplierIdeal (n := m + 1) c v) := by
  intro x F hint
  refine ⟨hint.1, ?_⟩
  let d := complexChartAt (n := m + 1) x
  let g : ComplexModel (m + 1) → ℂ := fun z => F (d.val.symm z)
  have hd : d.val x ∈ d.val.target := d.val.map_source (mem_complexChartAt_source x)
  have hg : ∀ᶠ z in 𝓝 (d.val x), DifferentiableAt ℂ g z := by
    obtain ⟨_, U, hU, hxU, hgd, _⟩ := hint.2
    filter_upwards [hU.mem_nhds hxU] with z hz
    exact (hgd z hz).differentiableAt (hU.mem_nhds hz)
  have hsource := (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x hc (hu d (d.val x) hd) hg).mp hint.2
  apply (AnalyticModificationJacobianMultiplierGerms.multiplierIntegrableAt_iff_fiber_jacobian_germs
    hπ x hc (hv d (d.val x) hd) hg).mpr
  intro y hy
  let e := complexChartAt (n := m + 1) y
  let f := coordinateMap π e d
  let G : ComplexModel (m + 1) → ℂ := fun z => g (f z) * complexJacobian f z
  have hD := coordinateDomain_isOpen hπ.1 e d
  have hpD : e.val y ∈ coordinateDomain π e d := by
    apply mem_coordinateDomain (mem_complexChartAt_source y)
    rw [hy]
    exact mem_complexChartAt_source x
  have hcongr (w : X → EReal) :
      (fun z => chartFunction w d (f z)) =ᶠ[𝓝 (e.val y)]
        chartFunction (fun y => w (π y)) e := by
    filter_upwards [hD.mem_nhds hpD] with z hz
    change w (d.val.symm (d.val (π (e.val.symm z)))) = w (π (e.val.symm z))
    rw [d.val.left_inv hz.2]
  have hU : MultiplierIntegrableAt (chartFunction (fun y => u (π y)) e) c G (e.val y) volume :=
    (hsource y hy).congr (hcongr u) (EventuallyEq.refl _ _)
  have hGa : AnalyticAt ℂ G (e.val y) := by
    obtain ⟨_, U, hUo, hpU, hgd, _⟩ := hU
    exact HolomorphicAnalytic.analyticAt_of_differentiableOn hUo hgd hpU
  have hV := hIp c hc e (e.val y) (e.val.map_source (mem_complexChartAt_source y)) G hGa
    ((QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mp hU)
  have hV' : MultiplierIntegrableAt (chartFunction (fun y => v (π y)) e) c G (e.val y) volume :=
    (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
      _ _ _ _).mpr hV
  exact hV'.congr (hcongr v).symm (EventuallyEq.refl _ _)

/-- The result is the original ALL-chart order, using actual coordinate integral transport. -/
theorem iOrder_of_pullback_iOrder
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    {u v : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := m + 1) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := m + 1) v)
    (hIp : IOrderOnManifold (n := m + 1) (fun y => u (π y)) (fun y => v (π y))) :
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
    exact hgt.mdifferentiableAt.comp t (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel (m + 1))) d.property ht)
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
  have hVmem := multiplierIdeal_le_of_pullback_iOrder hπ hu hv hIp hc x F hFmem
  have hvd : UpperSemicontinuousOn (chartFunction v d) (ChartWeightedL2.overlapDomain d e) :=
    (hv d).upperSemicontinuousOn.mono fun _ ht => ht.1
  have hVInt := ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
    d e hx (mem_complexChartAt_source x) hvd hc.ne' hVmem.2
  rw [hxz] at hVInt
  apply (QuasiEquisingularApproximationDemailly.multiplierIntegrableAt_ambient_iff_borel
    _ _ _ _).mp
  exact hVInt.congr (EventuallyEq.refl _ _) hgF.symm

end
end SGPT.Foundations.Analysis.Pending.RawMultiplierIdealOrderModificationDescent
