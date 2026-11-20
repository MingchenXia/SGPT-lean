import SGPT.Foundations.Analysis.Pending.AnalyticModificationPreferredJacobianTest
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierPrincipalization


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero

open FirstPass FirstPass.HolomorphicMaps FirstPass.HolomorphicIdealSheaves

universe u

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual modification noncollapse preserves an ORIGINAL locally holomorphic nonzero germ. -/
theorem frequently_comp_ne_zero {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (y : Y) {F : X → ℂ} (hF : HolomorphicAt n F (π y))
    (hFnon : ∃ᶠ x in 𝓝 (π y), F x ≠ 0) :
    ∃ᶠ z in 𝓝 y, F (π z) ≠ 0 := by
  let e := complexChartAt (n := n) y
  let d := complexChartAt (n := n) (π y)
  let g : ComplexModel n → ℂ := fun z => F (d.val.symm z)
  have hg : ∀ᶠ z in 𝓝 (d.val (π y)), DifferentiableAt ℂ g z :=
    CartanLocalReduction.holAt_comp_chart_symm (mem_complexChartAt_source (π y)) hF
  have hgnon : ∃ᶠ z in 𝓝 (d.val (π y)), g z ≠ 0 := by
    by_contra hn
    have hzero : ∀ᶠ z in 𝓝 (d.val (π y)), g z = 0 := by
      filter_upwards [Filter.not_frequently.mp hn] with z hz
      exact not_ne_iff.mp hz
    have hback := (d.val.continuousAt (mem_complexChartAt_source (π y))).tendsto.eventually hzero
    have hzeroF : ∀ᶠ x in 𝓝 (π y), F x = 0 := by
      filter_upwards [hback, d.val.open_source.mem_nhds (mem_complexChartAt_source (π y))] with x hx hxs
      simpa only [g, d.val.left_inv hxs] using hx
    exact (hFnon.and_eventually hzeroF).exists.elim fun _ h => h.1 h.2
  have hweighted := AnalyticModificationPreferredJacobianTest.frequently_preferred_jacobian_test_ne_zero
    hπ y hg hgnon
  have hyD : e.val y ∈ coordinateDomain π e d :=
    mem_coordinateDomain (mem_complexChartAt_source y) (mem_complexChartAt_source (π y))
  have hnon : ∃ᶠ z in 𝓝 (e.val y), F (π (e.val.symm z)) ≠ 0 := by
    apply (hweighted.and_eventually ((coordinateDomain_isOpen hπ.1 e d).mem_nhds hyD)).mono
    intro z hz
    have h := (mul_ne_zero_iff.mp hz.1).1
    change F (d.val.symm (d.val (π (e.val.symm z)))) ≠ 0 at h
    simpa only [d.val.left_inv hz.2.2] using h
  have hT : Tendsto e.val.symm (𝓝 (e.val y)) (𝓝 y) := by
    have h := e.val.continuousAt_symm (e.val.map_source (mem_complexChartAt_source y))
    rw [ContinuousAt, e.val.left_inv (mem_complexChartAt_source y)] at h
    exact h
  apply Filter.frequently_iff_forall_eventually_exists_and.mpr
  intro q hq
  obtain ⟨z, hz, hzq⟩ := (hnon.and_eventually (hT.eventually hq)).exists
  exact ⟨e.val.symm z, hz, hzq⟩

/-- A genuine original member, its literal pulled generator and noncollapse prove nonzero stalks. -/
theorem isNonzeroAt_pullback_multiplierIdeal {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    {u : X → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    {c : ℝ} (hc : 0 < c) (y : Y) :
    DivisorExponent.IsNonzeroAt
      (GermIdeal.pullback (m := n) π (multiplierIdeal (n := n) c u)) y := by
  obtain ⟨F, hF, hFnon⟩ :=
    GlobalQuasiPshMultiplierPrincipalization.exists_nonzero_germ_of_isGlobalQuasiPshPotential hu hc (π y)
  refine ⟨F ∘ π, ?_, frequently_comp_ne_zero hπ y hF.1 hFnon⟩
  exact InvertibleIdealQuotient.isInSpanAt_self
    (S := fun s => ∃ a, (multiplierIdeal (n := n) c u).mem (π y) a ∧ s = a ∘ π)
    ⟨F, hF, rfl⟩
    (hF.1.comp_contMDiff (Eventually.of_forall fun _ => hπ.1.contMDiffAt))

/-- Actual local Nadel coherence and literal holomorphic ideal pullback, without a supplied family. -/
theorem isCoherent_pullback_multiplierIdeal {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π)
    (hn : 0 < n) {u : X → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    {c : ℝ} (hc : 0 < c) :
    (GermIdeal.pullback (m := n) π (multiplierIdeal (n := n) c u)).IsCoherent :=
  GermIdealPullbackCalculus.isCoherent_pullback hπ.1
    (GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic hn hu hc)

end SGPT.Foundations.Analysis.Pending.MultiplierPullbackNonzero
