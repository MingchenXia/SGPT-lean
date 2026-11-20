import SGPT.Foundations.Analysis.FirstPass.SubgeodesicChord
import SGPT.Foundations.Analysis.PlurisubharmonicIntegrability

/-!
# Chartwise local integrability of quasi-PSH potentials

A genuine global quasi-plurisubharmonic potential has an actual locally
integrable real representative in every holomorphic chart.  The proof keeps
the extended-real pole set until the almost-everywhere finiteness theorem is
applied; no `EReal.toReal` truncation is used as a geometric definition.
-/

open Filter MeasureTheory Metric Set
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The real representative of a genuine quasi-PSH potential is locally
integrable on the target of every holomorphic chart. -/
theorem IsGlobalQuasiPshPotential.locallyIntegrableOn_chart_toReal
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M) :
    LocallyIntegrableOn (fun z => (chartFunction u e z).toReal)
      e.val.target volume := by
  intro z hz
  obtain ⟨p, g, hp, hg, heq⟩ := hu.1 e z hz
  obtain ⟨D, hD, hzD, hpsh⟩ := hp
  have hnbhd : {y | y ∈ D ∧ y ∈ e.val.target ∧
      ContDiffAt ℝ ∞ g y ∧ chartFunction u e y = p y + (g y : EReal)} ∈ 𝓝 z := by
    filter_upwards [hD.mem_nhds hzD, e.val.open_target.mem_nhds hz, hg, heq]
      with y hyD hye hyg hEq
    exact ⟨hyD, hye, hyg, hEq⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  let W : Set (ComplexModel n) := ball z ε
  let K : Set (ComplexModel n) := closedBall z (ε / 2)
  have hzW : z ∈ W := by simpa [W] using hε
  have hWD : W ⊆ D := fun y hy => (hεsub hy).1
  have hWe : W ⊆ e.val.target := fun y hy => (hεsub hy).2.1
  have hKW : K ⊆ W := by
    exact closedBall_subset_ball (half_lt_self hε)
  have hpW : PlurisubharmonicOn p W :=
    (hpsh.mono hWD).plurisubharmonicOn isOpen_ball
  obtain ⟨q, hqW, hqraw⟩ :=
    hu.2.exists_chart_ne_bot e isOpen_ball hWe hzW
  have hqp : p q ≠ ⊥ := by
    intro hbot
    apply hqraw
    rw [(hεsub hqW).2.2.2, hbot]
    simp
  have hnontrivial : ∃ q ∈ W, p q ≠ ⊥ := ⟨q, hqW, hqp⟩
  have hpLoc : LocallyIntegrableOn (fun y => (p y).toReal) W volume :=
    hpW.locallyIntegrableOn_toReal volume (convex_ball z ε).isPreconnected
      hnontrivial
  have hgCont : ContinuousOn g W := fun y hy =>
    ((hεsub hy).2.2.1.continuousAt).continuousWithinAt
  have hgLoc : LocallyIntegrableOn g W volume :=
    hgCont.locallyIntegrableOn measurableSet_ball
  have hfinite : ∀ᵐ y ∂volume.restrict W, p y ≠ ⊤ ∧ p y ≠ ⊥ :=
    hpW.ae_finite volume (convex_ball z ε).isPreconnected hnontrivial
  have hrawEq :
      (fun y => (p y).toReal + g y) =ᵐ[volume.restrict W]
        (fun y => (chartFunction u e y).toReal) := by
    filter_upwards [ae_restrict_mem measurableSet_ball, hfinite]
      with y hyW hyfin
    rw [(hεsub hyW).2.2.2,
      EReal.toReal_add hyfin.1 hyfin.2 (EReal.coe_ne_top (g y))
        (EReal.coe_ne_bot (g y)), EReal.toReal_coe]
  have hrawLoc :
      LocallyIntegrableOn (fun y => (chartFunction u e y).toReal) W volume :=
    (hpLoc.add hgLoc).congr hrawEq
  refine ⟨K, mem_nhdsWithin_of_mem_nhds
    (Metric.closedBall_mem_nhds z (half_pos hε)), ?_⟩
  exact (hrawLoc.mono_set hKW).integrableOn_isCompact
    (isCompact_closedBall z (ε / 2))

/-- In particular, the real chart representative is integrable on every
compact subset of the chart target. -/
theorem IsGlobalQuasiPshPotential.integrableOn_chart_toReal
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    IntegrableOn (fun z => (chartFunction u e z).toReal) K volume :=
  ((hu.locallyIntegrableOn_chart_toReal e).mono_set hKe).integrableOn_isCompact hK

end

end SGPT.Foundations.Analysis.FirstPass
