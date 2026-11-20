import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-!
# Actual chart almost-everywhere increasing directed-limit recovery

Xia SGPT PDF0025 and PDF0128--0129. Actual PSH chart-AE order and genuine
arbitrary-family regularized suprema recover the net's regularized limit.
No sequence, cofinality, global measure transport, or target identity is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAENetRegularizedLimit

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual chart Haar-AE convergence of an increasing directed genuine PSH
net determines its actual regularized supremum, without countable cofinality. -/
theorem uscRegularization_iSup_eq_of_directed_monotone_ae_chart_tendsto
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {θ : ClosedRealOneOneForm n M} {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun i => chartFunction (u i) e z) atTop (𝓝 (chartFunction v e z))) :
    uscRegularization (⨆ i, u i) = v := by
  have huv : ∀ i, u i ≤ v := by
    intro i
    apply RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le
      (hu i).1 hv.1
    intro e
    filter_upwards [hl e] with z hz
    exact (hm (e.val.symm z)).ge_of_tendsto hz i
  obtain ⟨C, hC⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hv
  let U := uscRegularization (⨆ i, u i)
  have hU : IsThetaPshPotential θ.val U :=
    IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded hu
      (fun i x => (huv i x).trans (hC x))
  have huU : ∀ i, u i ≤ U := fun i x =>
    (le_iSup (fun k => u k) i x).trans (le_uscRegularization _ x)
  apply le_antisymm
  · exact uscRegularization_le hv.1.quasiPlurisubharmonic.upperSemicontinuous
      (iSup_le huv)
  · apply RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le
      hv.1 hU.1
    intro e
    filter_upwards [hl e] with z hz
    exact le_of_tendsto_of_tendsto hz tendsto_const_nhds
      (Eventually.of_forall fun i => huU i (e.val.symm z))

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAENetRegularizedLimit
