import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity
import SGPT.Foundations.Analysis.Pending.NegligibleSetsPluripolarProof
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-!
# Actual chart almost-everywhere increasing-limit recovery

Xia SGPT PDF0025 Proposition 1.2.6 and PDF0128. Genuine chart Haar-AE
increasing limits determine the actual regularized supremum by the proved
PSH AE order theorem and actual raw-supremum chart recovery. No global
measure transport or pluripolarity of arbitrary null sets is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAERegularizedLimit

open FirstPass IncreasingMixedRegularizedContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual monotone chart Haar-AE convergence to a genuine PSH potential
produces the actual regularized-supremum identity in every dimension. -/
theorem uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
    {θ : ClosedRealOneOneForm n M} {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential θ.val (u j)) (hv : IsThetaPshPotential θ.val v)
    (hm : ∀ x, Monotone fun j => u j x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun j => chartFunction (u j) e z) atTop (𝓝 (chartFunction v e z))) :
    uscRegularization (⨆ j, u j) = v := by
  have huv : ∀ j, u j ≤ v := by
    intro j
    apply RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le
      (hu j).1 hv.1
    intro e
    filter_upwards [hl e] with z hz
    exact (hm (e.val.symm z)).ge_of_tendsto hz j
  obtain ⟨C, hC⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hv
  let U := uscRegularization (⨆ j, u j)
  have hU : IsThetaPshPotential θ.val U :=
    NegligibleSetsPluripolarProof.isThetaPshPotential_uscRegularization_iSup_of_le hu
      (fun j x => (huv j x).trans (hC x))
  have hmono : Monotone u := fun j k hjk x => hm x hjk
  have hAE (e : ComplexChart n M) :
      ∀ᵐ z ∂(volume.restrict e.val.target), chartFunction U e z = chartFunction v e z := by
    filter_upwards [ae_chartFunction_iSup_eq_of_genuine hu hmono hU e, hl e] with z hz hlim
    have hs : Tendsto (fun j => chartFunction (u j) e z) atTop
        (𝓝 (⨆ j, chartFunction (u j) e z)) :=
      tendsto_atTop_iSup (fun j k hjk => hm (e.val.symm z) hjk)
    exact hz.symm.trans (tendsto_nhds_unique hs hlim)
  apply le_antisymm
  · exact RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le
      hU.1 hv.1 (fun e => (hAE e).mono fun _ hz => hz.le)
  · exact RooftopEnvelopeAeObstacle.ThetaPlurisubharmonic.le_of_ae_in_charts_le
      hv.1 hU.1 (fun e => (hAE e).mono fun _ hz => hz.symm.le)

end

end SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAERegularizedLimit
