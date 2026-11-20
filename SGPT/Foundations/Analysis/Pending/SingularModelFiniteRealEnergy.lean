import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyPreceq
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDecreasingNets

set_option autoImplicit false

/-!
# Actual real energy on a singular model's finite-energy class

Xia SGPT PDF0118 equation (3.31), PDF0120--0121 Proposition 3.1.16,
and PDF0121--0122 Proposition 3.1.17. The actual finite-energy integral
characterization excludes both infinite energy values; the defining energy
therefore has real translation, order, and decreasing continuity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- The actual finite energy has real translation over an arbitrary singular model. -/
theorem toReal_energy_add_const (omega : KahlerBackground n M)
    (hfinite : RelativeFiniteEnergyPreceq θ φ u hφ) (c : ℝ) :
    (energy θ φ hφ (fun x => u x + (c : EReal))).toReal =
      (energy θ φ hφ u).toReal + c * modelVolume θ φ hφ := by
  rw [SingularModelEnergyExtendedTranslation.energy_add_const omega u c,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hfinite,
    ← EReal.coe_add, EReal.toReal_coe]
  simp only [EReal.toReal_coe]

/-- Real values of actual finite energies preserve the potential order. -/
theorem toReal_energy_mono (omega : KahlerBackground n M) {v : M → EReal}
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) (huv : u ≤ v) :
    (energy θ φ hφ u).toReal ≤ (energy θ φ hφ v).toReal :=
  EReal.toReal_le_toReal (energy_mono_of_le huv)
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega hu).ne'
    (energy_ne_top_of_preceq hv.1.relativePSHPreceq)

/-- Actual extended decreasing continuity gives real energy convergence at
any genuine finite-energy limit; no boundedness of the reference is used. -/
theorem toReal_energy_tendsto_of_antitone (omega : KahlerBackground n M)
    {uk : ℕ → M → EReal} (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (hu0φ : MoreSingularOn (uk 0) φ univ) (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x)))
    (hfinite : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun k => (energy θ φ hφ (uk k)).toReal) atTop
      (𝓝 (energy θ φ hφ u).toReal) :=
  (EReal.tendsto_toReal (energy_ne_top_of_preceq hfinite.1.relativePSHPreceq)
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega hfinite).ne').comp
      (SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone
        omega θ hφ huk hu0φ hanti hlim)

/-- The same actual real energy convergence holds for arbitrary decreasing
directed PSH nets, without a countable cofinality assumption. -/
theorem toReal_energy_tendsto_of_directed_antitone {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] (omega : KahlerBackground n M)
    {ui : ι → M → EReal} (hui : ∀ i, IsThetaPshPotential θ.val (ui i)) (i0 : ι)
    (hui0φ : MoreSingularOn (ui i0) φ univ) (hanti : ∀ x, Antitone fun i => ui i x)
    (hlim : ∀ x, Tendsto (fun i => ui i x) atTop (𝓝 (u x)))
    (hfinite : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun i => (energy θ φ hφ (ui i)).toReal) atTop
      (𝓝 (energy θ φ hφ u).toReal) :=
  (EReal.tendsto_toReal (energy_ne_top_of_preceq hfinite.1.relativePSHPreceq)
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega hfinite).ne').comp
      (SingularModelEnergyDecreasingNets.energy_tendsto_of_directed_antitone
        omega θ hφ hui i0 hui0φ hanti hlim)

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy
