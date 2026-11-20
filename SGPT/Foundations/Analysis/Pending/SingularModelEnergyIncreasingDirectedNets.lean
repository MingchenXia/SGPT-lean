import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingPreceq
import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAENetRegularizedLimit

set_option autoImplicit false

/-!
# Actual increasing E1 energy continuity for arbitrary directed nets

Xia SGPT PDF0128--0129. Actual Choquet extraction preserves a regularized
supremum, not cofinality of the original index set. Actual sequence energy
continuity and energy order then produce convergence of the full directed
net. Chart Haar-AE limits are recovered by the actual PSH order bridge.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingDirectedNets

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses SingularModelIncreasingAENetRegularizedLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual real energy converges for every increasing directed E1 net at
its genuine regularized supremum, with no countable cofinality premise. -/
theorem toReal_energy_tendsto_of_directed_monotone_regularized
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hreg : uscRegularization (⨆ i, u i) = v) :
    Tendsto (fun i => (energy θ φ hφ (u i)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) := by
  classical
  have huv : ∀ i, u i ≤ v := fun i x =>
    (le_iSup (fun k => u k) i x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  obtain ⟨s, hs, _, hsup⟩ :=
    IncreasingMixedDirectedNets.exists_monotone_sequence_uscRegularization_iSup_eq
      (K := Unit) (Classical.arbitrary I) (u := fun i (_ : Unit) => u i)
      (fun _ i j hij x => hm x hij)
  have hsreg : uscRegularization (⨆ k, u (s k)) = v := by
    rw [hsup (), hreg]
  have hseq := SingularModelEnergyIncreasingPreceq.toReal_energy_tendsto_of_monotone_regularized
    omega (fun k => hu (s k)) hv (fun x k l hkl => hm x (hs hkl)) hsreg
  have hemono : Monotone fun i => (energy θ φ hφ (u i)).toReal :=
    fun i j hij => SingularModelFiniteRealEnergy.toReal_energy_mono omega
      (hu i) (hu j) (fun x => hm x hij)
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨k, hk⟩ := (hseq.eventually_const_lt ha).exists
    filter_upwards [eventually_ge_atTop (s k)] with i hki
    exact hk.trans_le (hemono hki)
  · intro b hb
    exact Eventually.of_forall fun i => lt_of_le_of_lt
      (SingularModelFiniteRealEnergy.toReal_energy_mono omega (hu i) hv (huv i)) hb

/-- Actual finite-energy realification transfers this arbitrary directed
regularized convergence to the defining extended energies. -/
theorem energy_tendsto_of_directed_monotone_regularized
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hreg : uscRegularization (⨆ i, u i) = v) :
    Tendsto (fun i => energy θ φ hφ (u i)) atTop (𝓝 (energy θ φ hφ v)) := by
  have h := EReal.tendsto_coe.mpr
    (toReal_energy_tendsto_of_directed_monotone_regularized omega hu hv hm hreg)
  have he (i : I) := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hu i)
  have hev := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hv
  simpa only [he, hev] using h

/-- The same actual real energy continuity holds for arbitrary increasing
directed E1 nets with genuine chart Haar-AE limits. -/
theorem toReal_energy_tendsto_of_directed_monotone_ae_chart
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun i => chartFunction (u i) e z) atTop (𝓝 (chartFunction v e z))) :
    Tendsto (fun i => (energy θ φ hφ (u i)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) :=
  toReal_energy_tendsto_of_directed_monotone_regularized omega hu hv hm
    (uscRegularization_iSup_eq_of_directed_monotone_ae_chart_tendsto
      (fun i => (hu i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

/-- The actual extended model energies converge for the same arbitrary
directed chart Haar-AE increasing finite-energy net. -/
theorem energy_tendsto_of_directed_monotone_ae_chart
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun i => chartFunction (u i) e z) atTop (𝓝 (chartFunction v e z))) :
    Tendsto (fun i => energy θ φ hφ (u i)) atTop (𝓝 (energy θ φ hφ v)) :=
  energy_tendsto_of_directed_monotone_regularized omega hu hv hm
    (uscRegularization_iSup_eq_of_directed_monotone_ae_chart_tendsto
      (fun i => (hu i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingDirectedNets
