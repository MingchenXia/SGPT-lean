import SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity

set_option autoImplicit false

/-!
# Actual global-volume AE increasing directed energy continuity

Xia SGPT PDF0127--0129, with actual positive-density global-volume/chart
measure transport. The natural actual global-volume AE limit produces the
regularized supremum and the actual full-preceq directed energy limit.
Arbitrary nonempty directed preorders are allowed, with no cofinal sequence,
countability, net-convergence-predicate measurability, or target-limit input.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingGlobalAE

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M}

/-- Actual global-volume AE increasing convergence of a directed genuine PSH net recovers its regularized supremum. -/
theorem uscRegularization_iSup_eq_of_directed_monotone_ae_kahlerVolume
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential θ.val (u i)) (hv : IsThetaPshPotential θ.val v)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => u i x) atTop (𝓝 (v x))) :
    uscRegularization (⨆ i, u i) = v := by
  apply SingularModelIncreasingAENetRegularizedLimit.uscRegularization_iSup_eq_of_directed_monotone_ae_chart_tendsto
    hu hv hm
  intro e
  exact KahlerVolumeChartAEEquivalence.ae_chartTarget_of_ae_kahlerVolume omega e hl

variable [ConnectedSpace M] {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual finite real model energy converges for a full-preceq increasing directed E1 net with actual global-volume AE limit. -/
theorem toReal_energy_tendsto_of_directed_monotone_ae_kahlerVolume
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => u i x) atTop (𝓝 (v x))) :
    Tendsto (fun i => (energy θ φ hφ (u i)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) :=
  SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
    omega hu hv hm (uscRegularization_iSup_eq_of_directed_monotone_ae_kahlerVolume omega
      (fun i => (hu i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

/-- Actual defining extended model energy converges for the same global-volume AE increasing directed finite-energy net. -/
theorem energy_tendsto_of_directed_monotone_ae_kahlerVolume
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => u i x) atTop (𝓝 (v x))) :
    Tendsto (fun i => energy θ φ hφ (u i)) atTop (𝓝 (energy θ φ hφ v)) :=
  SingularModelEnergyIncreasingDirectedNets.energy_tendsto_of_directed_monotone_regularized
    omega hu hv hm (uscRegularization_iSup_eq_of_directed_monotone_ae_kahlerVolume omega
      (fun i => (hu i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

/-- Actual Darvas distances tend to zero for the same global-volume AE increasing directed finite-energy net. -/
theorem relativeD1_tendsto_zero_of_directed_monotone_ae_kahlerVolume
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, RelativeFiniteEnergyPreceq θ φ (u i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => u i x)
    (hl : ∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => u i x) atTop (𝓝 (v x))) :
    Tendsto (fun i => relativeD1 θ φ hφ (u i) v) atTop (𝓝 0) :=
  SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
    omega hu hv hm (uscRegularization_iSup_eq_of_directed_monotone_ae_kahlerVolume omega
      (fun i => (hu i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingGlobalAE
