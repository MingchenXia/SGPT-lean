import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedE1
import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingAERegularizedLimit

set_option autoImplicit false

/-!
# Actual increasing energy on the full singularity-order E1 class

Xia SGPT PDF0127--0128 and the chart-AE bridge from PDF0025. A common
finite translation produces actual normalized E1 membership; actual energy
translation then recovers full-domain real and extended convergence.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingPreceq

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses SingularModelIncreasingAERegularizedLimit

noncomputable section

private theorem regularization_iSup_add_const {X : Type*} [TopologicalSpace X]
    (u : ℕ → X → EReal) (c : ℝ) :
    uscRegularization (⨆ j, fun x => u j x + (c : EReal)) =
      fun x => uscRegularization (⨆ j, u j) x + (c : EReal) := by
  have hsup : (⨆ j, fun x => u j x + (c : EReal)) =
      fun x => (⨆ j, u j) x + (c : EReal) := by
    funext x
    simp only [iSup_apply]
    exact (NegligibleSetNotCharged.iSup_add_coe (fun j => u j x) c).symm
  rw [hsup, uscRegularization_add_coe_const]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual common finite translation extends increasing regularized real
energy continuity to the entire singularity-order E1 domain. -/
theorem toReal_energy_tendsto_of_monotone_regularized (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => (energy θ φ hφ (u j)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) := by
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  obtain ⟨C, hC⟩ := hv.1.relativePSHPreceq.2
  have hvN : (fun x => v x + ((-C : ℝ) : EReal)) ≤ φ := by
    intro x
    calc
      _ ≤ (φ x + (C : EReal)) + ((-C : ℝ) : EReal) :=
        add_le_add (hC x (mem_univ x)) le_rfl
      _ = φ x := by rw [add_assoc, ← EReal.coe_add]; simp
  have huN : ∀ j, (fun x => u j x + ((-C : ℝ) : EReal)) ≤ φ :=
    fun j x => (add_le_add (huv j x) le_rfl).trans (hvN x)
  have hmN : ∀ x, Monotone fun j => u j x + ((-C : ℝ) : EReal) :=
    fun x j k hjk => add_le_add (hm x hjk) le_rfl
  have hregN : uscRegularization (⨆ j, fun x => u j x + ((-C : ℝ) : EReal)) =
      fun x => v x + ((-C : ℝ) : EReal) := by
    rw [regularization_iSup_add_const, hreg]
  have h := SingularModelEnergyIncreasingRegularizedE1.toReal_energy_tendsto_of_monotone_regularized
    omega (fun j => (hu j).relativeFiniteEnergy_add omega (huN j))
    (hv.relativeFiniteEnergy_add omega hvN) hmN hregN
  have he (j : ℕ) := SingularModelFiniteRealEnergy.toReal_energy_add_const omega (hu j) (-C)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv (-C)] at h
  simp only [he] at h
  simpa only [add_sub_cancel_right] using h.sub_const ((-C) * modelVolume θ φ hφ)

/-- The actual extended energy convergence in the same full E1 domain is
produced by finite-energy realification, without normalized potentials. -/
theorem energy_tendsto_of_monotone_regularized (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => energy θ φ hφ (u j)) atTop (𝓝 (energy θ φ hφ v)) := by
  have h := EReal.tendsto_coe.mpr
    (toReal_energy_tendsto_of_monotone_regularized omega hu hv hm hreg)
  have he (j : ℕ) := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hu j)
  have hev := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hv
  simpa only [he, hev] using h

/-- Actual chart Haar-AE increasing convergence produces real energy
convergence on the full singularity-order E1 class. -/
theorem toReal_energy_tendsto_of_monotone_ae_chart (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun j => chartFunction (u j) e z) atTop (𝓝 (chartFunction v e z))) :
    Tendsto (fun j => (energy θ φ hφ (u j)).toReal) atTop
      (𝓝 (energy θ φ hφ v).toReal) :=
  toReal_energy_tendsto_of_monotone_regularized omega hu hv hm
    (uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      (fun j => (hu j).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

/-- The defining extended model energies have the same chart Haar-AE
increasing continuity on the full singularity-order E1 class. -/
theorem energy_tendsto_of_monotone_ae_chart (omega : KahlerBackground n M)
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun j => chartFunction (u j) e z) atTop (𝓝 (chartFunction v e z))) :
    Tendsto (fun j => energy θ φ hφ (u j)) atTop (𝓝 (energy θ φ hφ v)) :=
  energy_tendsto_of_monotone_regularized omega hu hv hm
    (uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      (fun j => (hu j).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingPreceq
