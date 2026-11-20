import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingDirectedNets

set_option autoImplicit false

/-!
# Actual Darvas control of energy and increasing limits

Xia SGPT PDF0160--0161 and PDF0169 Theorem 4.3.3. An independent
elementary one-Lipschitz consequence of the actual energy/rooftop formula
gives real and extended energy continuity under actual Darvas convergence.
PDF0128--0129 actual increasing energy gives increasing directed d1 limits.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
open RelativePreceqClasses SingularModelIncreasingAENetRegularizedLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual finite-energy rooftop membership and actual energy order give
the one-Lipschitz bound for the defining real energy on the full E1 class. -/
theorem abs_energy_sub_le_relativeD1 (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    |(energy θ φ hφ u).toReal - (energy θ φ hφ v).toReal| ≤ relativeD1 θ φ hφ u v := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hru := SingularModelFiniteRealEnergy.toReal_energy_mono omega hr hu
    (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic)
  have hrv := SingularModelFiniteRealEnergy.toReal_energy_mono omega hr hv
    (rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic)
  rw [relativeD1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual Darvas convergence along any filter implies convergence of the
actual real energy; the actual rooftop and its finite energy are produced. -/
theorem toReal_energy_tendsto_of_relativeD1_tendsto_zero {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hd : Tendsto (fun i => relativeD1 θ φ hφ (ui i) v) F (𝓝 0)) :
    Tendsto (fun i => (energy θ φ hφ (ui i)).toReal) F
      (𝓝 (energy θ φ hφ v).toReal) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
    (fun _ => abs_nonneg _) (fun i => abs_energy_sub_le_relativeD1 omega (hui i) hv)

/-- Actual finite-energy realification gives extended model-energy
convergence under the same natural Darvas convergence input. -/
theorem energy_tendsto_of_relativeD1_tendsto_zero {I : Type*} {F : Filter I}
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hd : Tendsto (fun i => relativeD1 θ φ hφ (ui i) v) F (𝓝 0)) :
    Tendsto (fun i => energy θ φ hφ (ui i)) F (𝓝 (energy θ φ hφ v)) := by
  have h := EReal.tendsto_coe.mpr
    (toReal_energy_tendsto_of_relativeD1_tendsto_zero omega hui hv hd)
  have he (i : I) := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hui i)
  have hev := SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hv
  simpa only [he, hev] using h

/-- Actual increasing directed finite-energy nets converge in actual
Darvas distance to their genuine regularized supremum. -/
theorem relativeD1_tendsto_zero_of_directed_monotone_regularized
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => ui i x)
    (hreg : uscRegularization (⨆ i, ui i) = v) :
    Tendsto (fun i => relativeD1 θ φ hφ (ui i) v) atTop (𝓝 0) := by
  have huv : ∀ i, ui i ≤ v := fun i x =>
    (le_iSup (fun k => ui k) i x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  have hid (i : I) : relativeD1 θ φ hφ (ui i) v =
      (energy θ φ hφ v).toReal - (energy θ φ hφ (ui i)).toReal :=
    relativeD1_eq_sub_of_le (hui i).1.plurisubharmonic (huv i)
  have h := SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
    omega hui hv hm hreg
  simpa only [hid, sub_self] using
    (tendsto_const_nhds (x := (energy θ φ hφ v).toReal)).sub h

/-- The actual directed chart Haar-AE increasing limit also gives actual
Darvas distance convergence, without a distance-limit premise. -/
theorem relativeD1_tendsto_zero_of_directed_monotone_ae_chart
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (hm : ∀ x, Monotone fun i => ui i x)
    (hl : ∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
      Tendsto (fun i => chartFunction (ui i) e z) atTop (𝓝 (chartFunction v e z))) :
    Tendsto (fun i => relativeD1 θ φ hφ (ui i) v) atTop (𝓝 0) :=
  relativeD1_tendsto_zero_of_directed_monotone_regularized omega hui hv hm
    (uscRegularization_iSup_eq_of_directed_monotone_ae_chart_tendsto
      (fun i => (hui i).1.plurisubharmonic) hv.1.plurisubharmonic hm hl)

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasEnergyContinuity
