import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy

set_option autoImplicit false

/-!
# Basic actual Darvas functional for arbitrarily singular model references

Xia SGPT PDF0160--0161, Definition 4.3.1 and the elementary energy identities,
with PDF0118 translation and PDF0120--0121 decreasing energy continuity.
Actual finite-energy rooftop closure produces the genuine finite-energy
rooftop. The actual energy functional is nonnegative, invariant under common
finite translations, and converges to zero for decreasing sequences/nets.
The contraction, separation, and triangle theorem remain separate obligations.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelFiniteRealEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- The actual Darvas energy functional is nonnegative on the genuine
finite-energy singularity-order class, with no boundedness of the model. -/
theorem relativeD1_nonneg [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    0 ≤ relativeD1 θ φ hφ u v := by
  have hw := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have h1 := SingularModelFiniteRealEnergy.toReal_energy_mono omega hw hu
    (rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic)
  have h2 := SingularModelFiniteRealEnergy.toReal_energy_mono omega hw hv
    (rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic)
  rw [relativeD1]
  linarith

/-- Actual rooftop covariance and actual finite energy translations cancel
the common model-volume correction in the Darvas functional. -/
theorem relativeD1_add_const [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ)
    (c : ℝ) :
    relativeD1 θ φ hφ (fun x => u x + (c : EReal)) (fun x => v x + (c : EReal)) =
      relativeD1 θ φ hφ u v := by
  rw [relativeD1, relativeD1, rooftop_add_const,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega hv,
    SingularModelFiniteRealEnergy.toReal_energy_add_const omega
      (relativeFiniteEnergyPreceq_rooftop omega hu hv)]
  ring

/-- Genuine decreasing finite-energy sequences converge to their
finite-energy limit in the actual Darvas functional for a singular model. -/
theorem relativeD1_tendsto_zero_of_antitone (omega : KahlerBackground n M)
    {uk : ℕ → M → EReal} (huk : ∀ k, RelativeFiniteEnergyPreceq θ φ (uk k) hφ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    Tendsto (fun k => relativeD1 θ φ hφ (uk k) u) atTop (𝓝 0) := by
  have hconv := toReal_energy_tendsto_of_antitone omega
    (fun k => (huk k).1.plurisubharmonic) (huk 0).1.relativePSHPreceq.2 hanti hlim hu
  have hid (k : ℕ) : relativeD1 θ φ hφ (uk k) u =
      (energy θ φ hφ (uk k)).toReal - (energy θ φ hφ u).toReal := by
    rw [relativeD1_comm θ φ hφ]
    exact relativeD1_eq_sub_of_le hu.1.plurisubharmonic
      (fun x => (hanti x).le_of_tendsto (hlim x) k)
  simpa only [hid, sub_self] using
    hconv.sub (tendsto_const_nhds (x := (energy θ φ hφ u).toReal))

/-- The actual Darvas functional also converges to zero for general
decreasing directed nets of genuine finite-energy potentials. -/
theorem relativeD1_tendsto_zero_of_directed_antitone {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] (omega : KahlerBackground n M)
    {ui : ι → M → EReal} (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (i0 : ι)
    (hanti : ∀ x, Antitone fun i => ui i x)
    (hlim : ∀ x, Tendsto (fun i => ui i x) atTop (𝓝 (u x))) :
    Tendsto (fun i => relativeD1 θ φ hφ (ui i) u) atTop (𝓝 0) := by
  have hconv := toReal_energy_tendsto_of_directed_antitone omega
    (fun i => (hui i).1.plurisubharmonic) i0 (hui i0).1.relativePSHPreceq.2 hanti hlim hu
  have hid (i : ι) : relativeD1 θ φ hφ (ui i) u =
      (energy θ φ hφ (ui i)).toReal - (energy θ φ hφ u).toReal := by
    rw [relativeD1_comm θ φ hφ]
    exact relativeD1_eq_sub_of_le hu.1.plurisubharmonic
      (fun x => (hanti x).le_of_tendsto (hlim x) i)
  simpa only [hid, sub_self] using
    hconv.sub (tendsto_const_nhds (x := (energy θ φ hφ u).toReal))

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic
