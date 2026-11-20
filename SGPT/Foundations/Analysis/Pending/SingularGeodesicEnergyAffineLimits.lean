import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalTruncationEnergy

set_option autoImplicit false

/-! # Actual endpoint energy limits and independent scalar affine limits -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularGeodesicEnergyAffineLimits

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation MongeAmpereEnergyDecreasing

noncomputable section

/-- Actual one-sided limits identify the two constants of a real interior affine function. -/
theorem eq_chord_of_affine_and_endpoint_limits {f : ℝ → ℝ} {a b : ℝ}
    (haff : ∃ c₀ c₁ : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, f t = c₀ + c₁ * t)
    (hleft : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 a))
    (hright : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 b)) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f t = (1 - t) * a + t * b := by
  obtain ⟨c₀, c₁, h⟩ := haff
  have hc : Continuous (fun t : ℝ => c₀ + c₁ * t) := by fun_prop
  have hL : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c₀) := by
    have ht : Tendsto (fun t : ℝ => c₀ + c₁ * t) (𝓝[>] (0 : ℝ)) (𝓝 (c₀ + c₁ * 0)) :=
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have heq : (fun t : ℝ => c₀ + c₁ * t) =ᶠ[𝓝[>] (0 : ℝ)] f := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with t ht₀ ht₁
      exact (h t ⟨ht₀, ht₁⟩).symm
    simpa only [mul_zero, add_zero] using ht.congr' heq
  have hR : Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (c₀ + c₁)) := by
    have ht : Tendsto (fun t : ℝ => c₀ + c₁ * t) (𝓝[<] (1 : ℝ)) (𝓝 (c₀ + c₁ * 1)) :=
      (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have heq : (fun t : ℝ => c₀ + c₁ * t) =ᶠ[𝓝[<] (1 : ℝ)] f := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with t ht₁ ht₀
      exact (h t ⟨ht₀, ht₁⟩).symm
    simpa only [mul_one] using ht.congr' heq
  have ha := tendsto_nhds_unique hleft hL
  have hb := tendsto_nhds_unique hright hR
  intro t ht
  rw [h t ht, ha, hb]
  ring

/-- Continuity of fixed real linear combinations and genuine nontrivial-filter uniqueness transport scalar chord identities to their prescribed limits. -/
theorem eq_chord_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    {F A B : ι → ℝ} {f a b t : ℝ}
    (hF : Tendsto F l (𝓝 f)) (hA : Tendsto A l (𝓝 a)) (hB : Tendsto B l (𝓝 b))
    (heq : ∀ i, F i = (1 - t) * A i + t * B i) :
    f = (1 - t) * a + t * b := by
  have h := (hA.const_mul (1 - t)).add (hB.const_mul t)
  exact tendsto_nhds_unique hF (h.congr fun i => (heq i).symm)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Actual defining extended energies of genuine singular-reference truncations converge without a reference bound or affinity assumption. -/
theorem energy_tendsto_endpoint_truncation (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun j => energy θ φ hφ (truncation φ u j)) atTop (𝓝 (energy θ φ hφ u)) :=
  SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
      hu.1.relativePSHPreceq.2 j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
      hu.1.relativePSHPreceq.2 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)

/-- The actual finite endpoint energy makes the canonical defining-energy truncation limit real as well, with PSH, monotonicity and pole-compatible convergence produced internally. -/
theorem toReal_energy_tendsto_endpoint_truncation (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun j => (energy θ φ hφ (truncation φ u j)).toReal) atTop
      (𝓝 (energy θ φ hφ u).toReal) :=
  SingularModelFiniteRealEnergy.toReal_energy_tendsto_of_antitone omega
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
      hu.1.relativePSHPreceq.2 j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu.1.plurisubharmonic
      hu.1.relativePSHPreceq.2 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top) hu

end

end SGPT.Foundations.Analysis.Pending.SingularGeodesicEnergyAffineLimits
