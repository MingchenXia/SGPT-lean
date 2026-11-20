import SGPT.Foundations.Analysis.Pending.FiniteGeodesicSingularBarriers
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy

set_option autoImplicit false

/-!
# Actual endpoint energy control over singular models

Xia SGPT PDF0172--0173, the endpoint part of Step 2 in Proposition
4.3.3. Actual extended affine barriers and actual energy translation
give endpoint estimates and limits for same-type E1 endpoints. The
model may be singular, and dimension zero is retained. Interior
energy affinity is a separate theorem.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses FiniteGeodesicSingularBarriers

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual finite endpoint energies control the actual geodesic energy
by its affine barriers, with no boundedness of the model. -/
theorem toReal_energy_finiteGeodesic_bounds (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {C : ℝ}
    (hC₁ : ∀ x, u₁ x ≤ u₀ x + (C : EReal))
    (hC₀ : ∀ x, u₀ x ≤ u₁ x + (C : EReal))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |(energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal -
      (energy θ φ hφ u₀).toReal| ≤ C * t * modelVolume θ φ hφ ∧
    |(energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal -
      (energy θ φ hφ u₁).toReal| ≤ C * (1 - t) * modelVolume θ φ hφ := by
  have hg := relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht
  have hbar := finiteGeodesic_extended_barriers hu₀.1.plurisubharmonic
    hu₁.1.plurisubharmonic hC₁ hC₀ ht
  have hl₀ := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (hu₀.add_const omega (-C * t)) hg (fun x => (hbar x).1.1)
  have hh₀ := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    hg (hu₀.add_const omega (C * t)) (fun x => (hbar x).1.2)
  have hl₁ := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (hu₁.add_const omega (-C * (1 - t))) hg (fun x => (hbar x).2.1)
  have hh₁ := SingularModelFiniteRealEnergy.toReal_energy_mono omega
    hg (hu₁.add_const omega (C * (1 - t))) (fun x => (hbar x).2.2)
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu₀] at hl₀ hh₀
  rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega hu₁] at hl₁ hh₁
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The actual real energy of a same-type E1 geodesic tends to its initial energy. -/
theorem tendsto_toReal_energy_finiteGeodesic_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (htype : SameSingularityTypeOn u₀ u₁ univ) :
    Tendsto (fun t => (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (energy θ φ hφ u₀).toReal) := by
  obtain ⟨C, _, hC₁, hC₀⟩ := exists_nonneg_le_add_of_sameSingularityType htype
  have hid : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun t => (energy θ φ hφ u₀).toReal -
      C * t * modelVolume θ φ hφ) (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (energy θ φ hφ u₀).toReal) := by
    simpa using tendsto_const_nhds.sub ((hid.const_mul C).mul_const (modelVolume θ φ hφ))
  have hh : Tendsto (fun t => (energy θ φ hφ u₀).toReal +
      C * t * modelVolume θ φ hφ) (nhdsWithin (0 : ℝ) (Ioi 0))
      (𝓝 (energy θ φ hφ u₀).toReal) := by
    simpa using tendsto_const_nhds.add ((hid.const_mul C).mul_const (modelVolume θ φ hφ))
  have ht : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t ∈ Ioo 0 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with t ht₀ ht₁
    exact ⟨ht₀, ht₁⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh ?_ ?_
  · filter_upwards [ht] with t ht
    have h := (abs_le.mp (toReal_energy_finiteGeodesic_bounds omega hu₀ hu₁ hC₁ hC₀ ht).1).1
    linarith
  · filter_upwards [ht] with t ht
    have h := (abs_le.mp (toReal_energy_finiteGeodesic_bounds omega hu₀ hu₁ hC₁ hC₀ ht).1).2
    linarith

/-- The actual real energy of a same-type E1 geodesic tends to its terminal energy. -/
theorem tendsto_toReal_energy_finiteGeodesic_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (htype : SameSingularityTypeOn u₀ u₁ univ) :
    Tendsto (fun t => (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal)
      (nhdsWithin (1 : ℝ) (Iio 1)) (𝓝 (energy θ φ hφ u₁).toReal) := by
  obtain ⟨C, _, hC₁, hC₀⟩ := exists_nonneg_le_add_of_sameSingularityType htype
  have hid : Tendsto (fun t : ℝ => t) (nhdsWithin 1 (Iio 1)) (𝓝 1) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun _t : ℝ => (1 : ℝ)) (nhdsWithin 1 (Iio 1)) (𝓝 1) :=
    tendsto_const_nhds
  have hsmall : Tendsto (fun t => C * (1 - t) * modelVolume θ φ hφ)
      (nhdsWithin (1 : ℝ) (Iio 1)) (𝓝 (0 : ℝ)) := by
    simpa using ((hone.sub hid).const_mul C).mul_const (modelVolume θ φ hφ)
  have hl : Tendsto (fun t => (energy θ φ hφ u₁).toReal -
      C * (1 - t) * modelVolume θ φ hφ) (nhdsWithin (1 : ℝ) (Iio 1))
      (𝓝 (energy θ φ hφ u₁).toReal) := by
    simpa using tendsto_const_nhds.sub hsmall
  have hh : Tendsto (fun t => (energy θ φ hφ u₁).toReal +
      C * (1 - t) * modelVolume θ φ hφ) (nhdsWithin (1 : ℝ) (Iio 1))
      (𝓝 (energy θ φ hφ u₁).toReal) := by
    simpa using tendsto_const_nhds.add hsmall
  have ht : ∀ᶠ t : ℝ in nhdsWithin 1 (Iio 1), t ∈ Ioo 0 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with t ht₁ ht₀
    exact ⟨ht₀, ht₁⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hh ?_ ?_
  · filter_upwards [ht] with t ht
    have h := (abs_le.mp (toReal_energy_finiteGeodesic_bounds omega hu₀ hu₁ hC₁ hC₀ ht).2).1
    linarith
  · filter_upwards [ht] with t ht
    have h := (abs_le.mp (toReal_energy_finiteGeodesic_bounds omega hu₀ hu₁ hC₁ hC₀ ht).2).2
    linarith

/-- The actual extended energy has the initial endpoint limit over a singular model. -/
theorem tendsto_energy_finiteGeodesic_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (htype : SameSingularityTypeOn u₀ u₁ univ) :
    Tendsto (fun t => energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (energy θ φ hφ u₀)) := by
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₀]
  refine (EReal.tendsto_coe.2
    (tendsto_toReal_energy_finiteGeodesic_left omega hu₀ hu₁ htype)).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t ht₀ ht₁
  exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)

/-- The actual extended energy has the terminal endpoint limit over a singular model. -/
theorem tendsto_energy_finiteGeodesic_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (htype : SameSingularityTypeOn u₀ u₁ univ) :
    Tendsto (fun t => energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))
      (nhdsWithin (1 : ℝ) (Iio 1)) (𝓝 (energy θ φ hφ u₁)) := by
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₁]
  refine (EReal.tendsto_coe.2
    (tendsto_toReal_energy_finiteGeodesic_right omega hu₀ hu₁ htype)).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t ht₁ ht₀
  exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointEnergy
