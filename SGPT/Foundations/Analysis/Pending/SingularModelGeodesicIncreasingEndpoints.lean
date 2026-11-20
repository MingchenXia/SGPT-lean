import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicSupremumNets
import SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasSeparation

set_option autoImplicit false

/-!
# Actual Perron identification for increasing singular E1 endpoint nets

Xia SGPT PDF0173--0174 Proposition 4.3.4. The actual slice supremum is
produced as genuine E1 and lies below the actual endpoint-limit Perron
slice. Actual increasing endpoint and slice energies and the proved
general E1 chord give equal finite real energies. Actual ordered Darvas
distance and separation identify the two actual slices. Completion
retains both endpoints, and the actual directed limits reach the actual
completed geodesic. No affinity or path-identification certificate is an
input, no bounded reference is imposed, and no cofinal sequence is assumed.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicIncreasingEndpoints

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelGeodesicSupremumProducer
  SingularModelGeodesicSupremumNets SingularModelDarvasEnergyContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u₀ u₁ : M → EReal}
  {hφ : IsModelPotential θ φ}
  {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {ui₀ ui₁ : I → M → EReal}

/-- Actual increasing energies, actual general endpoint chords and actual Darvas separation identify the produced geodesic supremum with the actual endpoint-limit Perron slice. -/
theorem uscRegularization_iSup_finiteGeodesic_eq (omega : KahlerBackground n M)
    (hui₀ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₀ i) hφ)
    (hui₁ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₁ i) hφ)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hreg₀ : uscRegularization (⨆ i, ui₀ i) = u₀)
    (hreg₁ : uscRegularization (⨆ i, ui₁ i) = u₁)
    (hm₀ : ∀ x, Monotone fun i => ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i => ui₁ i x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    uscRegularization (⨆ i, finiteGeodesic θ.val (ui₀ i) (ui₁ i) t) =
      finiteGeodesic θ.val u₀ u₁ t := by
  have hproduced := (subgeodesic_and_finite_energy_of_regularized_endpoint_suprema
    omega hui₀ hui₁ hu₀ hu₁ hreg₀ hreg₁).2 t ht
  have hG := relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht
  have hHlim := (tendsto_at_regularized_geodesic_supremum omega hui₀ hui₁
    hu₀ hu₁ hreg₀ hreg₁ hm₀ hm₁ ht).2.1
  have hE₀ := SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
    omega hui₀ hu₀ hm₀ hreg₀
  have hE₁ := SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
    omega hui₁ hu₁ hm₁ hreg₁
  have hchord : Tendsto (fun i => (energy θ φ hφ
      (finiteGeodesic θ.val (ui₀ i) (ui₁ i) t)).toReal) atTop
      (𝓝 (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal) := by
    have h := (hE₀.const_mul (1 - t)).add (hE₁.const_mul t)
    rw [← SingularGeodesicGeneralEnergyAffinity.toReal_energy_finiteGeodesic_eq_chord
      omega hu₀ hu₁ ht] at h
    simpa only [SingularGeodesicGeneralEnergyAffinity.toReal_energy_finiteGeodesic_eq_chord
      omega (hui₀ _) (hui₁ _) ht] using h
  have he := tendsto_nhds_unique hHlim hchord
  apply SingularModelDarvasSeparation.eq_of_relativeD1_eq_zero_of_preceq
    omega hproduced.1 hG
  rw [relativeD1_eq_sub_of_le hproduced.1.1.plurisubharmonic hproduced.2, he, sub_self]

/-- Genuine endpoint completion extends the true increasing Perron identification to every point of the closed time interval. -/
theorem uscRegularization_iSup_closedSubgeodesicSlice_eq (omega : KahlerBackground n M)
    (hui₀ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₀ i) hφ)
    (hui₁ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₁ i) hφ)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hreg₀ : uscRegularization (⨆ i, ui₀ i) = u₀)
    (hreg₁ : uscRegularization (⨆ i, ui₁ i) = u₁)
    (hm₀ : ∀ x, Monotone fun i => ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i => ui₁ i x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    uscRegularization (⨆ i, closedSubgeodesicSlice
      (finiteGeodesic θ.val (ui₀ i) (ui₁ i)) (ui₀ i) (ui₁ i) t) =
      closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t := by
  by_cases h0 : t = 0
  · simpa only [h0, closedSubgeodesicSlice_zero] using hreg₀
  by_cases h1 : t = 1
  · simpa only [h1, closedSubgeodesicSlice_one] using hreg₁
  have hI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  simp only [closedSubgeodesicSlice_eq_curve hI]
  exact uscRegularization_iSup_finiteGeodesic_eq omega hui₀ hui₁ hu₀ hu₁ hreg₀ hreg₁ hm₀ hm₁ hI

private theorem endpoint_limits (omega : KahlerBackground n M)
    {ui : I → M → EReal} {u : M → EReal}
    (hui : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui i) hφ)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hreg : uscRegularization (⨆ i, ui i) = u)
    (hm : ∀ x, Monotone fun i => ui i x) :
    Tendsto (fun i => relativeD1 θ φ hφ (ui i) u) atTop (𝓝 0) ∧
    Tendsto (fun i => (energy θ φ hφ (ui i)).toReal) atTop (𝓝 (energy θ φ hφ u).toReal) ∧
    Tendsto (fun i => energy θ φ hφ (ui i)) atTop (𝓝 (energy θ φ hφ u)) := by
  have hd := relativeD1_tendsto_zero_of_directed_monotone_regularized omega hui hu hm hreg
  exact ⟨hd, toReal_energy_tendsto_of_relativeD1_tendsto_zero omega hui hu hd,
    energy_tendsto_of_relativeD1_tendsto_zero omega hui hu hd⟩

/-- Actual increasing endpoint nets converge in defining Darvas distance, real energy and defining extended energy to the actual endpoint-limit completed Perron segment on the entire closed interval. -/
theorem tendsto_closedSubgeodesicSlice_of_increasing_endpoints (omega : KahlerBackground n M)
    (hui₀ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₀ i) hφ)
    (hui₁ : ∀ i, RelativeFiniteEnergyPreceq θ φ (ui₁ i) hφ)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hreg₀ : uscRegularization (⨆ i, ui₀ i) = u₀)
    (hreg₁ : uscRegularization (⨆ i, ui₁ i) = u₁)
    (hm₀ : ∀ x, Monotone fun i => ui₀ i x)
    (hm₁ : ∀ x, Monotone fun i => ui₁ i x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => relativeD1 θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ i) (ui₁ i)) (ui₀ i) (ui₁ i) t)
      (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)) atTop (𝓝 0) ∧
    Tendsto (fun i => (energy θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ i) (ui₁ i)) (ui₀ i) (ui₁ i) t)).toReal)
      atTop (𝓝 (energy θ φ hφ
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)).toReal) ∧
    Tendsto (fun i => energy θ φ hφ
      (closedSubgeodesicSlice (finiteGeodesic θ.val (ui₀ i) (ui₁ i)) (ui₀ i) (ui₁ i) t))
      atTop (𝓝 (energy θ φ hφ
        (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t))) := by
  by_cases h0 : t = 0
  · simpa only [h0, closedSubgeodesicSlice_zero] using endpoint_limits omega hui₀ hu₀ hreg₀ hm₀
  by_cases h1 : t = 1
  · simpa only [h1, closedSubgeodesicSlice_one] using endpoint_limits omega hui₁ hu₁ hreg₁ hm₁
  have hI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have h := tendsto_at_regularized_geodesic_supremum omega hui₀ hui₁ hu₀ hu₁
    hreg₀ hreg₁ hm₀ hm₁ hI
  rw [uscRegularization_iSup_finiteGeodesic_eq omega hui₀ hui₁ hu₀ hu₁
    hreg₀ hreg₁ hm₀ hm₁ hI] at h
  simpa only [closedSubgeodesicSlice_eq_curve hI] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicIncreasingEndpoints
