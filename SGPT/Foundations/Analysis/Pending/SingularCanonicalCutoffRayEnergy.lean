import SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRay
import SGPT.Foundations.Analysis.Pending.SingularModelScaledCutoffEnergy

set_option autoImplicit false

/-! # Actual canonical cutoff-ray radial energy from genuine mixed mass deficits -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRayEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance RelativePreceqClasses
  RelativePreceqRays SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages
  SingularCanonicalCutoffSlices SingularCanonicalCutoffTailLimits SingularCanonicalCutoffRay

noncomputable section

private theorem tendsto_atTop_of_gt_subtype {α : Type*} {f : ℝ → α}
    {l : Filter α} {B : ℝ}
    (h : Tendsto (fun C : {C : ℝ // B < C} => f C.val) atTop l) :
    Tendsto f atTop l := by
  let : Nonempty {C : ℝ // B < C} := ⟨⟨B + 1, by linarith⟩⟩
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  obtain ⟨C, hC⟩ := Filter.eventually_atTop.1 (h s hs)
  exact Filter.eventually_atTop.2 ⟨C.val, fun c hcc =>
    hC ⟨c, C.property.trans_le hcc⟩ hcc⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u : M → EReal}

omit [ConnectedSpace M] in
private theorem energy_model_eq_zero (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) : energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- Genuine actual finite-type endpoint inclusions and the established general closed E1 chord produce the exact closed cutoff-stage energy. -/
theorem toReal_energy_cutoffStage_eq_mul (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ)
    {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    (energy θ φ hφ (cutoffStage θ φ u C s)).toReal =
      (s / C) * (energy θ φ hφ (realCutoff φ u C)).toReal := by
  have h0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeFiniteEnergyPreceq θ φ (realCutoff φ u C) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_realCutoff hφ.plurisubharmonic hu
        (MoreSingularOn.of_le fun x _ => hup x) C)
  have h := SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega h0 h1 ⟨div_nonneg hs.1 hC.le, (div_le_one hC).mpr hs.2⟩
  simpa only [cutoffStage, energy_model_eq_zero omega hφ, EReal.toReal_zero,
    mul_zero, zero_add] using h

/-- The actual stage energy limit internally produces unrestricted real-parameter convergence of the genuine scaled cutoff energies. -/
theorem tendsto_toReal_cutoff_energy_div (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) :
    Tendsto (fun C : ℝ => (energy θ φ hφ (realCutoff φ u C)).toReal / C) atTop
      (𝓝 (energy θ φ hφ (cutoffSlice θ φ u 1)).toReal) := by
  have hlim := (tendsto_cutoffStage_common_tail omega hφ hu hup
    (s := 1) (B := 1) zero_le_one le_rfl).2.1
  have hC (C : {C : ℝ // (1 : ℝ) < C}) : 0 < C.val := zero_lt_one.trans C.property
  have hs (C : {C : ℝ // (1 : ℝ) < C}) : (1 : ℝ) ∈ Icc (0 : ℝ) C.val :=
    ⟨zero_le_one, C.property.le⟩
  apply tendsto_atTop_of_gt_subtype (B := 1)
  simpa only [toReal_energy_cutoffStage_eq_mul omega hφ hu hup (hC _) (hs _),
    one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hlim

/-- The genuine constructed source ray, true increasing stage energies and the actual real-cutoff mass-deficit limit internally identify its defining extended radial energy. -/
theorem radialEnergy_cutoffSlice_eq_mixed_mass_deficit (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) :
    RelativeGeodesicRays.radialEnergy θ φ hφ (cutoffSlice θ φ u) =
      (((∑ k : Fin (n + 1),
        ((endpointMixedMass θ φ u hφ.plurisubharmonic hu k).toReal -
          (DiagonalMass.diagonalPotentialMass θ φ hφ.plurisubharmonic).toReal)) /
            (n + 1 : ℝ) : ℝ) : EReal) := by
  have he := tendsto_nhds_unique (tendsto_toReal_cutoff_energy_div omega hφ hu hup)
    (SingularModelScaledCutoffEnergy.tendsto_scaled_toReal_energy_realCutoff omega hφ hu hup)
  have hR := isBoundedRayFromModel_cutoffSlice omega hφ hu hup
  have hfinite : IsFiniteEnergyRayFromModel θ φ hφ (cutoffSlice θ φ u) :=
    ⟨⟨hR.1.1, fun t ht =>
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hR.1.2 t ht.le)⟩, hR.2⟩
  have h1 : RelativeFiniteEnergyPreceq θ φ (cutoffSlice θ φ u 1) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (hR.1.2 1 zero_le_one)
  rw [SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hfinite,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega h1]
  exact congrArg (fun x : ℝ => (x : EReal)) he

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalCutoffRayEnergy
