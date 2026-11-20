import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinRay
import SGPT.Foundations.Analysis.Pending.SingularModelOriginRayEnergy

set_option autoImplicit false

/-! # The genuine terminal-maximum limit giving the actual bounded join's radial energy -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativePreceqRays SingularBoundedRayJoinStages
  SingularBoundedRayJoinStageOrder SingularBoundedRayJoinSlices
  SingularBoundedRayJoinCommonTail SingularBoundedRayJoinRay

noncomputable section

private theorem tendsto_atTop_of_gt_subtype {α : Type*} {f : ℝ → α}
    {l : Filter α} {B : ℝ}
    (h : Tendsto (fun T : {T : ℝ // B < T} => f T.val) atTop l) :
    Tendsto f atTop l := by
  let : Nonempty {T : ℝ // B < T} := ⟨⟨B + 1, by linarith⟩⟩
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (h s hs)
  exact Filter.eventually_atTop.2 ⟨T.val, fun t htt =>
    hT ⟨t, T.property.trans_le htt⟩ htt⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ : M → EReal} {hφ : IsModelPotential θ φ} {ℓ ℓ' : ℝ → M → EReal}

omit [ConnectedSpace M] in
private theorem energy_model_eq_zero (omega : KahlerBackground n M) :
    energy θ φ hφ φ = 0 := by
  rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
    ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- The actual general E1 chord internally gives the terminal-maximum energy formula on the entire genuine closed join stage. -/
theorem toReal_energy_joinStage_eq_mul (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ')
    {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc (0 : ℝ) T) :
    (energy θ φ hφ (joinStage θ φ ℓ ℓ' T s)).toReal =
      (s / T) * (energy θ φ hφ (fun x => max (ℓ T x) (ℓ' T x))).toReal := by
  have h0 : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have h1 : RelativeFiniteEnergyPreceq θ φ (fun x => max (ℓ T x) (ℓ' T x)) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_max (hℓ.1.2 T hT.le) (hℓ'.1.2 T hT.le))
  have h := SingularGeodesicGeneralEnergyAffinity.toReal_energy_closedSubgeodesicSlice_eq_chord
    omega h0 h1 ⟨div_nonneg hs.1 hT.le, (div_le_one hT).mpr hs.2⟩
  simpa only [joinStage, energy_model_eq_zero omega, EReal.toReal_zero,
    mul_zero, zero_add] using h

/-- The genuine directed increasing stage energies internally produce unrestricted real-time convergence of the actual terminal-maximum energy quotients. -/
theorem tendsto_toReal_terminal_max_energy_div (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    Tendsto (fun T : ℝ => T⁻¹ *
      (energy θ φ hφ (fun x => max (ℓ T x) (ℓ' T x))).toReal) atTop
      (𝓝 (energy θ φ hφ (joinSlice θ φ ℓ ℓ' 1)).toReal) := by
  let I := {T : ℝ // (1 : ℝ) < T}
  let : Nonempty I := ⟨⟨2, by norm_num⟩⟩
  have hT (T : I) : 0 < T.val := zero_lt_one.trans T.property
  have hs (T : I) : (1 : ℝ) ∈ Icc (0 : ℝ) T.val :=
    ⟨zero_le_one, T.property.le⟩
  have hui (T : I) : RelativeFiniteEnergyPreceq θ φ (joinStage θ φ ℓ ℓ' T.val 1) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinStage omega hℓ hℓ' (hT T) (hs T))
  have hu : RelativeFiniteEnergyPreceq θ φ (joinSlice θ φ ℓ ℓ' 1) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinSlice omega hℓ hℓ' 1)
  have hm : ∀ x, Monotone fun T : I => joinStage θ φ ℓ ℓ' T.val 1 x := by
    intro x T S hTS
    exact joinStage_mono_terminalTime omega hℓ hℓ' (hT T) hTS (hs T) x
  have hreg : uscRegularization (⨆ T : I, joinStage θ φ ℓ ℓ' T.val 1) =
      joinSlice θ φ ℓ ℓ' 1 :=
    (joinSlice_eq_regularized_common_tail omega hℓ hℓ' zero_le_one le_rfl).symm
  have hlim :=
    SingularModelEnergyIncreasingDirectedNets.toReal_energy_tendsto_of_directed_monotone_regularized
      omega hui hu hm hreg
  apply tendsto_atTop_of_gt_subtype (B := 1)
  simpa only [toReal_energy_joinStage_eq_mul omega hℓ hℓ' (hT _) (hs _),
    one_div] using hlim

/-- Actual finite-energy realification gives convergence of the defining extended terminal-maximum energy quotients, including an arbitrarily singular model. -/
theorem tendsto_terminal_max_energy_div (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    Tendsto (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
      energy θ φ hφ (fun x => max (ℓ T x) (ℓ' T x))) atTop
      (𝓝 (energy θ φ hφ (joinSlice θ φ ℓ ℓ' 1))) := by
  have hu : RelativeFiniteEnergyPreceq θ φ (joinSlice θ φ ℓ ℓ' 1) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_joinSlice omega hℓ hℓ' 1)
  have h := EReal.tendsto_coe.mpr (tendsto_toReal_terminal_max_energy_div omega hℓ hℓ')
  rw [SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hmax : RelativeFiniteEnergyPreceq θ φ (fun x => max (ℓ T x) (ℓ' T x)) hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (relativeEInfinity_max (hℓ.1.2 T hT.le) (hℓ'.1.2 T hT.le))
  rw [EReal.coe_mul, SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hmax]

/-- The genuine constructed bounded join internally has the exact original radial-energy limit formula, using the existing defining extended-real limit reader. -/
theorem radialEnergy_joinSlice_eq_limUnder_terminal_max (omega : KahlerBackground n M)
    (hℓ : IsBoundedRayFromModel θ φ hφ ℓ)
    (hℓ' : IsBoundedRayFromModel θ φ hφ ℓ') :
    RelativeGeodesicRays.radialEnergy θ φ hφ (joinSlice θ φ ℓ ℓ') =
      limUnder atTop (fun T : ℝ => ((T⁻¹ : ℝ) : EReal) *
        energy θ φ hφ (fun x => max (ℓ T x) (ℓ' T x))) := by
  have hJ := isBoundedRayFromModel_joinSlice omega hℓ hℓ'
  have hfinite : IsFiniteEnergyRayFromModel θ φ hφ (joinSlice θ φ ℓ ℓ') :=
    ⟨⟨hJ.1.1, fun t ht =>
      RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
        (hJ.1.2 t ht.le)⟩, hJ.2⟩
  rw [SingularModelOriginRayEnergy.radialEnergy_eq_energy_one omega hfinite]
  exact (tendsto_terminal_max_energy_div omega hℓ hℓ').limUnder_eq.symm

end

end SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinEnergy
