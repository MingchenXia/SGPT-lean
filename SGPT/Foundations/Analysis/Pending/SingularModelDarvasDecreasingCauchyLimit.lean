import SGPT.Foundations.Analysis.Pending.SingularModelDarvasIncreasingCauchyLimit
import SGPT.Foundations.Analysis.Pending.SingularModelUniformTruncationFullMass
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

set_option autoImplicit false

/-!
# Actual decreasing native Darvas Cauchy limits

Xia SGPT PDF0167, the decreasing half of Theorem 4.3.2. Actual native
Cauchy bounds and the actual supremum lower bound produce genuine
noncollapse of the infimum by Hartogs. Actual energy lower bounds then
produce uniform finite-type truncation bounds, actual full mass, and
actual finite energy. No finite-energy limit certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasDecreasingCauchyLimit

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace SingularModelDarvasIncreasingCauchyLimit
  SingularModelEnergyTruncation MongeAmpereEnergyDecreasing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

private theorem exists_energy_lower_of_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    CauchySeq ui → ∃ L : ℝ, ∀ i, L ≤ (energy θ φ hφ (ui i).val).toReal := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  intro hc
  obtain ⟨R, _, hR⟩ := cauchySeq_bdd hc
  refine ⟨(energy θ φ hφ (ui 0).val).toReal - R, ?_⟩
  intro i
  have hpair : relativeD1 θ φ hφ (ui i).val (ui 0).val ≤ R := (hR i 0).le
  have h := (SingularModelDarvasEnergyContinuity.abs_energy_sub_le_relativeD1
    omega (ui i).property (ui 0).property).trans hpair
  have hneg := (abs_le.mp h).1
  linarith

/-- Actual decreasing native Cauchy infima are genuine potentials, with noncollapse produced. -/
theorem isThetaPshPotential_iInf_of_antitone_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun i => (ui i).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    CauchySeq ui → IsThetaPshPotential θ.val (⨅ i, (ui i).val) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  intro hc
  obtain ⟨R, _, hR⟩ := exists_pos_bound_relativeD1_of_cauchySeq omega ui hc
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  have hreach : ∀ i, ∃ x : M, ((-(R / modelVolume θ φ hφ + 1) : ℝ) : EReal) ≤ (ui i).val x := by
    intro i
    have hs := SingularModelDarvasSupremumLowerBound.iSup_toReal_ge_neg_div_of_relativeD1_le
      omega (fun j => (ui j).property) hR i
    rw [neg_div] at hs
    have hf := ModelRaySupremum.iSup_ne_top_ne_bot (ui i).property.1.plurisubharmonic
    have hlt : ((-(R / modelVolume θ φ hφ + 1) : ℝ) : EReal) < ⨆ x, (ui i).val x := by
      rw [← EReal.coe_toReal hf.1 hf.2]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
    exact ⟨x, hx.le⟩
  have hne := ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le
    (fun i => (ui i).property.1.plurisubharmonic) hanti hreach
  have hraw := ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
    (fun i => (ui i).property.1.plurisubharmonic.1) hanti
  have heq : (⨅ i, (ui i).val) = (fun x => ⨅ i, (ui i).val x) := by
    funext x
    exact iInf_apply
  rw [heq]
  exact ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hraw hne

/-- Actual decreasing native Cauchy infima have their full mass and finite energy produced. -/
theorem relativeFiniteEnergyPreceq_iInf_of_antitone_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun i => (ui i).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    CauchySeq ui → RelativeFiniteEnergyPreceq θ φ (⨅ i, (ui i).val) hφ := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  intro hc
  let U : M → EReal := ⨅ i, (ui i).val
  have hU : IsThetaPshPotential θ.val U :=
    isThetaPshPotential_iInf_of_antitone_cauchySeq omega ui hanti hc
  obtain ⟨L, hL⟩ := exists_energy_lower_of_cauchySeq omega ui hc
  obtain ⟨R, _, hR⟩ := exists_pos_bound_relativeD1_of_cauchySeq omega ui hc
  obtain ⟨C, hC⟩ := SingularModelDarvasSupremumControl.exists_uniform_upper_bound_of_relativeD1_le
    omega (fun i => (ui i).property) hR
  let v := fun i x => (ui i).val x + ((-C : ℝ) : EReal)
  let V := fun x => U x + ((-C : ℝ) : EReal)
  have hvle (i : ℕ) : v i ≤ φ := by
    intro x
    have h := RelativePreceqStatements.le_add_const_of_moreSingularOn_of_singularityEnvelope_eq
      (ui i).property.1.plurisubharmonic hφ.envelope_eq.symm
      (ui i).property.1.relativePSHPreceq.2 (hC i) x
    have ht := add_le_add h (le_refl (((-C : ℝ) : EReal)))
    simpa only [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero] using ht
  have hvfinite (i : ℕ) : RelativeFiniteEnergyPreceq θ φ (v i) hφ :=
    (ui i).property.add_const omega (-C)
  have hV : IsThetaPshPotential θ.val V := hU.add_const (-C)
  have hVle : V ≤ φ := by
    intro x
    simpa only [V, U, iInf_apply] using
      (add_le_add (iInf_le (fun i => (ui i).val x) 0) le_rfl).trans (hvle 0 x)
  have hvanti : ∀ x, Antitone fun i => v i x := fun x i j hij =>
    add_le_add (hanti x hij) le_rfl
  have hvlim : ∀ x, Tendsto (fun i => v i x) atTop (𝓝 (V x)) := by
    intro x
    have h := tendsto_atTop_iInf (hvanti x)
    simpa only [v, V, U, iInf_apply, ThetaPshDecreasingLimit.iInf_add_coe] using h
  let L' : ℝ := L + (-C) * modelVolume θ φ hφ
  have hvenergy (i : ℕ) : L' ≤ (energy θ φ hφ (v i)).toReal := by
    rw [SingularModelFiniteRealEnergy.toReal_energy_add_const omega (ui i).property (-C)]
    exact add_le_add (hL i) le_rfl
  have hVenergy : (L' : EReal) ≤ energy θ φ hφ V := by
    rw [← SingularModelEnergyExtendedContinuity.energy_iInf_of_antitone omega θ hφ
      (fun i => (hvfinite i).1.plurisubharmonic) (MoreSingularOn.of_le fun x _ => hvle 0 x)
      hvanti hvlim]
    refine le_iInf fun i => ?_
    rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega (hvfinite i)]
    exact EReal.coe_le_coe_iff.mpr (hvenergy i)
  have hVfinite : RelativeFiniteEnergy θ φ V hφ :=
    SingularModelUniformTruncationFullMass.relativeFiniteEnergy_of_uniform_truncation_energy_lower
      (hφ := hφ) omega hV hVle (L := L') (fun j => by
        apply EReal.coe_le_coe_iff.mp
        have hm : energy θ φ hφ V ≤ energy θ φ hφ (truncation φ V j) :=
          energy_mono_of_le (le_truncation φ V j)
        rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
          (relativeEInfinity_truncation hφ.plurisubharmonic hV
            (MoreSingularOn.of_le fun x _ => hVle x) j)] at hm
        exact hVenergy.trans hm)
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy hVfinite)

/-- Actual decreasing native Cauchy sequences converge to their produced actual finite-energy infimum. -/
theorem tendsto_iInf_of_antitone_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ)
    (hanti : ∀ x, Antitone fun i => (ui i).val x) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    CauchySeq ui → ∃ hU : RelativeFiniteEnergyPreceq θ φ (⨅ i, (ui i).val) hφ,
      Tendsto ui atTop (𝓝 (⟨⨅ i, (ui i).val, hU⟩ : ModelFiniteEnergyPotential θ φ hφ)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hc
  have hU := relativeFiniteEnergyPreceq_iInf_of_antitone_cauchySeq omega ui hanti hc
  refine ⟨hU, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  exact SingularModelDarvasBasic.relativeD1_tendsto_zero_of_antitone omega
    (fun i => (ui i).property) hU hanti
    (fun x => by simpa only [iInf_apply] using tendsto_atTop_iInf (hanti x))

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasDecreasingCauchyLimit
