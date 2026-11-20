import SGPT.Foundations.Analysis.Pending.SingularModelEnergyFiniteDiamond
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyPreceq

set_option autoImplicit false

/-!
# Actual extended energy diamond inequality for arbitrary singular models

Xia SGPT PDF0137, Corollary 3.1.7, equation (3.57). Actual same-type
truncation diamonds pass to the defining extended energy. The genuine
rooftop lower barrier produces nondegeneracy of the decreasing rooftop
infimum, which actual competitor maximality identifies with the endpoint
rooftop. No boundedness, differentiability, or diamond premise is used.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedDiamond

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses MongeAmpereEnergyDecreasing SingularModelEnergyTruncation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual extended energy satisfies the diamond inequality for an arbitrary
singular model and genuine singularity-order endpoints with a genuine rooftop. -/
theorem energy_add_le_max_add_rooftop (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativePSHPreceq θ φ u)
    (hv : RelativePSHPreceq θ φ v) (hr : IsThetaPshPotential θ.val (rooftop θ u v)) :
    energy θ φ hφ u + energy θ φ hφ v ≤
      energy θ φ hφ (fun x => max (u x) (v x)) + energy θ φ hφ (rooftop θ u v) := by
  let : Nonempty M := by
    rcases isEmpty_or_nonempty M with hM | hM
    · have hpos := hφ.positive_mass
      simp only [DiagonalMass.diagonalPotentialMass, Set.eq_empty_of_isEmpty,
        measure_empty] at hpos
      exact (lt_irrefl 0 hpos).elim
    · exact hM
  let uj : ℕ → M → EReal := truncation φ u
  let vj : ℕ → M → EReal := truncation φ v
  have huj (j : ℕ) : RelativeEInfinity θ φ (uj j) :=
    relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 j
  have hvj (j : ℕ) : RelativeEInfinity θ φ (vj j) :=
    relativeEInfinity_truncation hφ.plurisubharmonic hv.1 hv.2 j
  let rj : ℕ → M → EReal := fun j => rooftop θ (uj j) (vj j)
  have hrj (j : ℕ) : RelativeEInfinity θ φ (rj j) :=
    SingularModelEnergyFiniteDiamond.relativeEInfinity_rooftop hφ.plurisubharmonic (huj j) (hvj j)
  have hm : RelativePSHPreceq θ φ (fun x => max (u x) (v x)) :=
    ⟨IsThetaPshPotential.max hu.1 hv.1, DominationPrincipleReduction.moreSingularOn_max hu.2 hv.2⟩
  have hrφ : RelativePSHPreceq θ φ (rooftop θ u v) :=
    ⟨hr, (MoreSingularOn.of_le fun x _ => rooftop_le_left hu.1 hv.1 x).trans hu.2⟩
  have hmj (j : ℕ) : IsThetaPshPotential θ.val (fun x => max (uj j x) (vj j x)) :=
    IsThetaPshPotential.max (huj j).1 (hvj j).1
  have hk (j : ℕ) :
      ((relativeEnergyOfMinimalType θ φ (uj j) hφ.plurisubharmonic (huj j).1 +
        relativeEnergyOfMinimalType θ φ (vj j) hφ.plurisubharmonic (hvj j).1 : ℝ) : EReal) ≤
      ((relativeEnergyOfMinimalType θ φ _ hφ.plurisubharmonic (hmj j) +
        relativeEnergyOfMinimalType θ φ (rj j) hφ.plurisubharmonic (hrj j).1 : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr
      (SingularModelEnergyFiniteDiamond.relativeEnergyOfMinimalType_add_le_max_add_rooftop
        omega θ hφ.plurisubharmonic (huj j) (hvj j))
  have hTu := energy_tendsto_truncation omega θ hφ hu.1 hu.2
  have hTv := energy_tendsto_truncation omega θ hφ hv.1 hv.2
  have hTm := energy_tendsto_truncation omega θ hφ hm.1 hm.2
  have hTm' : Tendsto (fun j => (relativeEnergyOfMinimalType θ φ _
      hφ.plurisubharmonic (hmj j) : EReal)) atTop
      (𝓝 (energy θ φ hφ (fun x => max (u x) (v x)))) := by
    refine hTm.congr fun j => ?_
    rw [RelativeEnergyDiamond.relativeEnergyOfMinimalType_congr
      (RelativeEnergyDiamond.truncation_max φ u v j).symm]
  have hanti : ∀ x, Antitone fun j => rj j x := fun x i j hij =>
    rooftop_mono (truncation_antitone φ u · hij) (truncation_antitone φ v · hij) x
  have hrle (j : ℕ) : rooftop θ u v ≤ rj j :=
    rooftop_mono (le_truncation φ u j) (le_truncation φ v j)
  have hrjle (j : ℕ) : rj j ≤ uj j ∧ rj j ≤ vj j :=
    ⟨rooftop_le_left (huj j).1 (hvj j).1, rooftop_le_right (huj j).1 (hvj j).1⟩
  have hinf : (fun x => ⨅ j, rj j x) = rooftop θ u v := by
    refine le_antisymm ?_ fun x => le_iInf fun j => hrle j x
    have hp : ThetaPlurisubharmonic θ.val (fun x => ⨅ j, rj j x) :=
      ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone
        (fun j => (hrj j).1.1) hanti
    have hg : IsThetaPshPotential θ.val (fun x => ⨅ j, rj j x) :=
      ⟨hp, hr.2.mono fun x => le_iInf fun j => hrle j x⟩
    refine le_rooftopEnvelope hg (quasiEverywhere_of_forall fun x => le_min ?_ ?_)
    · exact ge_of_tendsto (tendsto_truncation_of_ne_top
        hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
        (Eventually.of_forall fun j => (iInf_le _ j).trans ((hrjle j).1 x))
    · exact ge_of_tendsto (tendsto_truncation_of_ne_top
        hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
        (Eventually.of_forall fun j => (iInf_le _ j).trans ((hrjle j).2 x))
  have hlimr : ∀ x, Tendsto (fun j => rj j x) atTop (𝓝 (rooftop θ u v x)) := by
    intro x
    rw [← congrFun hinf x]
    exact tendsto_atTop_iInf (hanti x)
  have hTr := SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone
    omega θ hφ (fun j => (hrj j).1) (hrj 0).2.1 hanti hlimr
  have hTr' : Tendsto (fun j => (relativeEnergyOfMinimalType θ φ (rj j)
      hφ.plurisubharmonic (hrj j).1 : EReal)) atTop (𝓝 (energy θ φ hφ (rooftop θ u v))) := by
    simpa only [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ (hrj _)]
      using hTr
  have hL := RelativeEnergyDiamond.tendsto_add_of_ne_top hTu hTv
    (energy_ne_top_of_preceq hu) (energy_ne_top_of_preceq hv)
  have hR := RelativeEnergyDiamond.tendsto_add_of_ne_top hTm' hTr'
    (energy_ne_top_of_preceq hm) (energy_ne_top_of_preceq hrφ)
  refine le_of_tendsto_of_tendsto' hL hR fun j => ?_
  simpa only [EReal.coe_add] using hk j

/-- On the actual finite-energy class the genuine rooftop is produced by
closure, and the actual diamond inequality holds between the real energies. -/
theorem toReal_energy_add_le_max_add_rooftop [ConnectedSpace M]
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : RelativeFiniteEnergyPreceq θ φ u hφ)
    (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    (energy θ φ hφ u).toReal + (energy θ φ hφ v).toReal ≤
      (energy θ φ hφ (fun x => max (u x) (v x))).toReal +
      (energy θ φ hφ (rooftop θ u v)).toReal := by
  have hr := relativeFiniteEnergyPreceq_rooftop omega hu hv
  have hm : RelativePSHPreceq θ φ (fun x => max (u x) (v x)) :=
    ⟨IsThetaPshPotential.max hu.1.plurisubharmonic hv.1.plurisubharmonic,
      DominationPrincipleReduction.moreSingularOn_max
        hu.1.relativePSHPreceq.2 hv.1.relativePSHPreceq.2⟩
  have hmbot : ⊥ < energy θ φ hφ (fun x => max (u x) (v x)) :=
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega hu).trans_le
      (energy_mono_of_le fun x => le_max_left _ _)
  have h := energy_add_le_max_add_rooftop omega θ hφ hu.1.relativePSHPreceq
    hv.1.relativePSHPreceq hr.1.plurisubharmonic
  rw [← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hv,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hr,
    ← EReal.coe_toReal (energy_ne_top_of_preceq hm) hmbot.ne',
    ← EReal.coe_add, ← EReal.coe_add] at h
  simpa only [EReal.toReal_coe, EReal.coe_le_coe_iff] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedDiamond
