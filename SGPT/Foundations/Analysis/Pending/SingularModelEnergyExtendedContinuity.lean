import SGPT.Foundations.Analysis.Pending.SingularModelEnergyContinuity
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-!
# Decreasing continuity of extended singular-model energy

Xia SGPT PDF0120--0121, the sequence case of Proposition 3.1.16.
For each actual same-type majorant of the limit, taking pointwise maxima
produces a genuine finite-type decreasing sequence. Its actual energy
converges, and the defining majorant infimum gives the extended limit.
The proof also applies when the pointwise limit is not itself genuine PSH.
General directed nets remain a separate result.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyCocycle SingularModelEnergyContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The actual extended energy commutes with a decreasing sequence whose initial
potential is more singular than the model reference, including infinite energy. -/
theorem energy_iInf_of_antitone (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) {uk : ℕ → M → EReal}
    (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (hu0φ : MoreSingularOn (uk 0) φ univ)
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    (⨅ k, energy θ φ hφ (uk k)) = energy θ φ hφ u := by
  have hle := MongeAmpereEnergyDecreasing.le_of_antitone_of_tendsto hanti hlim
  refine le_antisymm ?_ (le_iInf fun k => energy_mono_of_le (hle k))
  refine le_sInf ?_
  rintro e ⟨w, hw, huw, rfl⟩
  let vk : ℕ → M → EReal := fun k x => max (uk k x) (w x)
  have hvk (k : ℕ) : IsThetaPshPotential θ.val (vk k) :=
    IsThetaPshPotential.max (huk k) hw.plurisubharmonic
  have htype (k : ℕ) : SameSingularityTypeOn (vk k) φ univ :=
    ⟨DominationPrincipleReduction.moreSingularOn_max
        ((MoreSingularOn.of_le fun x _ => hanti x (Nat.zero_le k)).trans hu0φ)
        hw.sameSingularityType.1,
      hw.sameSingularityType.2.trans
        (MoreSingularOn.of_le fun x _ => le_max_right (uk k x) (w x))⟩
  have hvanti : ∀ x, Antitone fun k => vk k x := fun x i j hij =>
    max_le_max (hanti x hij) le_rfl
  have hvlim : ∀ x, Tendsto (fun k => vk k x) atTop (𝓝 (w x)) := by
    intro x
    have hc : Tendsto (fun _ : ℕ => w x) atTop (𝓝 (w x)) := tendsto_const_nhds
    simpa only [vk, max_eq_right (huw x)] using (hlim x).max hc
  have hconv := relativeEnergyOfMinimalType_tendsto_of_antitone omega θ
    hφ.plurisubharmonic hw.plurisubharmonic hw.sameSingularityType hvk
    (htype 0) hvanti hvlim
  have hconv' := (continuous_coe_real_ereal.tendsto _).comp hconv
  refine ge_of_tendsto' hconv' fun k => ?_
  refine (iInf_le _ k).trans ?_
  have hmono : energy θ φ hφ (uk k) ≤ energy θ φ hφ (vk k) :=
    energy_mono_of_le fun x => le_max_left (uk k x) (w x)
  rwa [energy_eq_of_relativeEInfinity omega θ hφ ⟨hvk k, htype k⟩] at hmono

/-- Actual extended energies converge along any decreasing genuine PSH sequence
initially more singular than the model reference; the value may be minus infinity. -/
theorem energy_tendsto_of_antitone (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) {uk : ℕ → M → EReal}
    (huk : ∀ k, IsThetaPshPotential θ.val (uk k))
    (hu0φ : MoreSingularOn (uk 0) φ univ)
    (hanti : ∀ x, Antitone fun k => uk k x)
    (hlim : ∀ x, Tendsto (fun k => uk k x) atTop (𝓝 (u x))) :
    Tendsto (fun k => energy θ φ hφ (uk k)) atTop (𝓝 (energy θ φ hφ u)) := by
  have hmono : Antitone fun k => energy θ φ hφ (uk k) :=
    fun i j hij => energy_mono_of_le fun x => hanti x hij
  have hL := tendsto_atTop_iInf hmono
  rwa [energy_iInf_of_antitone omega θ hφ huk hu0φ hanti hlim] at hL

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedContinuity
