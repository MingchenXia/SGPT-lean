import SGPT.Foundations.Analysis.Pending.SingularModelIncreasingRegularizedMixedWeights
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyCocycle
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTranslation

set_option autoImplicit false

/-!
# Actual finite same-type energy at increasing regularized suprema

Xia SGPT PDF0119 and PDF0127, the genuine regularized-supremum finite-type
sequence domain. Actual canonical moving-weight integrals produce the
energy limit; no regularized convergence premise or bounded reference is used.
General E1 and chart almost-everywhere consumers are separate producers.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedContinuity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
open SingularModelEnergyCocycle SingularModelEnergyTranslation
open SingularModelFiniteEnergyMixedGap SingularModelIncreasingRegularizedMixedWeights
open RelativeDarvasDistance

noncomputable section

private theorem uscRegularization_iSup_sub_const {X : Type*} [TopologicalSpace X]
    (u : ℕ → X → EReal) (C : ℝ) :
    uscRegularization (⨆ j, fun x => u j x - (C : EReal)) =
      fun x => uscRegularization (⨆ j, u j) x - (C : EReal) := by
  have hsup : (⨆ j, fun x => u j x - (C : EReal)) =
      fun x => (⨆ j, u j) x - (C : EReal) := by
    funext x
    simp only [iSup_apply, sub_eq_add_neg, ← EReal.coe_neg]
    exact (NegligibleSetNotCharged.iSup_add_coe (fun j => u j x) (-C)).symm
  rw [hsup]
  simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
    uscRegularization_add_coe_const (⨆ j, u j) (-C)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual finite same-type energy is continuous along a genuine regularized
increasing sequence, with no bounded-potential or capacity certificate input. -/
theorem relativeEnergyOfMinimalType_tendsto_of_monotone_regularized
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ v : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hv : IsThetaPshPotential θ.val v) (hvφ : SameSingularityTypeOn v φ univ)
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (huφ : SameSingularityTypeOn (u 0) φ univ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => relativeEnergyOfMinimalType θ φ (u j) hφ (hu j)) atTop
      (𝓝 (relativeEnergyOfMinimalType θ φ v hφ hv)) := by
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  obtain ⟨C, hC⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hv
  have htj : ∀ j, SameSingularityTypeOn (u j) φ univ := fun j =>
    ⟨(MoreSingularOn.of_le fun x _ => huv j x).trans hvφ.1,
      huφ.2.trans (MoreSingularOn.of_le fun x _ => hm x (Nat.zero_le j))⟩
  have hshift (w : M → EReal) :
      SameSingularityTypeOn (fun x => w x - (C : EReal)) w univ := by
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
      sameSingularityTypeOn_add_const w univ (-C)
  have hUv : ∀ j, (fun x => u j x - (C : EReal)) ≤ fun x => v x - (C : EReal) :=
    fun j x => by simpa only [sub_eq_add_neg] using add_le_add (huv j x) (le_refl (-(C : EReal)))
  have hUm : ∀ x, Monotone fun j => u j x - (C : EReal) := by
    intro x j k hjk
    simpa only [sub_eq_add_neg] using add_le_add (hm x hjk) (le_refl (-(C : EReal)))
  have hV0 : (fun x => v x - (C : EReal)) ≤ 0 := by
    intro x
    calc v x - (C : EReal) ≤ (C : EReal) - (C : EReal) := by
          simpa only [sub_eq_add_neg] using add_le_add (hC x) (le_refl (-(C : EReal)))
      _ = 0 := by rw [← EReal.coe_sub]; simp
  have hshiftReg : uscRegularization (⨆ j, fun x => u j x - (C : EReal)) =
      fun x => v x - (C : EReal) := by
    rw [uscRegularization_iSup_sub_const, hreg]
  obtain ⟨B, hB⟩ := (huφ.trans hvφ.symm).2
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hVU : ∀ x, v x - (C : EReal) ≤ (u 0 x - (C : EReal)) + (D : EReal) := by
    intro x
    have hb := (hB x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_left B 0)))
    have h := add_le_add hb (le_refl (-(C : EReal)))
    simpa only [sub_eq_add_neg, add_right_comm] using h
  have hbound := tendsto_integral_canonicalGap_binaryMixedMeasure_regularized omega
    (fun j => (hu j).sub_const C) (hv.sub_const C) hUm hV0 hD hVU hshiftReg (fun _ => true)
  simp only [binaryMixedMeasure, ↓reduceIte] at hbound
  have hs : Tendsto (fun j =>
      relativeEnergyOfMinimalType θ φ (fun x => v x - (C : EReal)) hφ (hv.sub_const C) -
      relativeEnergyOfMinimalType θ φ (fun x => u j x - (C : EReal)) hφ ((hu j).sub_const C))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun j => ?_) (fun j => ?_)
    · exact sub_nonneg.mpr (relativeEnergyOfMinimalType_mono omega θ hφ
        ((hu j).sub_const C) (hv.sub_const C) ((hshift (u j)).trans (htj j))
        ((hshift v).trans hvφ) (hUv j))
    · exact (integral_le_relativeEnergyOfMinimalType_sub_le omega θ hφ
        (hv.sub_const C) ((hu j).sub_const C) ((hshift v).trans hvφ)
        ((hshift (u j)).trans (htj j))).2
  have hconv := hs.neg.add_const
    (relativeEnergyOfMinimalType θ φ (fun x => v x - (C : EReal)) hφ (hv.sub_const C))
  simp only [neg_sub, sub_add_cancel, neg_zero, zero_add] at hconv
  have htrans : ∀ j, relativeEnergyOfMinimalType θ φ (fun x => u j x - (C : EReal))
      hφ ((hu j).sub_const C) = relativeEnergyOfMinimalType θ φ (u j) hφ (hu j) -
      C * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := fun j =>
    relativeEnergyOfMinimalType_sub_const omega θ hφ (hu j) (htj j) C
  rw [relativeEnergyOfMinimalType_sub_const omega θ hφ hv hvφ C] at hconv
  simp only [htrans] at hconv
  simpa only [sub_add_cancel] using hconv.add_const
    (C * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ)

/-- Actual model energy agrees with the convergent finite formula along an
increasing same-type regularized sequence over an arbitrary singular model. -/
theorem energy_tendsto_of_monotone_regularized_sameType
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ v : M → EReal} (hφ : IsModelPotential θ φ)
    (hv : IsThetaPshPotential θ.val v) (hvφ : SameSingularityTypeOn v φ univ)
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential θ.val (u j))
    (huφ : SameSingularityTypeOn (u 0) φ univ)
    (hm : ∀ x, Monotone fun j => u j x)
    (hreg : uscRegularization (⨆ j, u j) = v) :
    Tendsto (fun j => energy θ φ hφ (u j)) atTop (𝓝 (energy θ φ hφ v)) := by
  have huv : ∀ j, u j ≤ v := fun j x =>
    (le_iSup (fun k => u k) j x).trans (by rw [← hreg]; exact le_uscRegularization _ x)
  have htj : ∀ j, SameSingularityTypeOn (u j) φ univ := fun j =>
    ⟨(MoreSingularOn.of_le fun x _ => huv j x).trans hvφ.1,
      huφ.2.trans (MoreSingularOn.of_le fun x _ => hm x (Nat.zero_le j))⟩
  have h := relativeEnergyOfMinimalType_tendsto_of_monotone_regularized omega θ hφ.plurisubharmonic
    hv hvφ hu huφ hm hreg
  have he : ∀ j, energy θ φ hφ (u j) =
      (relativeEnergyOfMinimalType θ φ (u j) hφ.plurisubharmonic (hu j) : EReal) := fun j =>
    energy_eq_of_relativeEInfinity omega θ hφ ⟨hu j, htj j⟩
  rw [energy_eq_of_relativeEInfinity omega θ hφ ⟨hv, hvφ⟩]
  simp only [he]
  exact EReal.tendsto_coe.mpr h

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingRegularizedContinuity
