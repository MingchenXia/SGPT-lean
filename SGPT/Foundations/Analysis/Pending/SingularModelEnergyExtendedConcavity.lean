import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyConcavity

set_option autoImplicit false

/-!
# Concavity of actual extended singular-model energy

Xia SGPT PDF0122, Corollary 3.1.4, from Lemma 3.1.5 (PDF0119--0120)
and Proposition 3.1.16. Genuine same-type singular max truncations
approximate both endpoints, finite-type concavity supplies actual inequalities,
and actual decreasing energy continuity passes to the extended limit.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedConcavity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses ThetaPshConvexCombination SingularModelEnergyCocycle
  SingularModelEnergyTruncation

noncomputable section

/-- Positive convex weights preserve limits with no positive-infinite endpoint,
including negative-infinite endpoints and arbitrary source filters. -/
theorem tendsto_weighted_add_of_ne_top {ι : Type*} {F : Filter ι}
    {a b : EReal} {ak bk : ι → EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hA : Tendsto ak F (𝓝 a)) (hB : Tendsto bk F (𝓝 b)) :
    Tendsto (fun k => (t : EReal) * ak k + ((1 - t : ℝ) : EReal) * bk k) F
      (𝓝 ((t : EReal) * a + ((1 - t : ℝ) : EReal) * b)) := by
  have hnotop (c : ℝ) (hc : 0 < c) (r : EReal) (hr : r ≠ ⊤) :
      (c : EReal) * r ≠ ⊤ := by
    induction r using EReal.rec with
    | bot => simp [EReal.coe_mul_bot_of_pos hc]
    | top => exact (hr rfl).elim
    | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  have hA' := EReal.Tendsto.const_mul (a := (t : EReal)) hA
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hB' := EReal.Tendsto.const_mul (a := ((1 - t : ℝ) : EReal)) hB
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  exact (EReal.continuousAt_add
    (Or.inl (hnotop t ht0 a ha))
    (Or.inr (hnotop (1 - t) (by linarith) b hb))).tendsto.comp (hA'.prodMk_nhds hB')

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual extended singular-model energy is concave for positive convex weights,
with genuine max truncations and their finite-type energies produced in the proof. -/
theorem energy_concave_of_pos (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : MoreSingularOn u φ univ) (hvφ : MoreSingularOn v φ univ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (t : EReal) * energy θ φ hφ u + ((1 - t : ℝ) : EReal) * energy θ φ hφ v ≤
      energy θ φ hφ (convexComb t u v) := by
  let uk := MongeAmpereEnergyDecreasing.truncation φ u
  let vk := MongeAmpereEnergyDecreasing.truncation φ v
  have huk (k : ℕ) : RelativeEInfinity θ φ (uk k) :=
    relativeEInfinity_truncation hφ.plurisubharmonic hu huφ k
  have hvk (k : ℕ) : RelativeEInfinity θ φ (vk k) :=
    relativeEInfinity_truncation hφ.plurisubharmonic hv hvφ k
  let wk : ℕ → M → EReal := fun k => convexComb t (uk k) (vk k)
  have hwk (k : ℕ) : IsThetaPshPotential θ.val (wk k) :=
    isThetaPshPotential_convexComb (huk k).1 (hvk k).1 ht0 ht1
  have hwtype (k : ℕ) : SameSingularityTypeOn (wk k) φ univ :=
    SingularModelEnergyConcavity.sameSingularityTypeOn_convexComb (huk k).2 (hvk k).2 ht0 ht1
  have hwanti : ∀ x, Antitone fun k => wk k x := by
    intro x i j hij
    exact convexComb_mono ht0.le ht1.le
      (fun y => MongeAmpereEnergyDecreasing.truncation_antitone φ u y hij)
      (fun y => MongeAmpereEnergyDecreasing.truncation_antitone φ v y hij) x
  have hwlim (x : M) : Tendsto (fun k => wk k x) atTop (𝓝 (convexComb t u v x)) :=
    tendsto_weighted_add_of_ne_top (hu.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.quasiPlurisubharmonic.ne_top x)
      ht0 ht1 (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
      (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
  have hEw := SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    hwk (hwtype 0).1 hwanti hwlim
  have hEu := energy_tendsto_truncation omega θ hφ hu huφ
  have hEv := energy_tendsto_truncation omega θ hφ hv hvφ
  have hEl := tendsto_weighted_add_of_ne_top
    (energy_ne_top_of_preceq (hφ := hφ) ⟨hu, huφ⟩)
    (energy_ne_top_of_preceq (hφ := hφ) ⟨hv, hvφ⟩) ht0 ht1 hEu hEv
  apply le_of_tendsto_of_tendsto hEl hEw
  refine Eventually.of_forall fun k => ?_
  change (t : EReal) * (relativeEnergyOfMinimalType θ φ (uk k) hφ.plurisubharmonic (huk k).1 : EReal) +
    ((1 - t : ℝ) : EReal) *
      (relativeEnergyOfMinimalType θ φ (vk k) hφ.plurisubharmonic (hvk k).1 : EReal) ≤
        energy θ φ hφ (wk k)
  rw [energy_eq_of_relativeEInfinity omega θ hφ ⟨hwk k, hwtype k⟩]
  have hc := SingularModelEnergyConcavity.relativeEnergyOfMinimalType_concave omega θ
    hφ.plurisubharmonic (huk k).1 (hvk k).1 (huk k).2 (hvk k).2 ht0 ht1
  simpa only [← EReal.coe_mul, ← EReal.coe_add] using EReal.coe_le_coe_iff.mpr hc

/-- Full closed-interval concavity of actual extended energy for arbitrary singular model references. -/
theorem energy_concave (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u v : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v)
    (huφ : MoreSingularOn u φ univ) (hvφ : MoreSingularOn v φ univ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : EReal) * energy θ φ hφ u + ((1 - t : ℝ) : EReal) * energy θ φ hφ v ≤
      energy θ φ hφ (convexComb t u v) := by
  by_cases hzero : t = 0
  · subst t
    have heq : convexComb 0 u v = v := by
      funext x
      simp only [convexComb_apply, sub_zero, EReal.coe_zero, EReal.coe_one,
        zero_mul, one_mul, zero_add]
    rw [heq]
    simp
  by_cases hone : t = 1
  · subst t
    have heq : convexComb 1 u v = u := by
      funext x
      simp only [convexComb_apply, sub_self, EReal.coe_one, EReal.coe_zero,
        one_mul, zero_mul, add_zero]
    rw [heq]
    simp
  exact energy_concave_of_pos omega θ hφ hu hv huφ hvφ
    (lt_of_le_of_ne ht0 (Ne.symm hzero)) (lt_of_le_of_ne ht1 hone)

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedConcavity
