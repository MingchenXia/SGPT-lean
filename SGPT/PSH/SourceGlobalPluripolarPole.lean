import SGPT.PSH.Pluripolar
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.PluripolarOuterCapacity
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.GlobalPluripolarPole

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

/-- Exact source assembly of the ALREADY PROVED complete compact connected
Kähler capacity/pole mothers. Actual source local witnesses manufacture one
nonpositive global sourceω-PSH/QPSH pole, in ANY dimension includingzero.
No incoming global-pole/capacity/volume/normalization/desired-result certificate.
This is bounded Kähler scope, not the broader compact-complex gloJosefson. -/
theorem source_exists_nonpositive_global_pluripolar_pole
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
    (omega : KahlerBackground n M) {S : Set M}
    (hS : (ofFixedModel n M).LocallyPluripolar S) :
    ∃ q : M → EReal,
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas omega.form) q ∧
      (ofFixedModel n M).IsQPSH q ∧ (∀ x, q x ≤ 0) ∧ ∀ x ∈ S, q x = ⊥ := by
  have hSNative : ManifoldLocallyPluripolar (n := n) S := by
    intro e
    exact hS.in_chart e
  have hback : atlasClosedFormToNative (nativeClosedFormToAtlas omega.form) = omega.form := by
    rcases omega.form with ⟨wForm, hwForm⟩
    cases wForm
    rfl
  have source {q : M → EReal} (hq : IsThetaPshPotential omega.form.val q) :
      (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas omega.form) q := by
    apply (isThetaPSH_iff_nativeThetaPotential (nativeClosedFormToAtlas omega.form) q).mpr
    simpa only [hback] using hq
  rcases isEmpty_or_nonempty M with hM | hM
  · have hzero := source (PluripolarCapacityDichotomy.isThetaPshPotential_zero omega)
    exact ⟨fun _ => 0, hzero, ⟨_, hzero⟩, fun _ => le_rfl,
      fun x _ => (IsEmpty.false x).elim⟩
  · borelize M
    have hex : ∃ u : M → EReal, IsThetaPshPotential omega.form.val u ∧ ∀ x ∈ S, u x = ⊥ := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hempty := PluripolarOuterCapacity.eq_empty_of_manifoldLocallyPluripolar_dim_zero hSNative
        exact ⟨fun _ => 0, PluripolarCapacityDichotomy.isThetaPshPotential_zero omega,
          fun x hx => False.elim (by rw [hempty] at hx; exact hx)⟩
      · exact KahlerVolumePositive.exists_isThetaPshPotential_poles_of_outerCapacityZero' hn omega
          (PluripolarOuterCapacity.outerCapacityZero_of_manifoldLocallyPluripolar omega hSNative)
    obtain ⟨u, hu, hpoles⟩ := hex
    obtain ⟨C, hC⟩ := hu.exists_global_upper_bound
    let q : M → EReal := fun x => u x - (C : EReal)
    have hq : IsThetaPshPotential omega.form.val q := hu.sub_const C
    have hqSource := source hq
    refine ⟨q, hqSource, ⟨_, hqSource⟩, sub_const_nonpositive_of_le hC, ?_⟩
    intro x hx
    change u x - (C : EReal) = ⊥
    rw [hpoles x hx, sub_eq_add_neg, EReal.bot_add]

end SGPT.PSH.GlobalPluripolarPole
