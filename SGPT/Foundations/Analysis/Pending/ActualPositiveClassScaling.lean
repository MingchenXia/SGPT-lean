import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Actual positive scaling of big classes and minimal potentials

Kähler currents give actual scaled bigness. Normalized PSH competitors
give the actual minimal-potential identity used in SGPT PDF0240.
-/

open Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPositiveClassScaling

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  SingularMinimalCanonicalRay

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Scale the actual Kähler current witnessing bigness. -/
theorem isBigClass_positive_smul {α : RealBottChern n M} (hα : IsBigClass α)
    {c : ℝ} (hc : 0 < c) : IsBigClass (c • α) := by
  obtain ⟨T⟩ := hα
  refine ⟨{
    representative := c • T.representative
    represents := by rw [RealBottChern.ofRepresentative_smul, T.represents]
    potential := fun x => (c : EReal) * T.potential x
    lowerBound := KahlerBackground.smul hc T.lowerBound
    strictlyPsh := ?_ }⟩
  rw [KahlerBackground.smul_form, ← smul_sub]
  exact RestrictedApproximantComparison.isThetaPshPotential_smul T.strictlyPsh hc

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- The actual normalized minimal-potential identity, produced from competitors. -/
theorem thetaPshSupremum_positive_smul (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {c : ℝ} (hc : 0 < c) :
    thetaPshSupremum (c • θ).val = fun x => (c : EReal) * thetaPshSupremum θ.val x := by
  have hc0 : (0 : EReal) ≤ (c : EReal) := EReal.coe_nonneg.mpr hc.le
  have hV := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  have hcV := RestrictedApproximantComparison.isThetaPshPotential_smul hV hc
  apply le_antisymm
  · apply thetaPshSupremum_le_iff.mpr
    intro w hw hw0 x
    have hinv := RestrictedApproximantComparison.isThetaPshPotential_smul hw
      (inv_pos.mpr hc)
    have hform : c⁻¹ • (c • θ) = θ := by
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [hform] at hinv
    have hinv0 : (fun y => ((c⁻¹ : ℝ) : EReal) * w y) ≤ 0 := by
      intro y
      have h := mul_le_mul_of_nonneg_left (hw0 y)
        (EReal.coe_nonneg.mpr (inv_pos.mpr hc).le)
      simpa only [Pi.zero_apply, mul_zero] using h
    have h := mul_le_mul_of_nonneg_left (le_thetaPshSupremum hinv hinv0 x) hc0
    simpa only [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hc.ne',
      EReal.coe_one, one_mul] using h
  · apply le_thetaPshSupremum hcV
    intro x
    have h := mul_le_mul_of_nonneg_left (thetaPshSupremum_le_zero θ.val x) hc0
    simpa only [Pi.zero_apply, mul_zero] using h

end

end SGPT.Foundations.Analysis.Pending.ActualPositiveClassScaling
