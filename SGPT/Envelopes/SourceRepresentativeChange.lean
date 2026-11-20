import SGPT.Toric.LogLogModelEnvelope
import SGPT.PSH.SourceSubgeodesicBackground
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes

/-! # Smooth changes of representative for the original ordinary envelope

Transport the entire original normalized competitor family, including empty
families, with finite smooth corrections. No mass hypothesis is imposed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}

/-- Every normalized competitor transports with the same quantitative bound. -/
theorem sourceOrdinaryEnvelope_changeRepresentative_le (hg : ChartSmooth (n := n) g)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative η).val.coeff e z =
        (atlasClosedFormToNative θ).val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    (B : ℝ) (hB : ∀ x, |g x| ≤ B) (u : M → EReal) :
    sourceSingularityEnvelope θ u ≤
      fun x => sourceSingularityEnvelope η (fun y => u y - (g y : EReal)) x +
        ((2 * B : ℝ) : EReal) := by
  apply uscRegularization_le
    (upperSemicontinuous_add_coe_const
      (upperSemicontinuous_sourceSingularityEnvelope η _) (2 * B))
  intro x
  apply iSup_le
  intro v
  let w : M → EReal := fun y => v.1 y + (((-g y - B : ℝ)) : EReal)
  have hw : (ofFixedModel n M).IsThetaPSH η w := by
    have hsub := sourceThetaPSH_sub_smooth
      ((sourceSmoothBackgroundChange_iff_native θ η g).mpr ⟨hg, hθη⟩) v.2.1
    have hh := (isThetaPSH_iff_nativeThetaPotential η _).mpr
      (((isThetaPSH_iff_nativeThetaPotential η _).mp hsub).add_const (-B))
    convert hh using 1
    funext y
    simp only [w, sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
  have hw0 : w ≤ 0 := by
    intro y
    have hb : -g y - B ≤ 0 := by linarith [(abs_le.mp (hB y)).1]
    have hh := add_le_add (v.2.2.1 y) (EReal.coe_le_coe_iff.mpr hb)
    simpa only [w, Pi.zero_apply, EReal.coe_zero, add_zero] using hh
  obtain ⟨C, hC⟩ := v.2.2.2
  have hwtype : SGPT.PSH.SingularityLE w (fun y => u y - (g y : EReal)) := by
    refine ⟨C - B, fun y hy => ?_⟩
    have hh := add_le_add (hC y hy) (le_refl (((-g y - B : ℝ)) : EReal))
    apply hh.trans_eq
    have hreal : C + (-g y - B) = -g y + (C - B) := by ring
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add] using
      congrArg (fun r : ℝ ↦ u y + (r : EReal)) hreal
  have hle := le_sourceSingularityEnvelope hw hw0 hwtype x
  have hh := add_le_add hle (le_refl (((g x + B : ℝ)) : EReal))
  have hcancel : w x + (((g x + B : ℝ)) : EReal) = v.1 x := by
    simp only [w, add_assoc, ← EReal.coe_add]
    have hz : -g x - B + (g x + B) = 0 := by ring
    rw [hz, EReal.coe_zero, add_zero]
  rw [hcancel] at hh
  exact hh.trans (add_le_add le_rfl
    (EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB x)).2])))

variable [CompactSpace M]

/-- The entire original representative-independence proposition, including
genuine compensated membership and both finite singularity comparisons. -/
theorem sourceOrdinaryEnvelope_changeRepresentative (hg : ChartSmooth (n := n) g)
    (hθη : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative η).val.coeff e z =
        (atlasClosedFormToNative θ).val.coeff e z + smoothDDC (fun y => g (e.val.symm y)) z)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH η (fun x => u x - (g x : EReal)) ∧
      SGPT.PSH.SingularityEquiv (sourceSingularityEnvelope θ u)
        (sourceSingularityEnvelope η (fun x => u x - (g x : EReal))) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hg).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have hneg : ChartSmooth (n := n) (fun x => -g x) := fun e => (hg e).neg
  have hηθ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative θ).val.coeff e z =
        (atlasClosedFormToNative η).val.coeff e z + smoothDDC (fun y => -g (e.val.symm y)) z := by
    intro e z hz
    rw [smoothDDC_neg e.val.open_target (hg e) hz, hθη e z hz, add_neg_cancel_right]
  have hreverse := sourceOrdinaryEnvelope_changeRepresentative_le hneg hηθ B
    (fun x => by simpa only [abs_neg] using hbound x) (fun x => u x - (g x : EReal))
  have hcancel : (fun x => u x - (g x : EReal) - ((-g x : ℝ) : EReal)) = u := by
    funext x
    simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      neg_neg, neg_add_cancel, EReal.coe_zero, add_zero]
  rw [hcancel] at hreverse
  exact ⟨sourceThetaPSH_sub_smooth
      ((sourceSmoothBackgroundChange_iff_native θ η g).mpr ⟨hg, hθη⟩) hu,
    ⟨⟨2 * B, fun x _ => sourceOrdinaryEnvelope_changeRepresentative_le hg hθη B hbound u x⟩,
      ⟨2 * B, fun x _ => hreverse x⟩⟩⟩

end SGPT.PSH.VariableComplexAtlas
