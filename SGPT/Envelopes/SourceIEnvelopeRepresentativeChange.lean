import SGPT.PSH.SourceIVolumeGoodness
import SGPT.PSH.SourceSubgeodesicBackground
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder
import SGPT.Foundations.Analysis.Pending.GlobalSlotStokes

/-! # Smooth representative changes for the original I-envelope

Actual smooth compensation preserves genuine source PSH membership.
All original normalized competitors are transported with finite bounds;
the full source proposition includes poles and every natural dimension.
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

private theorem sourceIEquivalent_of_finite_comparisons
    {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH η v)
    (ht : SGPT.PSH.SingularityEquiv u v) :
    sourceIEquivalent (ofFixedModel n M) u v := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := ht
  apply (sourceIEquivalent_iff_native ⟨θ, hu⟩ ⟨η, hv⟩).mpr
  exact ⟨iOrderOnManifold_of_le_add
      ((isThetaPSH_iff_nativeThetaPotential η v).mp hv).1.quasiPlurisubharmonic
      (fun x => hA x (mem_univ x)),
    iOrderOnManifold_of_le_add
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu).1.quasiPlurisubharmonic
      (fun x => hB x (mem_univ x))⟩

variable [CompactSpace M]
  {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)} {g : M → ℝ}

omit [CompactSpace M] in
/-- Transport every actual normalized I-competitor with its finite smooth bound. -/
theorem sourceIEnvelope_changeRepresentative_le
    (hchange : SourceSmoothBackgroundChange θ η g)
    (B : ℝ) (hB : ∀ x, |g x| ≤ B)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceIEnvelope θ u ≤
      fun x => sourceIEnvelope η (fun y => u y - (g y : EReal)) x +
        ((2 * B : ℝ) : EReal) := by
  have hu' := sourceThetaPSH_sub_smooth hchange hu
  have hIu : sourceIEquivalent (ofFixedModel n M) u (fun y => u y - (g y : EReal)) := by
    apply sourceIEquivalent_of_finite_comparisons hu hu'
    refine ⟨⟨B, fun x _ => ?_⟩, ⟨B, fun x _ => ?_⟩⟩
    · have hh := add_le_add (le_refl (u x - (g x : EReal)))
        (EReal.coe_le_coe_iff.mpr (abs_le.mp (hB x)).2)
      have heq : u x - (g x : EReal) + (g x : EReal) = u x := by
        simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
          neg_add_cancel, EReal.coe_zero, add_zero]
      rwa [heq] at hh
    · change u x + -(g x : EReal) ≤ u x + (B : EReal)
      exact add_le_add le_rfl
        (by rw [← EReal.coe_neg]; exact EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB x)).1]))
  apply uscRegularization_le
    (upperSemicontinuous_add_coe_const
      (upperSemicontinuous_sourceIEnvelope η _) (2 * B))
  intro x
  apply iSup_le
  intro v
  let w : M → EReal := fun y => v.1 y + (((-g y - B : ℝ)) : EReal)
  have hw : (ofFixedModel n M).IsThetaPSH η w := by
    have hsub := sourceThetaPSH_sub_smooth hchange v.2.1
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
  have hwv : sourceIEquivalent (ofFixedModel n M) w v.1 := by
    apply sourceIEquivalent_of_finite_comparisons hw v.2.1
    refine ⟨⟨0, fun y _ => ?_⟩, ⟨2 * B, fun y _ => ?_⟩⟩
    · have hb : -g y - B ≤ 0 := by linarith [(abs_le.mp (hB y)).1]
      simpa only [w, EReal.coe_zero, add_zero] using
        (add_le_add (le_refl (v.1 y)) (EReal.coe_le_coe_iff.mpr hb))
    · have hb : g y + B ≤ 2 * B := by linarith [(abs_le.mp (hB y)).2]
      have heq : w y + (((g y + B : ℝ)) : EReal) = v.1 y := by
        simp only [w, add_assoc, ← EReal.coe_add]
        have hz : -g y - B + (g y + B) = 0 := by ring
        rw [hz, EReal.coe_zero, add_zero]
      have hh := add_le_add (le_refl (w y)) (EReal.coe_le_coe_iff.mpr hb)
      rwa [heq] at hh
  have hwtype := sourceIEquivalent_trans hwv (sourceIEquivalent_trans v.2.2.2 hIu)
  have hle := le_sourceIEnvelope hw hw0 hwtype x
  have hh := add_le_add hle (le_refl (((g x + B : ℝ)) : EReal))
  have hcancel : w x + (((g x + B : ℝ)) : EReal) = v.1 x := by
    simp only [w, add_assoc, ← EReal.coe_add]
    have hz : -g x - B + (g x + B) = 0 := by ring
    rw [hz, EReal.coe_zero, add_zero]
  rw [hcancel] at hh
  exact hh.trans (add_le_add le_rfl
    (EReal.coe_le_coe_iff.mpr (by linarith [(abs_le.mp (hB x)).2])))

/-- WHOLE original `prop:Ienvindeptheta`: genuine compensated PSH and both
finite ordinary singularity comparisons, with no mass or dimension restriction. -/
theorem sourceIEnvelope_changeRepresentative
    (hchange : SourceSmoothBackgroundChange θ η g)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (ofFixedModel n M).IsThetaPSH η (fun x => u x - (g x : EReal)) ∧
      SGPT.PSH.SingularityEquiv (sourceIEnvelope θ u)
        (sourceIEnvelope η (fun x => u x - (g x : EReal))) := by
  have hc := (sourceSmoothBackgroundChange_iff_native θ η g).mp hchange
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (GlobalSlotStokes.ChartSmooth.continuous hc.1).continuousOn
  have hbound : ∀ x, |g x| ≤ B := fun x => by
    simpa only [Real.norm_eq_abs] using hB x (mem_univ x)
  have hneg : ChartSmooth (n := n) (fun x => -g x) := fun e => (hc.1 e).neg
  have hηθ : ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
      (atlasClosedFormToNative θ).val.coeff e z =
        (atlasClosedFormToNative η).val.coeff e z + smoothDDC (fun y => -g (e.val.symm y)) z := by
    intro e z hz
    rw [smoothDDC_neg e.val.open_target (hc.1 e) hz, hc.2 e z hz, add_neg_cancel_right]
  have hreverse := sourceIEnvelope_changeRepresentative_le
    ((sourceSmoothBackgroundChange_iff_native η θ (fun x => -g x)).mpr ⟨hneg, hηθ⟩)
    B (fun x => by simpa only [abs_neg] using hbound x)
    (sourceThetaPSH_sub_smooth hchange hu)
  have hcancel : (fun x => u x - (g x : EReal) - ((-g x : ℝ) : EReal)) = u := by
    funext x
    simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add,
      neg_neg, neg_add_cancel, EReal.coe_zero, add_zero]
  rw [hcancel] at hreverse
  exact ⟨sourceThetaPSH_sub_smooth hchange hu,
    ⟨⟨2 * B, fun x _ => sourceIEnvelope_changeRepresentative_le hchange B hbound hu x⟩,
      ⟨2 * B, fun x _ => hreverse x⟩⟩⟩

end SGPT.PSH.VariableComplexAtlas
