import SGPT.Foundations.Analysis.Pending.OrderedConvexNativeContinuity
import SGPT.Foundations.Analysis.Pending.SingularNativeScalingContinuity

import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false


/-! # Actual one-sided real coefficient limits in a genuine enlarged background -/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.TracePositiveCoefficientNativeLimits

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeEnergy ThetaPshConvexCombination ThetaPshL1Topology SingularCanonicalSingularityDistance
  PluripolarCapacityDichotomy SingularMinimalCanonicalRay
  SingularCanonicalCutoffConstantInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem scaled_genuine (β : KahlerBackground n M)
    {u : M → EReal} (hu : IsThetaPshPotential β.form.val u)
    {c C : ℝ} (hc : 0 < c) (hle : c ≤ C) :
    IsThetaPshPotential (C • β.form).val (fun x => (c : EReal) * u x) := by
  have h := RestrictedApproximantComparison.isThetaPshPotential_smul hu hc
  have heq : c • β.form + (C - c) • β.form = C • β.form := by module
  simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive h
    (KahlerDomination.isSemipositive_smul β.isSemipositive (sub_nonneg.mpr hle))

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] in
private theorem scale_sub_const {c : ℝ} (hc : 0 < c) (u : M → EReal) (b : ℝ) :
    (fun x => (c : EReal) * (u x - (b : EReal))) =
      fun x => (c : EReal) * u x - ((c * b : ℝ) : EReal) := by
  funext x
  simpa only [EReal.coe_neg, sub_eq_add_neg, mul_neg] using
    ThetaPshConvexCombination.coe_mul_add_coe hc (u x) (-b)

/-- The natural shrink parameter and internal genuine scaling witnesses
produce the lower coefficient limit in the actual enlarged Kähler class. -/
theorem tendsto_native_lower_coefficients (omega β : KahlerBackground n M)
    {u : M → EReal} (hu : IsThetaPshPotential β.form.val u)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {I : Type*} (F : Filter I)
    (r : I → Ioo (0 : ℝ) ℓ)
    (hr : Tendsto (fun i => (r i).val) F (𝓝 ℓ)) :
    let γ := KahlerBackground.smul (show 0 < ℓ + 1 by linarith) β
    ∃ htarget : IsThetaPshPotential γ.form.val (fun x => (ℓ : EReal) * u x),
    ∃ hstage : ∀ i, IsThetaPshPotential γ.form.val (fun x => ((r i).val : EReal) * u x),
      Tendsto (fun i => (⟨fun x => ((r i).val : EReal) * u x, hstage i⟩ :
        ThetaPshL1 γ.form.val)) F
        (@nhds (ThetaPshL1 γ.form.val)
          (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
          ⟨fun x => (ℓ : EReal) * u x, htarget⟩) := by
  dsimp only
  let γ := KahlerBackground.smul (show 0 < ℓ + 1 by linarith) β
  have htarget : IsThetaPshPotential γ.form.val (fun x => (ℓ : EReal) * u x) :=
    scaled_genuine β hu hℓ (by linarith)
  have hstage (i : I) : IsThetaPshPotential γ.form.val (fun x => ((r i).val : EReal) * u x) :=
    scaled_genuine β hu (r i).property.1 (by linarith [(r i).property.2])
  let t : I → Ioo (0 : ℝ) 1 := fun i => ⟨1 - (r i).val / ℓ,
    ⟨by have := (div_lt_one hℓ).mpr (r i).property.2; linarith,
     by have := div_pos (r i).property.1 hℓ; linarith⟩⟩
  have ht : Tendsto (fun i => (t i).val) F (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := F)).sub (hr.div_const ℓ)
    simpa only [div_self hℓ.ne', sub_self] using h
  have halg (i : I) : (1 - (t i).val) * ℓ = (r i).val := by
    dsimp only [t]
    field_simp
    ring
  have heq (i : I) :
      (fun x => ((1 - (t i).val : ℝ) : EReal) * ((ℓ : EReal) * u x)) =
      fun x => ((r i).val : EReal) * u x := by
    funext x
    rw [← mul_assoc, ← EReal.coe_mul, halg]
  have hs (i : I) : IsThetaPshPotential γ.form.val
      (fun x => ((1 - (t i).val : ℝ) : EReal) * ((ℓ : EReal) * u x)) := by
    rw [heq]
    exact hstage i
  have hlim := SingularNativeScalingContinuity.tendsto_native_admissible_scaling_one
    omega γ.form (isBigClass_kahler γ) htarget F t ht hs
  refine ⟨htarget, hstage, hlim.congr' (Eventually.of_forall fun i => ?_)⟩
  exact Subtype.ext (heq i)

/-- Actual compact finite normalization, ordered convex native continuity,
and defining canonical-ray constant invariance give the upper coefficient limit. -/
theorem tendsto_native_upper_coefficients (omega β : KahlerBackground n M)
    {u : M → EReal} (hu : IsThetaPshPotential β.form.val u)
    {ℓ : ℝ} (hℓ : 0 < ℓ) {I : Type*} (F : Filter I)
    (r : I → Ioo ℓ (ℓ + 1))
    (hr : Tendsto (fun i => (r i).val) F (𝓝 ℓ)) :
    let γ := KahlerBackground.smul (show 0 < ℓ + 1 by linarith) β
    ∃ htarget : IsThetaPshPotential γ.form.val (fun x => (ℓ : EReal) * u x),
    ∃ hstage : ∀ i, IsThetaPshPotential γ.form.val (fun x => ((r i).val : EReal) * u x),
      Tendsto (fun i => (⟨fun x => ((r i).val : EReal) * u x, hstage i⟩ :
        ThetaPshL1 γ.form.val)) F
        (@nhds (ThetaPshL1 γ.form.val)
          (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
          ⟨fun x => (ℓ : EReal) * u x, htarget⟩) := by
  dsimp only
  let γ := KahlerBackground.smul (show 0 < ℓ + 1 by linarith) β
  have htarget : IsThetaPshPotential γ.form.val (fun x => (ℓ : EReal) * u x) :=
    scaled_genuine β hu hℓ (by linarith)
  have hstage (i : I) : IsThetaPshPotential γ.form.val (fun x => ((r i).val : EReal) * u x) :=
    scaled_genuine β hu (hℓ.trans (r i).property.1) (r i).property.2.le
  obtain ⟨B, hB⟩ := hu.exists_global_upper_bound
  let σ : M → EReal := fun x => u x - (B : EReal)
  have hσ : IsThetaPshPotential β.form.val σ := hu.sub_const B
  have hσ0 : σ ≤ 0 := sub_const_nonpositive_of_le hB
  have hℓσ : IsThetaPshPotential γ.form.val (fun x => (ℓ : EReal) * σ x) :=
    scaled_genuine β hσ hℓ (by linarith)
  have hp : IsThetaPshPotential γ.form.val (fun x => ((ℓ + 1 : ℝ) : EReal) * σ x) :=
    scaled_genuine β hσ (by linarith) le_rfl
  have horder : (fun x => ((ℓ + 1 : ℝ) : EReal) * σ x) ≤ fun x => (ℓ : EReal) * σ x := by
    intro x
    change ((ℓ + 1 : ℝ) : EReal) * σ x ≤ (ℓ : EReal) * σ x
    have h0 : σ x ≤ (0 : EReal) := hσ0 x
    induction hs : σ x using EReal.rec with
    | bot => simp only [EReal.coe_mul_bot_of_pos hℓ, EReal.coe_mul_bot_of_pos (by linarith : 0 < ℓ + 1), le_refl]
    | top => rw [hs] at h0; simp at h0
    | coe a =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      have ha : a ≤ 0 := EReal.coe_le_coe_iff.mp (hs ▸ h0)
      nlinarith
  let t : I → Ioo (0 : ℝ) 1 := fun i => ⟨(r i).val - ℓ,
    ⟨sub_pos.mpr (r i).property.1, by linarith [(r i).property.2]⟩⟩
  have ht : Tendsto (fun i => (t i).val) F (𝓝 0) := by
    simpa only [sub_self] using hr.sub_const ℓ
  have heq (i : I) :
      convexComb (1 - (t i).val) (fun x => (ℓ : EReal) * σ x)
        (fun x => ((ℓ + 1 : ℝ) : EReal) * σ x) =
      fun x => ((r i).val : EReal) * σ x := by
    funext x
    induction hs : σ x using EReal.rec with
    | bot =>
      simp only [convexComb, hs, EReal.coe_mul_bot_of_pos hℓ,
        EReal.coe_mul_bot_of_pos (by linarith : 0 < ℓ + 1),
        EReal.coe_mul_bot_of_pos (sub_pos.mpr (t i).property.2),
        EReal.coe_mul_bot_of_pos (by linarith [(t i).property.1] : 0 < 1 - (1 - (t i).val)),
        EReal.coe_mul_bot_of_pos (hℓ.trans (r i).property.1)]
      rfl
    | top =>
      simp only [convexComb, hs, EReal.coe_mul_top_of_pos hℓ,
        EReal.coe_mul_top_of_pos (by linarith : 0 < ℓ + 1),
        EReal.coe_mul_top_of_pos (sub_pos.mpr (t i).property.2),
        EReal.coe_mul_top_of_pos (by linarith [(t i).property.1] : 0 < 1 - (1 - (t i).val)),
        EReal.coe_mul_top_of_pos (hℓ.trans (r i).property.1), EReal.top_add_top]
    | coe a =>
      simp only [convexComb, hs, ← EReal.coe_mul, ← EReal.coe_add]
      apply congrArg (fun a : ℝ => (a : EReal))
      dsimp only [t]
      ring
  have hnorm := OrderedConvexNativeContinuity.tendsto_native_ordered_convex
    omega γ.form (isBigClass_kahler γ) hℓσ hp horder F t ht
  dsimp only at hnorm
  have hσstage (i : I) : IsThetaPshPotential γ.form.val (fun x => ((r i).val : EReal) * σ x) :=
    scaled_genuine β hσ (hℓ.trans (r i).property.1) (r i).property.2.le
  let : PseudoMetricSpace (ThetaPshL1 γ.form.val) :=
    singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  have hnorm' : Tendsto (fun i => (⟨fun x => ((r i).val : EReal) * σ x, hσstage i⟩ :
      ThetaPshL1 γ.form.val)) F
      (@nhds (ThetaPshL1 γ.form.val)
        (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
        ⟨fun x => (ℓ : EReal) * σ x, hℓσ⟩) :=
    hnorm.congr' (Eventually.of_forall fun i => Subtype.ext (heq i))
  let X : I → ThetaPshL1 γ.form.val := fun i => ⟨fun x => ((r i).val : EReal) * σ x, hσstage i⟩
  let T : ThetaPshL1 γ.form.val := ⟨fun x => (ℓ : EReal) * σ x, hℓσ⟩
  let W : I → ThetaPshL1 γ.form.val := fun i => ⟨fun x => ((r i).val : EReal) * u x, hstage i⟩
  let V : ThetaPshL1 γ.form.val := ⟨fun x => (ℓ : EReal) * u x, htarget⟩
  have hd (i : I) : dist (X i) T = dist (W i) V := by
    rw [dist_eq_singularityDistance_toReal, dist_eq_singularityDistance_toReal]
    have hi : (fun x => ((r i).val : EReal) * σ x) =
        fun x => ((r i).val : EReal) * u x - (((r i).val * B : ℝ) : EReal) :=
      scale_sub_const (hℓ.trans (r i).property.1) u B
    have hl : (fun x => (ℓ : EReal) * σ x) =
        fun x => (ℓ : EReal) * u x - ((ℓ * B : ℝ) : EReal) := scale_sub_const hℓ u B
    dsimp only [X, T, W, V, Subtype.val]
    rw [hi, hl]
    unfold singularityDistance
    rw [canonicalRay_sub_const_eq γ.form (hstage i) ((r i).val * B),
      canonicalRay_sub_const_eq γ.form htarget (ℓ * B)]
  have hcX := @tendsto_iff_dist_tendsto_zero (ThetaPshL1 γ.form.val) I
    (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)) X F T
  have hcW := @tendsto_iff_dist_tendsto_zero (ThetaPshL1 γ.form.val) I
    (singularityPseudoMetricSpace omega γ.form (isBigClass_kahler γ)) W F V
  refine ⟨htarget, hstage, ?_⟩
  exact hcW.mpr ((hcX.mp hnorm').congr' (Eventually.of_forall fun i => hd i))

end

end SGPT.Foundations.Analysis.Pending.TracePositiveCoefficientNativeLimits
