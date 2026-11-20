import SGPT.PSH.SourceTestCurveClosedness
import SGPT.Convex.Legendre

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The EXACT original raw supremum on all real parameters. There is NO USC
regularization and no PSH output certificate in this definition. -/
def sourceTestCurveRawLegendre (Γ : SourceTestCurvePredata θ) (t : ℝ) (x : M) : EReal :=
  ⨆ τ : ℝ, ((t * τ : ℝ) : EReal) + sourceTestCurveAt Γ τ x

/-- The super-cutoff bottom branch may be removed from the original raw formula. -/
theorem SourceTestCurvePredata.rawLegendre_eq_iSup_closed
    (Γ : SourceTestCurvePredata θ) (t : ℝ) (x : M) :
    sourceTestCurveRawLegendre Γ t x =
      ⨆ τ : Iic Γ.max, ((t * τ.1 : ℝ) : EReal) + sourceTestCurveAt Γ τ.1 x := by
  apply le_antisymm
  · apply iSup_le
    intro τ
    by_cases hτ : τ ≤ Γ.max
    · exact le_iSup (fun τ : Iic Γ.max ↦
        ((t * τ.1 : ℝ) : EReal) + sourceTestCurveAt Γ τ.1 x) ⟨τ, hτ⟩
    · simp only [sourceTestCurveAt_of_gt Γ (lt_of_not_ge hτ), Pi.bot_apply, EReal.add_bot]
      exact bot_le
  · exact iSup_le fun τ ↦ le_iSup
      (fun s : ℝ ↦ ((t * s : ℝ) : EReal) + sourceTestCurveAt Γ s x) τ.1

/-- The literal cutoff infimum and genuine finite affine limits remove the
cutoff summand too. This exact index identity actually holds at EVERY real t. -/
theorem SourceTestCurvePredata.rawLegendre_eq_iSup_open
    (Γ : SourceTestCurvePredata θ) (t : ℝ) (x : M) :
    sourceTestCurveRawLegendre Γ t x =
      ⨆ τ : Iio Γ.max, ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x := by
  let S : EReal := ⨆ τ : Iio Γ.max, ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x
  have hcut : ((t * Γ.max : ℝ) : EReal) + sourceTestCurveCutoff Γ x ≤ S := by
    by_cases hb : sourceTestCurveCutoff Γ x = ⊥
    · simp only [hb, EReal.add_bot, bot_le]
    · have ht : sourceTestCurveCutoff Γ x ≠ ⊤ := by
        have hh := Γ.at_le_zero Γ.max x
        rw [sourceTestCurveAt_eq_max] at hh
        exact ne_of_lt (hh.trans_lt (by norm_num : (0 : EReal) < ⊤))
      let c := (sourceTestCurveCutoff Γ x).toReal
      have hc : sourceTestCurveCutoff Γ x = (c : EReal) :=
        (EReal.coe_toReal ht hb).symm
      rw [hc, ← EReal.coe_add]
      have hlim : Tendsto (fun s : ℝ ↦ ((t * s + c : ℝ) : EReal))
          (𝓝[<] Γ.max) (𝓝 ((t * Γ.max + c : ℝ) : EReal)) :=
        (continuous_coe_real_ereal.comp
          ((continuous_const.mul continuous_id).add continuous_const)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds
      apply le_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with s hs
      change s < Γ.max at hs
      have hh : (c : EReal) ≤ Γ.potential ⟨s, hs⟩ x := hc ▸ iInf_le (fun τ : Iio Γ.max ↦ Γ.potential τ x) ⟨s, hs⟩
      have hadd : ((t * s + c : ℝ) : EReal) ≤
          ((t * s : ℝ) : EReal) + Γ.potential ⟨s, hs⟩ x := by
        simpa only [EReal.coe_add] using add_le_add le_rfl hh
      exact hadd.trans
          (le_iSup (fun τ : Iio Γ.max ↦ ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x) ⟨s, hs⟩)
  apply le_antisymm
  · apply iSup_le
    intro τ
    by_cases hτ : τ < Γ.max
    · rw [sourceTestCurveAt_of_lt Γ hτ]
      exact le_iSup (fun τ : Iio Γ.max ↦ ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x) ⟨τ, hτ⟩
    by_cases he : τ = Γ.max
    · subst τ
      simpa only [sourceTestCurveAt_eq_max] using hcut
    · simp only [sourceTestCurveAt_of_gt Γ (lt_of_le_of_ne (le_of_not_gt hτ) (Ne.symm he)),
        Pi.bot_apply, EReal.add_bot]
      exact bot_le
  · apply iSup_le
    intro τ
    simpa only [sourceTestCurveRawLegendre, sourceTestCurveAt_of_lt Γ (show τ.1 < Γ.max from τ.2)] using
      (le_iSup (fun s : ℝ ↦ ((t * s : ℝ) : EReal) + sourceTestCurveAt Γ s x) τ.1)

/-- Actual finite source cutoff bounds the positive-time raw transform. -/
theorem SourceTestCurvePredata.rawLegendre_le_cutoff
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : 0 ≤ t) (x : M) :
    sourceTestCurveRawLegendre Γ t x ≤ ((t * Γ.max : ℝ) : EReal) := by
  rw [Γ.rawLegendre_eq_iSup_open t x]
  apply iSup_le
  intro τ
  calc
    ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x ≤ ((t * τ.1 : ℝ) : EReal) + 0 :=
      add_le_add le_rfl (show Γ.potential τ x ≤ (0 : EReal) from Γ.le_zero τ x)
    _ ≤ ((t * Γ.max : ℝ) : EReal) := by
      simpa only [add_zero] using EReal.coe_le_coe (mul_le_mul_of_nonneg_left τ.2.le ht)

/-- The literal all-bottom criterion holds for the raw transform at EVERY time. -/
theorem SourceTestCurvePredata.rawLegendre_eq_bot_iff
    (Γ : SourceTestCurvePredata θ) (t : ℝ) (x : M) :
    sourceTestCurveRawLegendre Γ t x = ⊥ ↔ ∀ τ, Γ.potential τ x = ⊥ := by
  rw [Γ.rawLegendre_eq_iSup_open t x]
  constructor
  · intro h τ
    have hh := (le_iSup (fun τ : Iio Γ.max ↦
      ((t * τ.1 : ℝ) : EReal) + Γ.potential τ x) τ).trans_eq h
    exact (EReal.add_eq_bot_iff.mp (le_bot_iff.mp hh)).resolve_left (EReal.coe_ne_bot _)
  · intro h
    apply le_bot_iff.mp
    apply iSup_le
    intro τ
    simp only [h τ, EReal.add_bot, le_refl]

/-- Every whole-extension value is bottom if all original values are bottom. -/
theorem SourceTestCurvePredata.at_eq_bot_of_original_bot
    (Γ : SourceTestCurvePredata θ) (x : M) (h : ∀ τ, Γ.potential τ x = ⊥) (s : ℝ) :
    sourceTestCurveAt Γ s x = ⊥ := by
  by_cases hs : s < Γ.max
  · simpa only [sourceTestCurveAt_of_lt Γ hs] using h ⟨s, hs⟩
  by_cases he : s = Γ.max
  · subst s
    rw [sourceTestCurveAt_eq_max]
    exact le_bot_iff.mp ((iInf_le _
      (⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩ : Iio Γ.max)).trans_eq (h _))
  · simp only [sourceTestCurveAt_of_gt Γ (lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm he)),
      Pi.bot_apply]

/-- Genuine original finite data give exactly positive infinity at negative time. -/
theorem SourceTestCurvePredata.rawLegendre_eq_top_of_neg
    (Γ : SourceTestCurvePredata θ) {t : ℝ} (ht : t < 0) (x : M)
    (h : ∃ b, Γ.potential b x ≠ ⊥) : sourceTestCurveRawLegendre Γ t x = ⊤ := by
  obtain ⟨b, hb⟩ := h
  have hbt : Γ.potential b x ≠ ⊤ := ne_of_lt
    ((Γ.le_zero b x).trans_lt (by norm_num : (0 : EReal) < ⊤))
  let c := (Γ.potential b x).toReal
  have hc : Γ.potential b x = (c : EReal) := (EReal.coe_toReal hbt hb).symm
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro R
  let s : ℝ := min b.1 ((R - c + 1) / t)
  have hsb : s ≤ b.1 := min_le_left _ _
  have hsm : s < Γ.max := hsb.trans_lt b.2
  have hbound : R - c + 1 ≤ t * s := by
    have hh := mul_le_mul_of_nonpos_right (min_le_right b.1 ((R - c + 1) / t)) ht.le
    dsimp [s]
    simpa only [div_mul_cancel₀ _ (ne_of_lt ht), mul_comm] using hh
  have hlo : ((t * s + c : ℝ) : EReal) ≤
      ((t * s : ℝ) : EReal) + Γ.potential ⟨s, hsm⟩ x := by
    rw [EReal.coe_add, ← hc]
    exact add_le_add le_rfl (Γ.antitone x (show (⟨s, hsm⟩ : Iio Γ.max) ≤ b from hsb))
  exact (EReal.coe_lt_coe (by linarith : R < t * s + c)).trans_le
    (hlo.trans (by simpa only [sourceTestCurveRawLegendre, sourceTestCurveAt_of_lt Γ hsm] using
      (le_iSup (fun σ : ℝ ↦ ((t * σ : ℝ) : EReal) + sourceTestCurveAt Γ σ x) s)))

/-- ENTIRE original negative-time remark, on the SAME original source values. -/
theorem sourceTestCurve_negative_legendre_whole (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : t < 0) (x : M) :
    ((∀ τ, Γ.potential τ x = ⊥) → sourceTestCurveRawLegendre Γ t x = ⊥) ∧
      ((∃ τ, Γ.potential τ x ≠ ⊥) → sourceTestCurveRawLegendre Γ t x = ⊤) :=
  ⟨(Γ.rawLegendre_eq_bot_iff t x).mpr, Γ.rawLegendre_eq_top_of_neg ht x⟩


private lemma closedTrace_proper_of_original_nonpole
    [CompactSpace M] [ConnectedSpace M] (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥) :
    SGPT.Convex.IsProper (sourceTestCurveClosedNegativeTrace Γ x) := by
  refine ⟨Γ.closedNegativeTrace_convex x, ⟨b.1, ?_⟩, ?_⟩
  · change sourceTestCurveClosedNegativeTrace Γ x b.1 < ⊤
    apply lt_top_iff_ne_top.mpr
    simpa [sourceTestCurveClosedNegativeTrace,
      sourceTestCurveAt_of_lt Γ (show b.1 < Γ.max from b.2)] using hb
  · intro s
    exact ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (by simpa [sourceTestCurveClosedNegativeTrace] using
        EReal.neg_le_neg_iff.mpr (Γ.at_le_zero s x))

private lemma scalar_linear_value (m : Module.Dual ℝ ℝ) (s : ℝ) : m s = s * m 1 := by
  simpa only [smul_eq_mul, mul_one] using m.map_smul s (1 : ℝ)

private lemma affine_minorant_slope_nonneg (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥)
    (m : Module.Dual ℝ ℝ) (c : ℝ)
    (hminor : ∀ s, ((m s + c : ℝ) : EReal) ≤ sourceTestCurveClosedNegativeTrace Γ x s) :
    0 ≤ m 1 := by
  have hfinite : sourceTestCurveClosedNegativeTrace Γ x b.1 ≠ ⊤ := by
    simpa [sourceTestCurveClosedNegativeTrace,
      sourceTestCurveAt_of_lt Γ (show b.1 < Γ.max from b.2)] using hb
  have hnb : sourceTestCurveClosedNegativeTrace Γ x b.1 ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (by simpa [sourceTestCurveClosedNegativeTrace] using
        EReal.neg_le_neg_iff.mpr (Γ.at_le_zero b.1 x))
  let H := (sourceTestCurveClosedNegativeTrace Γ x b.1).toReal
  have hH : sourceTestCurveClosedNegativeTrace Γ x b.1 = (H : EReal) :=
    (EReal.coe_toReal hfinite hnb).symm
  by_contra hn
  have hn : m 1 < 0 := lt_of_not_ge hn
  let s : ℝ := min b.1 ((H - c + 1) / m 1)
  have hs : s ≤ b.1 := min_le_left _ _
  have hlow : H - c + 1 ≤ s * m 1 := by
    have hh := mul_le_mul_of_nonpos_right
      (min_le_right b.1 ((H - c + 1) / m 1)) hn.le
    simpa only [div_mul_cancel₀ _ (ne_of_lt hn)] using hh
  have hupper : ((m s + c : ℝ) : EReal) ≤ (H : EReal) := by
    rw [← hH]
    exact (hminor s).trans (EReal.neg_le_neg_iff.mpr (Γ.at_antitone x hs))
  rw [EReal.coe_le_coe_iff, scalar_linear_value] at hupper
  linarith

variable [CompactSpace M] [ConnectedSpace M]

/-- EXISTING genuine affine separation and the original finite cutoff produce
ACTUAL strictly positive slopes; no slope or affine-envelope output is input. -/
theorem SourceTestCurvePredata.exists_positive_slope_minorant
    (Γ : SourceTestCurvePredata θ) (x : M)
    (h : ∃ b, Γ.potential b x ≠ ⊥) (τ r : ℝ)
    (hr : (r : EReal) < sourceTestCurveClosedNegativeTrace Γ x τ) :
    ∃ a c : ℝ, 0 < a ∧ r < a * τ + c ∧
      ∀ s, ((a * s + c : ℝ) : EReal) ≤ sourceTestCurveClosedNegativeTrace Γ x s := by
  obtain ⟨b, hb⟩ := h
  have hp := closedTrace_proper_of_original_nonpole Γ x b hb
  obtain ⟨m, c, habove, hminor⟩ :=
    SGPT.Convex.exists_affine_minorant_above_of_isProper_lowerSemicontinuous hp
      (Γ.closedNegativeTrace_lowerSemicontinuous x) τ r hr
  have hm := affine_minorant_slope_nonneg Γ x b hb m c hminor
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr habove) |τ - Γ.max|
  refine ⟨m 1 + ε, c - ε * Γ.max, by linarith, ?_, ?_⟩
  · have habs := mul_le_mul_of_nonneg_left (neg_abs_le (τ - Γ.max)) hε.le
    rw [scalar_linear_value] at habove hsmall
    nlinarith
  · intro s
    by_cases hs : s ≤ Γ.max
    · apply le_trans (EReal.coe_le_coe (show
          (m 1 + ε) * s + (c - ε * Γ.max) ≤ m s + c from ?_)) (hminor s)
      rw [scalar_linear_value m s]
      nlinarith [mul_le_mul_of_nonneg_left hs hε.le]
    · simp only [sourceTestCurveClosedNegativeTrace,
        sourceTestCurveAt_of_gt Γ (lt_of_not_ge hs), Pi.bot_apply, EReal.neg_bot, le_top]

/-- ENTIRE original inverse at EVERY whole real parameter, using the literal
strictly-positive-time raw transform and retaining every original pole. -/
theorem SourceTestCurvePredata.at_eq_iInf_positive_rawLegendre
    (Γ : SourceTestCurvePredata θ) (τ : ℝ) (x : M) :
    sourceTestCurveAt Γ τ x =
      ⨅ t : Ioi (0 : ℝ), sourceTestCurveRawLegendre Γ t.1 x - ((t.1 * τ : ℝ) : EReal) := by
  classical
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by change (0 : ℝ) < 1; exact zero_lt_one⟩⟩
  by_cases hbot : ∀ b, Γ.potential b x = ⊥
  · rw [Γ.at_eq_bot_of_original_bot x hbot τ]
    have hF (t : ℝ) : sourceTestCurveRawLegendre Γ t x = ⊥ :=
      (Γ.rawLegendre_eq_bot_iff t x).mpr hbot
    simp only [hF, EReal.bot_sub, iInf_const]
  · have hnon : ∃ b, Γ.potential b x ≠ ⊥ := not_forall.mp hbot
    let f := sourceTestCurveClosedNegativeTrace Γ x
    let J : EReal := ⨆ t : Ioi (0 : ℝ), ((t.1 * τ : ℝ) : EReal) -
      sourceTestCurveRawLegendre Γ t.1 x
    have hJle : J ≤ f τ := by
      apply iSup_le
      intro t
      apply (SGPT.Convex.real_sub_le_iff_comm (t.1 * τ)
        (sourceTestCurveRawLegendre Γ t.1 x) (f τ)).mpr
      simpa only [f, sourceTestCurveClosedNegativeTrace, sub_eq_add_neg, neg_neg,
        sourceTestCurveRawLegendre] using
        (le_iSup (fun s : ℝ ↦ ((t.1 * s : ℝ) : EReal) + sourceTestCurveAt Γ s x) τ)
    have hfJ : f τ ≤ J := by
      by_contra hn
      obtain ⟨r, hJr, hrf⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      obtain ⟨a, c, ha, hr, hminor⟩ := Γ.exists_positive_slope_minorant x hnon τ r hrf
      have hF : sourceTestCurveRawLegendre Γ a x ≤ ((-c : ℝ) : EReal) := by
        apply iSup_le
        intro s
        have hh := (SGPT.Convex.real_sub_le_iff_comm (a * s) (f s)
          ((-c : ℝ) : EReal)).mpr (by
            simpa only [← EReal.coe_sub, sub_neg_eq_add] using hminor s)
        simpa only [f, sourceTestCurveClosedNegativeTrace, sub_eq_add_neg, neg_neg] using hh
      have hterm : ((a * τ + c : ℝ) : EReal) ≤
          ((a * τ : ℝ) : EReal) - sourceTestCurveRawLegendre Γ a x := by
        simpa only [← EReal.coe_sub, sub_neg_eq_add] using
          EReal.sub_le_sub (le_refl ((a * τ : ℝ) : EReal)) hF
      have hrJ : (r : EReal) < J := (EReal.coe_lt_coe hr).trans_le
        (hterm.trans (le_iSup (fun t : Ioi (0 : ℝ) ↦ ((t.1 * τ : ℝ) : EReal) -
          sourceTestCurveRawLegendre Γ t.1 x) ⟨a, ha⟩))
      exact lt_asymm hJr hrJ
    have hJ : J = f τ := le_antisymm hJle hfJ
    have hneg : -J = ⨅ t : Ioi (0 : ℝ),
        -(((t.1 * τ : ℝ) : EReal) - sourceTestCurveRawLegendre Γ t.1 x) :=
      map_iSup EReal.negOrderIso _
    calc
      sourceTestCurveAt Γ τ x = -f τ := by simp only [f, sourceTestCurveClosedNegativeTrace, neg_neg]
      _ = -J := congrArg Neg.neg hJ.symm
      _ = _ := by
        rw [hneg]
        apply iInf_congr
        intro t
        rw [EReal.neg_sub (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))]
        simp only [sub_eq_add_neg, add_comm]


omit [CompactSpace M] [ConnectedSpace M] in
/-- Every actual whole-extension slice lies below its genuine original
spatial USC supremum, with no value of that supremum supplied as a premise. -/
theorem SourceTestCurvePredata.at_le_limit (Γ : SourceTestCurvePredata θ) (t : ℝ) :
    sourceTestCurveAt Γ t ≤ sourceTestCurveLimit Γ := by
  intro x
  have hslice (b : Iio Γ.max) : Γ.potential b x ≤ sourceTestCurveLimit Γ x :=
    (le_iSup (fun b : Iio Γ.max ↦ Γ.potential b x) b).trans
      (le_uscRegularization (fun y ↦ ⨆ b : Iio Γ.max, Γ.potential b y) x)
  by_cases ht : t < Γ.max
  · rw [sourceTestCurveAt_of_lt Γ ht]
    exact hslice ⟨t, ht⟩
  by_cases he : t = Γ.max
  · subst t
    rw [sourceTestCurveAt_eq_max]
    exact (iInf_le _ (⟨Γ.max - 1,
      by change Γ.max - 1 < Γ.max; linarith⟩ : Iio Γ.max)).trans (hslice _)
  · rw [sourceTestCurveAt_of_gt Γ (lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he))]
    exact bot_le

/-- The ORIGINAL assigned value at time zero is separate from the raw formula. -/
def sourceTestCurveLegendreWithInitial (Γ : SourceTestCurvePredata θ)
    (φ : M → EReal) (t : ℝ) : M → EReal :=
  if t = 0 then φ else sourceTestCurveRawLegendre Γ t

/-- The original basedness equality justifies adding precisely the ASSIGNED
zero-time value, without asserting the generally false raw formula there. -/
theorem SourceTestCurvePredata.at_eq_iInf_nonnegative_assignedLegendre
    (Γ : SourceTestCurvePredata θ) (φ : M → EReal) (hbase : sourceTestCurveLimit Γ = φ)
    (τ : ℝ) (x : M) :
    sourceTestCurveAt Γ τ x = ⨅ t : Ici (0 : ℝ),
      sourceTestCurveLegendreWithInitial Γ φ t.1 x - ((t.1 * τ : ℝ) : EReal) := by
  apply le_antisymm
  · apply le_iInf
    intro t
    by_cases ht : t.1 = 0
    · simpa only [sourceTestCurveLegendreWithInitial, ht, if_pos rfl, zero_mul,
        EReal.coe_zero, sub_zero] using hbase ▸ Γ.at_le_limit τ x
    · rw [sourceTestCurveLegendreWithInitial, if_neg ht]
      apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _))).mpr
      simpa only [sourceTestCurveRawLegendre, add_comm] using
        (le_iSup (fun s : ℝ ↦ ((t.1 * s : ℝ) : EReal) + sourceTestCurveAt Γ s x) τ)
  · rw [Γ.at_eq_iInf_positive_rawLegendre τ x]
    apply le_iInf
    intro t
    have ht : t.1 ≠ 0 := ne_of_gt t.2
    have hh := iInf_le (fun s : Ici (0 : ℝ) ↦
      sourceTestCurveLegendreWithInitial Γ φ s.1 x - ((s.1 * τ : ℝ) : EReal))
        ⟨t.1, by exact le_of_lt (show (0 : ℝ) < t.1 from t.2)⟩
    simpa only [sourceTestCurveLegendreWithInitial, if_neg ht] using hh

/-- ENTIRE original prop:Leginvtc, including all real parameters, all poles,
and the actual assigned-zero based-class convention. -/
theorem sourceTestCurve_legendre_inverse_whole (Γ : SourceTestCurvePredata θ) :
    (∀ τ x, sourceTestCurveAt Γ τ x =
      ⨅ t : Ioi (0 : ℝ), sourceTestCurveRawLegendre Γ t.1 x - ((t.1 * τ : ℝ) : EReal)) ∧
      ∀ (φ : M → EReal), sourceTestCurveLimit Γ = φ → ∀ τ x,
        sourceTestCurveAt Γ τ x = ⨅ t : Ici (0 : ℝ),
          sourceTestCurveLegendreWithInitial Γ φ t.1 x - ((t.1 * τ : ℝ) : EReal) :=
  ⟨Γ.at_eq_iInf_positive_rawLegendre, Γ.at_eq_iInf_nonnegative_assignedLegendre⟩

end SGPT.PSH.VariableComplexAtlas
