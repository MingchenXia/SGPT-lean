import SGPT.PSH.SourceTestCurveFoundation
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.Convex.DirectionalDerivative
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The literal infimum over EVERY earlier original real parameter. -/
def sourceTestCurveEarlierInf (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) : M → EReal :=
  fun x ↦ ⨅ σ : Iio τ.1, Γ.potential ⟨σ.1, by exact lt_trans (show σ.1 < τ.1 from σ.2) (show τ.1 < Γ.max from τ.2)⟩ x

private lemma negativeTrace_nonneg (Γ : SourceTestCurvePredata θ) (x : M) (t : ℝ) :
    0 ≤ sourceTestCurveNegativeTrace Γ.max Γ.potential x t := by
  by_cases ht : t < Γ.max
  · simpa [sourceTestCurveNegativeTrace, ht] using
      EReal.neg_le_neg_iff.mpr (Γ.le_zero ⟨t, ht⟩ x)
  · simp [sourceTestCurveNegativeTrace, ht]

private lemma negativeTrace_finite_before (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥)
    {t : ℝ} (ht : t < b.1) :
    sourceTestCurveNegativeTrace Γ.max Γ.potential x t ≠ ⊤ := by
  have htm : t < Γ.max := ht.trans b.2
  have hbot : Γ.potential ⟨t, htm⟩ x ≠ ⊥ :=
    ne_bot_of_le_ne_bot hb (Γ.antitone x (show (⟨t, htm⟩ : Iio Γ.max) ≤ b from ht.le))
  simpa [sourceTestCurveNegativeTrace, htm] using hbot

private lemma negativeTrace_continuousAt (Γ : SourceTestCurvePredata θ)
    (x : M) (b : Iio Γ.max) (hb : Γ.potential b x ≠ ⊥)
    {t : ℝ} (ht : t < b.1) :
    ContinuousAt (sourceTestCurveNegativeTrace Γ.max Γ.potential x) t := by
  let f := sourceTestCurveNegativeTrace Γ.max Γ.potential x
  have hnb (s : ℝ) : f s ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥) (negativeTrace_nonneg Γ x s)
  have hp : SGPT.Convex.IsProper f := ⟨Γ.concave x,
    ⟨t, lt_top_iff_ne_top.mpr (negativeTrace_finite_before Γ x b hb ht)⟩, hnb⟩
  have hsub : Iio b.1 ⊆ SGPT.Convex.effectiveDomain f := by
    intro s hs
    exact lt_top_iff_ne_top.mpr (negativeTrace_finite_before Γ x b hb hs)
  have hint : t ∈ interior (SGPT.Convex.effectiveDomain f) :=
    mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Iio_mem_nhds ht) hsub)
  have hc : ContinuousAt (fun s ↦ (f s).toReal) t :=
    ((SGPT.Convex.convexOn_toReal_effectiveDomain hp).continuousOn_interior t hint).continuousAt
      (isOpen_interior.mem_nhds hint)
  apply (continuous_coe_real_ereal.continuousAt.comp hc).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact (EReal.coe_toReal (negativeTrace_finite_before Γ x b hb hs) (hnb s)).symm

variable [CompactSpace M] [ConnectedSpace M]

/-- Existing zero-mass-allowed directed fixedpoint noncollapse produces genuine
PSH for the WHOLE earlier infimum, without a limit certificate. -/
theorem SourceTestCurvePredata.earlierInf_thetaPSH
    (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveEarlierInf Γ τ) := by
  have : Nonempty (Iio τ.1) := ⟨⟨τ.1 - 1, by change τ.1 - 1 < τ.1; linarith⟩⟩
  exact sourceOrdinaryFixedPoint_directedInf_thetaPSH
    (fun σ : Iio τ.1 ↦ Γ.potential ⟨σ.1, by exact lt_trans (show σ.1 < τ.1 from σ.2) (show τ.1 < Γ.max from τ.2)⟩)
    (fun σ ↦ Γ.thetaPSH _) (fun σ ↦ Γ.fixedPoint _)
    (fun x i j hij ↦ Γ.antitone x hij)

/-- Actual finite-domain convex continuity and genuine pole-set comparison
identify the literal earlier infimum at EVERY point, including every pole. -/
theorem SourceTestCurvePredata.earlierInf_eq
    (Γ : SourceTestCurvePredata θ) (τ : Iio Γ.max) :
    sourceTestCurveEarlierInf Γ τ = Γ.potential τ := by
  have hτm : τ.1 < Γ.max := τ.2
  let b : Iio Γ.max := ⟨(τ.1 + Γ.max) / 2, by change (τ.1 + Γ.max) / 2 < Γ.max; linarith⟩
  have hτb : τ.1 < b.1 := by dsimp [b]; linarith
  have hlow : Γ.potential τ ≤ sourceTestCurveEarlierInf Γ τ := by
    intro x
    change Γ.potential τ x ≤ ⨅ σ : Iio τ.1, _
    exact le_iInf fun σ ↦ Γ.antitone x (show (⟨σ.1, by exact lt_trans (show σ.1 < τ.1 from σ.2) (show τ.1 < Γ.max from τ.2)⟩ : Iio Γ.max) ≤ τ from le_of_lt σ.2)
  apply le_antisymm ?_ hlow
  apply (sourceQuasiEverywhere_le_iff (Γ.earlierInf_thetaPSH τ) (Γ.thetaPSH τ)).mp
  apply (sourceQuasiEverywhere_iff_native _).mpr
  apply (quasiPsh_finite_quasiEverywhere (Γ.native_thetaPSH b).quasiPshPotential).mono
  intro x hx
  have hc := negativeTrace_continuousAt Γ x b hx.1 hτb
  have hlim : Tendsto
      (fun s ↦ -sourceTestCurveNegativeTrace Γ.max Γ.potential x s)
      (𝓝[<] τ.1) (𝓝 (Γ.potential τ x)) := by
    have hh := hc.neg.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio τ.1))
    have heq : -sourceTestCurveNegativeTrace Γ.max Γ.potential x τ.1 = Γ.potential τ x := by
      simp [sourceTestCurveNegativeTrace, hτm]
    change Tendsto (fun s ↦ -sourceTestCurveNegativeTrace Γ.max Γ.potential x s)
      (𝓝[<] τ.1) (𝓝 (-sourceTestCurveNegativeTrace Γ.max Γ.potential x τ.1)) at hh
    rw [heq] at hh
    exact hh
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  change s < τ.1 at hs
  simpa [sourceTestCurveEarlierInf, sourceTestCurveNegativeTrace, hs.trans hτm] using
    (iInf_le (fun σ : Iio τ.1 ↦ Γ.potential ⟨σ.1, by exact lt_trans (show σ.1 < τ.1 from σ.2) (show τ.1 < Γ.max from τ.2)⟩ x) ⟨s, hs⟩)


omit [CompactSpace M] [ConnectedSpace M] in
/-- The exact three original branches are decreasing on the WHOLE real line. -/
theorem SourceTestCurvePredata.at_antitone (Γ : SourceTestCurvePredata θ) (x : M) :
    Antitone (fun t ↦ sourceTestCurveAt Γ t x) := by
  intro s t hst
  change sourceTestCurveAt Γ t x ≤ sourceTestCurveAt Γ s x
  by_cases ht : t < Γ.max
  · have hs : s < Γ.max := hst.trans_lt ht
    rw [sourceTestCurveAt_of_lt Γ ht, sourceTestCurveAt_of_lt Γ hs]
    exact Γ.antitone x hst
  by_cases hte : t = Γ.max
  · subst t
    rcases hst.eq_or_lt with rfl | hs
    · exact le_rfl
    · rw [sourceTestCurveAt_eq_max, sourceTestCurveAt_of_lt Γ hs]
      exact iInf_le (fun r : Iio Γ.max ↦ Γ.potential r x) ⟨s, hs⟩
  · rw [sourceTestCurveAt_of_gt Γ (lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm hte))]
    exact bot_le

/-- Every whole-extension value is literally the infimum of ALL earlier values. -/
theorem SourceTestCurvePredata.at_eq_earlierInf (Γ : SourceTestCurvePredata θ)
    (x : M) (t : ℝ) : sourceTestCurveAt Γ t x =
      ⨅ s : Iio t, sourceTestCurveAt Γ s.1 x := by
  apply le_antisymm
  · exact le_iInf fun s ↦ Γ.at_antitone x (show s.1 ≤ t from le_of_lt s.2)
  · by_cases ht : t < Γ.max
    · rw [sourceTestCurveAt_of_lt Γ ht, ← Γ.earlierInf_eq ⟨t, ht⟩]
      apply le_iInf
      intro s
      simpa only [sourceTestCurveAt_of_lt Γ (show s.1 < Γ.max from lt_trans s.2 ht)] using
        (iInf_le (fun s : Iio t ↦ sourceTestCurveAt Γ s.1 x) s)
    by_cases he : t = Γ.max
    · subst t
      rw [sourceTestCurveAt_eq_max]
      apply le_iInf
      intro s
      simpa only [sourceTestCurveAt_of_lt Γ s.2] using
        (iInf_le (fun s : Iio Γ.max ↦ sourceTestCurveAt Γ s.1 x) s)
    · have hgt : Γ.max < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he)
      let s : Iio t := ⟨(Γ.max + t) / 2, by change (Γ.max + t) / 2 < t; linarith⟩
      have hs : Γ.max < s.1 := by dsimp [s]; linarith
      rw [sourceTestCurveAt_of_gt Γ hgt]
      exact (iInf_le _ s).trans_eq (by simp only [sourceTestCurveAt_of_gt Γ hs, Pi.bot_apply])

/-- Genuine upper semicontinuity of the SAME whole real-parameter function. -/
theorem SourceTestCurvePredata.at_upperSemicontinuous (Γ : SourceTestCurvePredata θ)
    (x : M) : UpperSemicontinuous (fun t ↦ sourceTestCurveAt Γ t x) := by
  intro t a ha
  change sourceTestCurveAt Γ t x < a at ha
  rw [Γ.at_eq_earlierInf x t] at ha
  obtain ⟨s, hs⟩ := iInf_lt_iff.mp ha
  filter_upwards [Ioi_mem_nhds (show s.1 < t from s.2)] with r hr
  exact (Γ.at_antitone x hr.le).trans_lt hs

omit [CompactSpace M] [ConnectedSpace M] in
/-- Normalization is retained by the literal cutoff and bottom branches. -/
theorem SourceTestCurvePredata.at_le_zero (Γ : SourceTestCurvePredata θ) (t : ℝ) :
    sourceTestCurveAt Γ t ≤ 0 := by
  intro x
  by_cases ht : t < Γ.max
  · rw [sourceTestCurveAt_of_lt Γ ht]
    exact Γ.le_zero ⟨t, ht⟩ x
  by_cases he : t = Γ.max
  · subst t
    rw [sourceTestCurveAt_eq_max]
    exact (iInf_le _ ⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩).trans
      (Γ.le_zero _ x)
  · rw [sourceTestCurveAt_of_gt Γ (lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm he))]
    exact bot_le

/-- Negative of the WHOLE literal original extension, without any replacement. -/
def sourceTestCurveClosedNegativeTrace (Γ : SourceTestCurvePredata θ) (x : M) (t : ℝ) :
    EReal := -sourceTestCurveAt Γ t x

/-- Every positive shift of the unchanged open negative trace gives EXACTLY
its whole left completion after taking the actual arbitrary supremum. -/
theorem SourceTestCurvePredata.closedNegativeTrace_eq_shiftSup
    (Γ : SourceTestCurvePredata θ) (x : M) (t : ℝ) :
    sourceTestCurveClosedNegativeTrace Γ x t =
      ⨆ ε : Ioi (0 : ℝ), sourceTestCurveNegativeTrace Γ.max Γ.potential x (t - ε.1) := by
  by_cases ht : t ≤ Γ.max
  · apply le_antisymm
    · have h : -(⨆ ε : Ioi (0 : ℝ),
          sourceTestCurveNegativeTrace Γ.max Γ.potential x (t - ε.1)) ≤
          sourceTestCurveAt Γ t x := by
        rw [Γ.at_eq_earlierInf x t]
        apply le_iInf
        intro s
        let ε : Ioi (0 : ℝ) := ⟨t - s.1, by change 0 < t - s.1; exact sub_pos.mpr s.2⟩
        have hs : s.1 < Γ.max := lt_of_lt_of_le s.2 ht
        have he : t - ε.1 = s.1 := by dsimp [ε]; ring
        have hh := le_iSup (fun ε : Ioi (0 : ℝ) ↦
          sourceTestCurveNegativeTrace Γ.max Γ.potential x (t - ε.1)) ε
        rw [he, sourceTestCurveNegativeTrace, dif_pos hs] at hh
        rw [sourceTestCurveAt_of_lt Γ hs]
        exact EReal.neg_le_neg_iff.mp (by simpa only [neg_neg] using hh)
      exact EReal.neg_le_neg_iff.mp (by simpa [sourceTestCurveClosedNegativeTrace] using h)
    · apply iSup_le
      intro ε
      have hshift : t - ε.1 < Γ.max := by have := ε.2; change 0 < ε.1 at this; linarith
      rw [sourceTestCurveNegativeTrace, dif_pos hshift]
      change -Γ.potential ⟨t - ε.1, hshift⟩ x ≤ -sourceTestCurveAt Γ t x
      apply EReal.neg_le_neg_iff.mpr
      rw [← sourceTestCurveAt_of_lt Γ hshift]
      exact Γ.at_antitone x (by have := ε.2; change 0 < ε.1 at this; linarith)
  · have hgt : Γ.max < t := lt_of_not_ge ht
    have he : 0 < (t - Γ.max) / 2 := by linarith
    let ε : Ioi (0 : ℝ) := ⟨(t - Γ.max) / 2, he⟩
    have hshift : ¬ t - ε.1 < Γ.max := by dsimp [ε]; linarith
    rw [sourceTestCurveClosedNegativeTrace, sourceTestCurveAt_of_gt Γ hgt]
    change ⊤ = _
    symm
    apply top_unique
    simpa [sourceTestCurveNegativeTrace, hshift] using
      (le_iSup (fun ε : Ioi (0 : ℝ) ↦
        sourceTestCurveNegativeTrace Γ.max Γ.potential x (t - ε.1)) ε)

/-- Whole epigraph convexity is transported from genuine affine translates of
the original open trace, retaining both infinite endpoints. -/
theorem SourceTestCurvePredata.closedNegativeTrace_convex
    (Γ : SourceTestCurvePredata θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveClosedNegativeTrace Γ x) := by
  have heq : sourceTestCurveClosedNegativeTrace Γ x = fun t ↦
      ⨆ ε : Ioi (0 : ℝ), sourceTestCurveNegativeTrace Γ.max Γ.potential x (t - ε.1) :=
    funext (Γ.closedNegativeTrace_eq_shiftSup x)
  rw [heq]
  apply SGPT.Convex.isConvex_iSup
  intro ε
  let L : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (-ε.1)
  simpa [L, Function.comp_def, sub_eq_add_neg] using
    SGPT.Convex.isConvex_comp_affineMap (Γ.concave x) L

/-- Exact lower semicontinuity by literal extended-order reversal. -/
theorem SourceTestCurvePredata.closedNegativeTrace_lowerSemicontinuous
    (Γ : SourceTestCurvePredata θ) (x : M) :
    LowerSemicontinuous (sourceTestCurveClosedNegativeTrace Γ x) := by
  intro t a ha
  have hh : sourceTestCurveAt Γ t x < -a :=
    EReal.neg_lt_neg_iff.mp (by simpa [sourceTestCurveClosedNegativeTrace] using ha)
  filter_upwards [Γ.at_upperSemicontinuous x t (-a) hh] with s hs
  exact EReal.neg_lt_neg_iff.mp (by simpa [sourceTestCurveClosedNegativeTrace] using hs)

/-- The whole original function is closed concave, including the allowed
identically-bottom case and actual finite terminal effective-domain values. -/
theorem SourceTestCurvePredata.closedNegativeTrace_closed
    (Γ : SourceTestCurvePredata θ) (x : M) :
    SGPT.Convex.IsClosedConvex (sourceTestCurveClosedNegativeTrace Γ x) := by
  by_cases htop : sourceTestCurveClosedNegativeTrace Γ x = fun _ ↦ ⊤
  · exact Or.inr (Or.inl htop)
  · refine Or.inr (Or.inr ⟨⟨Γ.closedNegativeTrace_convex x, ?_, ?_⟩,
      Γ.closedNegativeTrace_lowerSemicontinuous x⟩)
    · obtain ⟨t, ht⟩ := Function.ne_iff.mp htop
      exact ⟨t, lt_top_iff_ne_top.mpr ht⟩
    · intro t
      exact ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
        (by simpa [sourceTestCurveClosedNegativeTrace] using
          EReal.neg_le_neg_iff.mpr (Γ.at_le_zero t x))

/-- On precisely the printed cutoff nonpole locus, the SAME negative trace is
proper; no positive cutoff mass or supplied finite readback is required. -/
theorem SourceTestCurvePredata.closedNegativeTrace_proper_of_cutoff_nonpole
    (Γ : SourceTestCurvePredata θ) (x : M) (hx : sourceTestCurveCutoff Γ x ≠ ⊥) :
    SGPT.Convex.IsProper (sourceTestCurveClosedNegativeTrace Γ x) := by
  refine ⟨Γ.closedNegativeTrace_convex x, ⟨Γ.max, ?_⟩, ?_⟩
  · change -sourceTestCurveAt Γ Γ.max x < ⊤
    rw [sourceTestCurveAt_eq_max]
    exact lt_top_iff_ne_top.mpr (by simpa using hx)
  · intro t
    exact ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (by simpa [sourceTestCurveClosedNegativeTrace] using
        EReal.neg_le_neg_iff.mpr (Γ.at_le_zero t x))

/-- ENTIRE original prop:Gammaclosed: closed concavity of the literal whole
function at EVERY point and properness on exactly the cutoff nonpole locus.
The original preliminary clauses already suffice for this stronger domain. -/
theorem sourceTestCurve_closedness_whole (Γ : SourceTestCurvePredata θ) :
    (∀ x, SGPT.Convex.IsClosedConvex (sourceTestCurveClosedNegativeTrace Γ x)) ∧
      ∀ x, sourceTestCurveCutoff Γ x ≠ ⊥ →
        SGPT.Convex.IsProper (sourceTestCurveClosedNegativeTrace Γ x) :=
  ⟨Γ.closedNegativeTrace_closed, Γ.closedNegativeTrace_proper_of_cutoff_nonpole⟩

end SGPT.PSH.VariableComplexAtlas
