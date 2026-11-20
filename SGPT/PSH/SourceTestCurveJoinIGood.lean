import SGPT.PSH.SourceTestCurveJoinModel
import SGPT.Convex.DirectionalDerivative
import SGPT.PSH.SourceTestCurveSumIGood
import SGPT.PSH.SourceIGoodOperations
import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.Convex.WeightedRooftop
import SGPT.Envelopes.SourceRelativeEnvelopeExhaustion
import SGPT.PSH.SourceIVolumeGoodness

/-! # Genuine I-goodness of the original binary test-curve join

Open/whole convex-envelope comparison, actual global strict-parameter mixtures,
proper weighted tuples and genuine quasi-everywhere PSH comparison manufacture
the literal raw goodness. Original positive I-model union consumers retain all
source quantifiers. No closedness, cutoff goodness or output certificate is input.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set
open scoped BigOperators
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual convex envelope of the TWO original open negative traces. -/
def sourceTestCurveOpenConvexEnvelope (Γ Δ : SourceTestCurvePredata θ) (x : M) : ℝ → EReal :=
  SGPT.Convex.lowerConvexEnvelope (fun s => min
    (sourceTestCurveNegativeTrace Γ.max Γ.potential x s)
    (sourceTestCurveNegativeTrace Δ.max Δ.potential x s))

/-- Actual normalization holds for every original open negative trace. -/
theorem SourceTestCurvePredata.openNegativeTrace_nonneg (Γ : SourceTestCurvePredata θ)
    (x : M) (s : ℝ) : (0 : EReal) ≤ sourceTestCurveNegativeTrace Γ.max Γ.potential x s := by
  unfold sourceTestCurveNegativeTrace
  split_ifs with hs
  · exact EReal.neg_nonneg.mpr (Γ.le_zero ⟨s,hs⟩ x)
  · exact le_top

/-- Existing lower-envelope convexity applies to the literal open obstacle. -/
theorem sourceTestCurveOpenConvexEnvelope_convex (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveOpenConvexEnvelope Γ Δ x) :=
  SGPT.Convex.isConvex_lowerConvexEnvelope _

/-- Zero is an actual convex minorant, not a supplied finiteness certificate. -/
theorem sourceTestCurveOpenConvexEnvelope_nonneg (Γ Δ : SourceTestCurvePredata θ) (x : M) (s : ℝ) :
    (0 : EReal) ≤ sourceTestCurveOpenConvexEnvelope Γ Δ x s := by
  exact SGPT.Convex.le_lowerConvexEnvelope
    (g := fun _ : ℝ => (0 : EReal))
    (by simpa only [EReal.coe_zero] using SGPT.Convex.isConvex_const (V := ℝ) 0)
    (fun r => le_min (Γ.openNegativeTrace_nonneg x r) (Δ.openNegativeTrace_nonneg x r)) s

/-- Only the cutoff value differs; the whole trace lies below the open one. -/
theorem SourceTestCurvePredata.wholeNegativeTrace_le_open (Γ : SourceTestCurvePredata θ)
    (x : M) (s : ℝ) :
    -sourceTestCurveAt Γ s x ≤ sourceTestCurveNegativeTrace Γ.max Γ.potential x s := by
  by_cases hs : s < Γ.max
  · rw [sourceTestCurveNegativeTrace,dif_pos hs,sourceTestCurveAt_of_lt Γ hs]
  · rw [sourceTestCurveNegativeTrace,dif_neg hs]
    exact le_top

/-- The inclusion is valid at EVERY parameter without asserting closedness. -/
theorem sourceTestCurveWholeConvexEnvelope_le_open (Γ Δ : SourceTestCurvePredata θ) (x : M) :
    sourceTestCurveJoinConvexEnvelope Γ Δ x ≤ sourceTestCurveOpenConvexEnvelope Γ Δ x := by
  apply SGPT.Convex.lowerConvexEnvelope_mono
  intro s
  apply le_min
  · exact (EReal.neg_le_neg_iff.mpr (le_max_left _ _)).trans
      (Γ.wholeNegativeTrace_le_open x s)
  · exact (EReal.neg_le_neg_iff.mpr (le_max_right _ _)).trans
      (Δ.wholeNegativeTrace_le_open x s)

/-- A strictly positive shift puts each original input in its actual open branch. -/
theorem SourceTestCurvePredata.openNegativeTrace_shift_le_whole
    (Γ : SourceTestCurvePredata θ) (x : M) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    sourceTestCurveNegativeTrace Γ.max Γ.potential x (s-δ) ≤ -sourceTestCurveAt Γ s x := by
  by_cases hs : s ≤ Γ.max
  · have ho : s-δ < Γ.max := by linarith
    rw [sourceTestCurveNegativeTrace,dif_pos ho]
    have hh := EReal.neg_le_neg_iff.mpr (Γ.at_antitone x (show s-δ ≤ s by linarith))
    simpa only [sourceTestCurveAt_of_lt Γ ho] using hh
  · rw [sourceTestCurveAt_of_gt Γ (lt_of_not_ge hs)]
    simp only [Pi.bot_apply,EReal.neg_bot,le_top]

/-- Translation of the ACTUAL open envelope is a genuine whole-obstacle minorant. -/
theorem sourceTestCurveOpenConvexEnvelope_le_whole_shift
    (Γ Δ : SourceTestCurvePredata θ) (x : M) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    sourceTestCurveOpenConvexEnvelope Γ Δ x τ ≤
      sourceTestCurveJoinConvexEnvelope Γ Δ x (τ+δ) := by
  let L : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ δ
  have hc := SGPT.Convex.isConvex_comp_affineMap
    (sourceTestCurveOpenConvexEnvelope_convex Γ Δ x) L
  change SGPT.Convex.IsConvex (fun s => sourceTestCurveOpenConvexEnvelope Γ Δ x (s-δ)) at hc
  have hm : (fun s => sourceTestCurveOpenConvexEnvelope Γ Δ x (s-δ)) ≤
      fun s => -max (sourceTestCurveAt Γ s x) (sourceTestCurveAt Δ s x) := by
    intro s
    have hG : sourceTestCurveOpenConvexEnvelope Γ Δ x (s-δ) ≤ -sourceTestCurveAt Γ s x :=
      ((SGPT.Convex.lowerConvexEnvelope_le _ (s-δ)).trans (min_le_left _ _)).trans
        (Γ.openNegativeTrace_shift_le_whole x s hδ)
    have hD : sourceTestCurveOpenConvexEnvelope Γ Δ x (s-δ) ≤ -sourceTestCurveAt Δ s x :=
      ((SGPT.Convex.lowerConvexEnvelope_le _ (s-δ)).trans (min_le_right _ _)).trans
        (Δ.openNegativeTrace_shift_le_whole x s hδ)
    have hG' := EReal.neg_le_neg_iff.mpr hG
    have hD' := EReal.neg_le_neg_iff.mpr hD
    simp only [neg_neg] at hG' hD'
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr (max_le hG' hD')
  have hh := SGPT.Convex.le_lowerConvexEnvelope hc hm (τ+δ)
  change sourceTestCurveOpenConvexEnvelope Γ Δ x ((τ+δ)-δ) ≤
    sourceTestCurveJoinConvexEnvelope Γ Δ x (τ+δ) at hh
  simpa only [add_sub_cancel_right] using hh

/-- A genuine finite whole input above the parameter identifies open and whole
convex envelopes. No closedness or positive cutoff mass is assumed. -/
theorem sourceTestCurveOpenConvexEnvelope_eq_whole_of_finite_above
    (Γ Δ : SourceTestCurvePredata θ) (x : M) {τ a : ℝ} (ha : τ < a)
    (hfinite : sourceTestCurveAt Γ a x ≠ ⊥ ∨ sourceTestCurveAt Δ a x ≠ ⊥) :
    sourceTestCurveOpenConvexEnvelope Γ Δ x τ =
      sourceTestCurveJoinConvexEnvelope Γ Δ x τ := by
  let K := sourceTestCurveJoinConvexEnvelope Γ Δ x
  have hchoose : ∃ A : SourceTestCurvePredata θ,
      K ≤ (fun s => -sourceTestCurveAt A s x) ∧ sourceTestCurveAt A a x ≠ ⊥ := by
    rcases hfinite with hG | hD
    · exact ⟨Γ,sourceTestCurveJoinConvexEnvelope_le_left Γ Δ x,hG⟩
    · exact ⟨Δ,sourceTestCurveJoinConvexEnvelope_le_right Γ Δ x,hD⟩
  obtain ⟨A,hKA,hAa⟩ := hchoose
  have htop : -sourceTestCurveAt A a x ≠ ⊤ := by simpa using hAa
  have hKtop (s : ℝ) (hs : s ≤ a) : K s ≠ ⊤ :=
    ne_of_lt (((hKA s).trans (EReal.neg_le_neg_iff.mpr (A.at_antitone x hs))).trans_lt
      (lt_top_iff_ne_top.mpr htop))
  have hKbot (s : ℝ) : K s ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (show (0 : EReal) ≤ K s from sourceTestCurveJoinConvexEnvelope_nonneg Γ Δ x s)
  let U := (K τ).toReal
  let V := (K a).toReal
  have hU : K τ = (U : EReal) := (EReal.coe_toReal (hKtop τ ha.le) (hKbot τ)).symm
  have hV : K a = (V : EReal) := (EReal.coe_toReal (hKtop a le_rfl) (hKbot a)).symm
  have hupper : sourceTestCurveOpenConvexEnvelope Γ Δ x τ ≤ K τ := by
    by_contra hn
    obtain ⟨r,hUr,hrOpen⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    rw [hU,EReal.coe_lt_coe_iff] at hUr
    have hgap : 0 < min (r-U) 1 := lt_min (sub_pos.mpr hUr) zero_lt_one
    obtain ⟨t,ht,hsmall⟩ := exists_pos_mul_lt hgap (max 1 |V-U|)
    rw [mul_comm] at hsmall
    have ht1 : t < 1 := by
      have hle : t ≤ t * max 1 |V-U| := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) |V-U|) ht.le
      exact hle.trans_lt (hsmall.trans_le (min_le_right (r-U) 1))
    have hcost : (1-t)*U+t*V < r := by
      have hdiff : V-U ≤ max 1 |V-U| := (le_abs_self _).trans (le_max_right _ _)
      have hmul := mul_le_mul_of_nonneg_left hdiff ht.le
      have hsmall' := hsmall.trans_le (min_le_left (r-U) 1)
      nlinarith
    have hp : (τ,U) ∈ SGPT.Convex.epigraph K := by
      change K τ ≤ (U : EReal)
      rw [hU]
    have hq : (a,V) ∈ SGPT.Convex.epigraph K := by
      change K a ≤ (V : EReal)
      rw [hV]
    have hc := sourceTestCurveJoinConvexEnvelope_convex Γ Δ x hp hq
      (sub_pos.mpr ht1).le ht.le (show (1-t)+t=1 by ring)
    change K ((1-t)*τ+t*a) ≤ (((1-t)*U+t*V : ℝ) : EReal) at hc
    have harg : (1-t)*τ+t*a = τ+t*(a-τ) := by ring
    rw [harg] at hc
    have hs := sourceTestCurveOpenConvexEnvelope_le_whole_shift Γ Δ x τ
      (mul_pos ht (sub_pos.mpr ha))
    have hAll := hs.trans hc
    exact (not_lt_of_ge hAll) ((EReal.coe_lt_coe hcost).trans hrOpen)
  exact le_antisymm hupper (sourceTestCurveWholeConvexEnvelope_le_open Γ Δ x τ)

/-- The GLOBAL strict-parameter mixture indices; no spatial finiteness field. -/
structure SourceTestCurveJoinMixtureIndex (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ) where
  left : Iio Γ.max
  right : Iio Δ.max
  weight : Icc (0 : ℝ) 1
  barycenter : weight.1*left.1+(1-weight.1)*right.1 = τ

/-- A genuine global index below the first input cutoff. -/
theorem sourceTestCurveJoinMixtureIndex_nonempty_left (Γ Δ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ < Γ.max) : Nonempty (SourceTestCurveJoinMixtureIndex Γ Δ τ) := by
  let a := (τ+Γ.max)/2
  let b := min τ Δ.max-1
  have ha : τ < a := by dsimp [a]; linarith
  have ham : a < Γ.max := by dsimp [a]; linarith
  have hb : b < τ := by dsimp [b]; linarith [min_le_left τ Δ.max]
  have hbm : b < Δ.max := by dsimp [b]; linarith [min_le_right τ Δ.max]
  have hab : 0 < a-b := by linarith
  let w := (τ-b)/(a-b)
  have hw0 : 0 < w := div_pos (by linarith) hab
  have hw1 : w < 1 := (div_lt_one hab).mpr (by linarith)
  refine ⟨⟨⟨a,ham⟩,⟨b,hbm⟩,⟨w,hw0.le,hw1.le⟩,?_⟩⟩
  change w*a+(1-w)*b = τ
  dsimp [w]
  field_simp [ne_of_gt hab]
  ring

/-- Swapping actual inputs supplies a global index below the second cutoff. -/
theorem sourceTestCurveJoinMixtureIndex_nonempty_right (Γ Δ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ < Δ.max) : Nonempty (SourceTestCurveJoinMixtureIndex Γ Δ τ) := by
  obtain ⟨j⟩ := sourceTestCurveJoinMixtureIndex_nonempty_left Δ Γ hτ
  refine ⟨⟨j.right,j.left,⟨1-j.weight.1,sub_nonneg.mpr j.weight.2.2,?_⟩,?_⟩⟩
  · linarith [j.weight.2.1]
  · change (1-j.weight.1)*j.right.1+(1-(1-j.weight.1))*j.left.1 = τ
    nlinarith [j.barycenter]

/-- Every original strict join parameter has an actual global mixture. -/
theorem sourceTestCurveJoinMixtureIndex_nonempty (Γ Δ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ < max Γ.max Δ.max) : Nonempty (SourceTestCurveJoinMixtureIndex Γ Δ τ) := by
  rcases lt_max_iff.mp hτ with h | h
  · exact sourceTestCurveJoinMixtureIndex_nonempty_left Γ Δ h
  · exact sourceTestCurveJoinMixtureIndex_nonempty_right Γ Δ h

/-- Closed-weight endpoints select the ACTUAL input, without scaling at zero. -/
def sourceTestCurveJoinMixture (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ)
    (j : SourceTestCurveJoinMixtureIndex Γ Δ τ) : M → EReal :=
  if j.weight.1 = 0 then Δ.potential j.right
  else if j.weight.1 = 1 then Γ.potential j.left
  else convexComb j.weight.1 (Γ.potential j.left) (Δ.potential j.right)

/-- Every global mixture is genuinely PSH in the SAME original background. -/
theorem sourceTestCurveJoinMixture_thetaPSH (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) (j : SourceTestCurveJoinMixtureIndex Γ Δ τ) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveJoinMixture Γ Δ τ j) := by
  unfold sourceTestCurveJoinMixture
  split_ifs with hw0 hw1
  · exact Δ.thetaPSH j.right
  · exact Γ.thetaPSH j.left
  · apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    exact isThetaPshPotential_convexComb
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (Γ.thetaPSH j.left))
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (Δ.thetaPSH j.right))
      (lt_of_le_of_ne j.weight.2.1 (Ne.symm hw0))
      (lt_of_le_of_ne j.weight.2.2 hw1)

/-- Actual normalization bounds every mixture by the SAME finite zero. -/
theorem sourceTestCurveJoinMixture_le_zero (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) (j : SourceTestCurveJoinMixtureIndex Γ Δ τ) :
    sourceTestCurveJoinMixture Γ Δ τ j ≤ 0 := by
  unfold sourceTestCurveJoinMixture
  split_ifs
  · exact Δ.le_zero j.right
  · exact Γ.le_zero j.left
  · intro x
    change (j.weight.1 : EReal)*Γ.potential j.left x+
      ((1-j.weight.1 : ℝ) : EReal)*Δ.potential j.right x ≤ 0
    have hG := mul_nonpos_of_nonneg_of_nonpos
      (EReal.coe_nonneg.mpr j.weight.2.1) (Γ.le_zero j.left x)
    have hD := mul_nonpos_of_nonneg_of_nonpos
      (EReal.coe_nonneg.mpr (sub_nonneg.mpr j.weight.2.2)) (Δ.le_zero j.right x)
    simpa only [add_zero] using add_le_add hG hD

/-- The actual spatial USC supremum of GLOBAL strict-parameter mixtures. -/
def sourceTestCurveJoinMixtureUSC (Γ Δ : SourceTestCurvePredata θ) (τ : ℝ) : M → EReal :=
  uscRegularization (⨆ j : SourceTestCurveJoinMixtureIndex Γ Δ τ,
    sourceTestCurveJoinMixture Γ Δ τ j)

/-- The genuine arbitrary-family PSH mother needs no monotone-family premise. -/
theorem sourceTestCurveJoinMixtureUSC_thetaPSH (Γ Δ : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveJoinMixtureUSC Γ Δ τ) := by
  let : Nonempty (SourceTestCurveJoinMixtureIndex Γ Δ τ) :=
    sourceTestCurveJoinMixtureIndex_nonempty Γ Δ hτ
  exact sourceIncreasingSingularitySupremum_thetaPSH θ
    (fun j : SourceTestCurveJoinMixtureIndex Γ Δ τ =>
      ⟨sourceTestCurveJoinMixture Γ Δ τ j,sourceTestCurveJoinMixture_thetaPSH Γ Δ τ j⟩)
    (C := 0) (fun j x => by
      simpa only [EReal.coe_zero,Pi.zero_apply] using sourceTestCurveJoinMixture_le_zero Γ Δ τ j x)

/-- A finite actual cutoff makes the whole original OPEN negative trace proper. -/
theorem SourceTestCurvePredata.openNegativeTrace_isProper_of_cutoff_ne_bot
    (Γ : SourceTestCurvePredata θ) (x : M) (hfinite : sourceTestCurveCutoff Γ x ≠ ⊥) :
    SGPT.Convex.IsProper (sourceTestCurveNegativeTrace Γ.max Γ.potential x) := by
  have hstrict (r : Iio Γ.max) : Γ.potential r x ≠ ⊥ :=
    ne_bot_of_le_ne_bot hfinite (iInf_le (fun q : Iio Γ.max => Γ.potential q x) r)
  refine ⟨Γ.concave x,⟨Γ.max-1,?_⟩,?_⟩
  · have hr : Γ.max-1 < Γ.max := by linarith
    change sourceTestCurveNegativeTrace Γ.max Γ.potential x (Γ.max-1) < ⊤
    rw [sourceTestCurveNegativeTrace,dif_pos hr]
    exact lt_top_iff_ne_top.mpr (by simpa using hstrict ⟨Γ.max-1,hr⟩)
  · intro r
    exact ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
      (Γ.openNegativeTrace_nonneg x r)

/-- Every actual global mixture lies below the literal raw concave envelope. -/
theorem sourceTestCurveJoinMixture_le_raw (Γ Δ : SourceTestCurvePredata θ)
    (τ : ℝ) (j : SourceTestCurveJoinMixtureIndex Γ Δ τ) :
    sourceTestCurveJoinMixture Γ Δ τ j ≤ sourceTestCurveRawConcaveMaximum Γ Δ τ := by
  have hG (a : Iio Γ.max) (x : M) : Γ.potential a x ≤ sourceTestCurveRawConcaveMaximum Γ Δ a.1 x := by
    have h := (le_max_left (sourceTestCurveAt Γ a.1 x) (sourceTestCurveAt Δ a.1 x)).trans
      (sourceTestCurveRawConcaveMaximum_ge Γ Δ a.1 x)
    simpa only [sourceTestCurveAt_of_lt Γ a.2] using h
  have hD (b : Iio Δ.max) (x : M) : Δ.potential b x ≤ sourceTestCurveRawConcaveMaximum Γ Δ b.1 x := by
    have h := (le_max_right (sourceTestCurveAt Γ b.1 x) (sourceTestCurveAt Δ b.1 x)).trans
      (sourceTestCurveRawConcaveMaximum_ge Γ Δ b.1 x)
    simpa only [sourceTestCurveAt_of_lt Δ b.2] using h
  unfold sourceTestCurveJoinMixture
  split_ifs with hw0 hw1
  · have he : j.right.1 = τ := by
      have h := j.barycenter
      simpa only [hw0,zero_mul,sub_zero,one_mul,zero_add] using h
    intro x
    simpa only [he] using hD j.right x
  · have he : j.left.1 = τ := by
      have h := j.barycenter
      simpa only [hw1,one_mul,sub_self,zero_mul,add_zero] using h
    intro x
    simpa only [he] using hG j.left x
  · intro x
    have hwpos : 0 < j.weight.1 := lt_of_le_of_ne j.weight.2.1 (Ne.symm hw0)
    have hwlt : j.weight.1 < 1 := lt_of_le_of_ne j.weight.2.2 hw1
    have hc := sourceTestCurveRawConcaveMaximum_convexComb_le Γ Δ
      j.left.1 j.right.1 hwpos hwlt x
    rw [j.barycenter] at hc
    apply le_trans ?_ hc
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hG j.left x) (EReal.coe_nonneg.mpr j.weight.2.1))
      (mul_le_mul_of_nonneg_left (hD j.right x)
        (EReal.coe_nonneg.mpr (sub_nonneg.mpr j.weight.2.2)))

/-- Actual proper weighted rooftop tuples give the reverse bound at finite
cutoff points. The defining global mixture index NEVER depends on finiteness. -/
theorem sourceTestCurveRaw_le_mixtureUSC_of_cutoff_finite
    (Γ Δ : SourceTestCurvePredata θ) (x : M) {τ : ℝ} (hτ : τ < max Γ.max Δ.max)
    (hΓ : sourceTestCurveCutoff Γ x ≠ ⊥) (hΔ : sourceTestCurveCutoff Δ x ≠ ⊥) :
    sourceTestCurveRawConcaveMaximum Γ Δ τ x ≤ sourceTestCurveJoinMixtureUSC Γ Δ τ x := by
  classical
  let F : Bool → ℝ → EReal := fun b => if b then
    sourceTestCurveNegativeTrace Γ.max Γ.potential x else
    sourceTestCurveNegativeTrace Δ.max Δ.potential x
  have hf (b : Bool) : SGPT.Convex.IsProper (F b) := by
    cases b
    · exact Δ.openNegativeTrace_isProper_of_cutoff_ne_bot x hΔ
    · exact Γ.openNegativeTrace_isProper_of_cutoff_ne_bot x hΓ
  have hK : sourceTestCurveOpenConvexEnvelope Γ Δ x = SGPT.Convex.convexInf F := by
    unfold sourceTestCurveOpenConvexEnvelope SGPT.Convex.convexInf
    congr 1
    funext r
    simp [F,iInf_bool_eq]
  have habove : sourceTestCurveAt Γ (max Γ.max Δ.max) x ≠ ⊥ ∨
      sourceTestCurveAt Δ (max Γ.max Δ.max) x ≠ ⊥ := by
    rcases le_total Γ.max Δ.max with hm | hm
    · right
      simpa only [max_eq_right hm,sourceTestCurveAt_eq_max] using hΔ
    · left
      simpa only [max_eq_left hm,sourceTestCurveAt_eq_max] using hΓ
  have hOpen := sourceTestCurveOpenConvexEnvelope_eq_whole_of_finite_above Γ Δ x hτ habove
  have hJ : sourceTestCurveRawConcaveMaximum Γ Δ τ x = -SGPT.Convex.weightedRooftop F τ := by
    change -sourceTestCurveJoinConvexEnvelope Γ Δ x τ = _
    rw [← hOpen,hK,SGPT.Convex.convexInf_eq_weightedRooftop hf]
  rw [hJ]
  have hlow : -sourceTestCurveJoinMixtureUSC Γ Δ τ x ≤ SGPT.Convex.weightedRooftop F τ := by
    apply le_iInf
    intro d
    apply le_iInf
    intro hd
    have hoG : d.point true < Γ.max := by
      by_contra hn
      have h := d.point_mem_domain true
      change sourceTestCurveNegativeTrace Γ.max Γ.potential x (d.point true) < ⊤ at h
      rw [sourceTestCurveNegativeTrace,dif_neg hn] at h
      exact lt_irrefl _ h
    have hoD : d.point false < Δ.max := by
      by_contra hn
      have h := d.point_mem_domain false
      change sourceTestCurveNegativeTrace Δ.max Δ.potential x (d.point false) < ⊤ at h
      rw [sourceTestCurveNegativeTrace,dif_neg hn] at h
      exact lt_irrefl _ h
    have hwSum : d.weight false+d.weight true=1 := by
      simpa only [Fintype.sum_bool,add_comm] using d.weight_sum
    have hwFalse : d.weight false=1-d.weight true := by linarith
    let j : SourceTestCurveJoinMixtureIndex Γ Δ τ :=
      ⟨⟨d.point true,hoG⟩,⟨d.point false,hoD⟩,
        ⟨d.weight true,d.weight_nonneg true,d.weight_le_one true⟩,by
          have h := hd
          change (∑ b : Bool,d.weight b • d.point b)=τ at h
          simp only [Fintype.sum_bool,smul_eq_mul] at h
          rw [hwFalse] at h
          nlinarith [h]⟩
    have hGa : Γ.potential j.left x ≠ ⊥ :=
      ne_bot_of_le_ne_bot hΓ (iInf_le (fun r : Iio Γ.max => Γ.potential r x) j.left)
    have hDa : Δ.potential j.right x ≠ ⊥ :=
      ne_bot_of_le_ne_bot hΔ (iInf_le (fun r : Iio Δ.max => Δ.potential r x) j.right)
    let A := (Γ.potential j.left x).toReal
    let B := (Δ.potential j.right x).toReal
    have hA : Γ.potential j.left x=(A : EReal) :=
      (EReal.coe_toReal (ne_of_lt ((Γ.le_zero j.left x).trans_lt (by simp))) hGa).symm
    have hB : Δ.potential j.right x=(B : EReal) :=
      (EReal.coe_toReal (ne_of_lt ((Δ.le_zero j.right x).trans_lt (by simp))) hDa).symm
    have hFG : F true (d.point true) = -(A : EReal) := by
      change sourceTestCurveNegativeTrace Γ.max Γ.potential x (d.point true) = _
      rw [sourceTestCurveNegativeTrace,dif_pos hoG]
      change -Γ.potential j.left x = _
      rw [hA]
    have hFD : F false (d.point false) = -(B : EReal) := by
      change sourceTestCurveNegativeTrace Δ.max Δ.potential x (d.point false) = _
      rw [sourceTestCurveNegativeTrace,dif_pos hoD]
      change -Δ.potential j.right x = _
      rw [hB]
    have hCost : d.cost = -(d.weight true*A+d.weight false*B) := by
      simp only [SGPT.Convex.RooftopData.cost,Fintype.sum_bool]
      rw [hFG,hFD]
      simp only [EReal.toReal_neg_eq,EReal.toReal_coe]
      ring
    have hMix : sourceTestCurveJoinMixture Γ Δ τ j x =
        ((d.weight true*A+d.weight false*B : ℝ) : EReal) := by
      unfold sourceTestCurveJoinMixture
      split_ifs with hw0 hw1
      · have hw : d.weight true=0 := hw0
        have hf0 : d.weight false=1 := by linarith
        rw [hB]
        simp only [hw,hf0,zero_mul,one_mul,zero_add]
      · have hw : d.weight true=1 := hw1
        have hf0 : d.weight false=0 := by linarith
        rw [hA]
        simp only [hw,hf0,one_mul,zero_mul,add_zero]
      · change (j.weight.1 : EReal)*Γ.potential j.left x+
          ((1-j.weight.1 : ℝ) : EReal)*Δ.potential j.right x = _
        rw [hA,hB,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add]
        congr 1
        change d.weight true*A+(1-d.weight true)*B = d.weight true*A+d.weight false*B
        rw [hwFalse]
    have hCostEq : (d.cost : EReal) = -sourceTestCurveJoinMixture Γ Δ τ j x := by
      rw [hCost,hMix,EReal.coe_neg]
    have hterm : sourceTestCurveJoinMixture Γ Δ τ j x ≤ sourceTestCurveJoinMixtureUSC Γ Δ τ x := by
      have hSup : (⨆ k : SourceTestCurveJoinMixtureIndex Γ Δ τ,
          sourceTestCurveJoinMixture Γ Δ τ k) =
          fun y => ⨆ k : SourceTestCurveJoinMixtureIndex Γ Δ τ,
            sourceTestCurveJoinMixture Γ Δ τ k y := by
        funext y
        exact iSup_apply
      rw [sourceTestCurveJoinMixtureUSC,hSup]
      exact (le_iSup (fun k : SourceTestCurveJoinMixtureIndex Γ Δ τ =>
        sourceTestCurveJoinMixture Γ Δ τ k x) j).trans
          (le_uscRegularization (fun y => ⨆ k : SourceTestCurveJoinMixtureIndex Γ Δ τ,
            sourceTestCurveJoinMixture Γ Δ τ k y) x)
    rw [hCostEq]
    exact EReal.neg_le_neg_iff.mpr hterm
  simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hlow

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Each actual mixture is I-good using only EXISTING intrinsic closure mothers. -/
theorem sourceTestCurveJoinMixture_iGood (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ)
    (τ : ℝ) (j : SourceTestCurveJoinMixtureIndex Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) :
    sourceIGood (n := n)
      (sourceTestCurveJoinMixture Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ j) := by
  have hG := Γ.iModel_openSlice_good omega hΓ j.left
  have hD := Δ.iModel_openSlice_good omega hΔ j.right
  unfold sourceTestCurveJoinMixture
  split_ifs with hw0 hw1
  · exact hD
  · exact hG
  · exact sourceIGood_add omega
      (sourceIGood_pos_mul hG (lt_of_le_of_ne j.weight.2.1 (Ne.symm hw0)))
      (sourceIGood_pos_mul hD (sub_pos.mpr (lt_of_le_of_ne j.weight.2.2 hw1)))

/-- Actual USC closure proves goodness of the constructed global mixture supremum. -/
theorem sourceTestCurveJoinMixtureUSC_iGood (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ)
    {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    sourceIGood (n := n)
      (sourceTestCurveJoinMixtureUSC Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) := by
  let J := SourceTestCurveJoinMixtureIndex Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ
  let : Nonempty J := sourceTestCurveJoinMixtureIndex_nonempty
    Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ
  let u : J → M → EReal := fun j =>
    sourceTestCurveJoinMixture Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ j
  have hb : FirstPass.LocallyUniformlyBoundedAbove (range u) univ := by
    intro x hx
    refine ⟨univ,Filter.univ_mem,0,?_⟩
    rintro f ⟨j,rfl⟩ y hy
    exact sourceTestCurveJoinMixture_le_zero Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ j y
  exact sourceIGood_uscSup omega u
    (fun j => sourceTestCurveJoinMixture_thetaPSH Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ j)
    (fun j => sourceTestCurveJoinMixture_iGood omega Γ Δ hΓ hΔ τ j) hb

/-- Genuine PSH of the raw envelope lets its global mixture bound survive USC. -/
theorem sourceTestCurveJoinMixtureUSC_le_raw (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    sourceTestCurveJoinMixtureUSC Γ Δ τ ≤ sourceTestCurveRawConcaveMaximum Γ Δ τ := by
  apply uscRegularization_le
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ Δ hτ.le)).1.quasiPlurisubharmonic.upperSemicontinuous
  exact iSup_le fun j => sourceTestCurveJoinMixture_le_raw Γ Δ τ j

/-- The actual global-mixture USC supremum equals the LITERAL raw envelope.
Only TWO genuine cutoff pole sets are excluded before actual PSH comparison. -/
theorem sourceTestCurveRawConcaveMaximum_eq_mixtureUSC (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurvePredata θ) {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    sourceTestCurveRawConcaveMaximum Γ Δ τ = sourceTestCurveJoinMixtureUSC Γ Δ τ := by
  apply le_antisymm
  · apply (sourceQuasiEverywhere_le_iff
      (sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ Δ hτ.le)
      (sourceTestCurveJoinMixtureUSC_thetaPSH Γ Δ hτ)).mp
    apply (sourceQuasiEverywhere_iff_native _).mpr
    have hGqe := quasiPsh_finite_quasiEverywhere
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.cutoff_thetaPSH).quasiPshPotential
    have hDqe := quasiPsh_finite_quasiEverywhere
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp Δ.cutoff_thetaPSH).quasiPshPotential
    apply (quasiEverywhere_and hGqe hDqe).mono
    intro x hx
    exact sourceTestCurveRaw_le_mixtureUSC_of_cutoff_finite Γ Δ x hτ hx.1.1 hx.2.1
  · exact sourceTestCurveJoinMixtureUSC_le_raw omega Γ Δ hτ

/-- Genuine raw I-goodness, using a PROVED global function identity. -/
theorem sourceTestCurveRawConcaveMaximum_iGood (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ)
    {τ : ℝ} (hτ : τ < max Γ.max Δ.max) :
    sourceIGood (n := n)
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) := by
  rw [sourceTestCurveRawConcaveMaximum_eq_mixtureUSC omega Γ.toSourceTestCurvePredata
    Δ.toSourceTestCurvePredata hτ]
  exact sourceTestCurveJoinMixtureUSC_iGood omega Γ Δ hΓ hΔ hτ

/-- Actual raw goodness plus positive SAME-background mass makes every
ordinary join slice an actual I-model; no output I-model certificate. -/
theorem SourceTestCurve.join_isIModel (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ) :
    SourceTestCurveIsIModel (SourceTestCurve.join omega Γ Δ) := by
  intro r
  have hτ : r.1 < max Γ.max Δ.max := r.2
  have hP := sourceTestCurveRawConcaveMaximum_thetaPSH omega
    Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata hτ.le
  have hpos := sourceTestCurveRawConcaveMaximum_mass_positive omega Γ Δ hτ
  have hgood := sourceTestCurveRawConcaveMaximum_iGood omega Γ Δ hΓ hΔ hτ
  have hPI := (sourceIGood_iff_PI_eq omega hP hpos).mp hgood
  have hout : sourceIModel θ ((SourceTestCurve.join omega Γ Δ).potential r) := by
    rw [SourceTestCurve.join_potential,hPI]
    exact sourceIEnvelope_isIModel hP
  exact (sourceIModel_iff_native θ _).mp hout

/-- The ENTIRE original positive I-model union is retained, with produced base. -/
theorem SourceTestCurve.join_mem_iModelPositive (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (hΓ : Γ ∈ SourceIModelTestCurvesPositive θ)
    (hΔ : Δ ∈ SourceIModelTestCurvesPositive θ) :
    SourceTestCurve.join omega Γ Δ ∈ SourceIModelTestCurvesPositive θ := by
  apply (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
  exact SourceTestCurve.join_isIModel omega Γ Δ
    ((sourceIModelTestCurvesPositive_iff_slices omega Γ).mp hΓ)
    ((sourceIModelTestCurvesPositive_iff_slices omega Δ).mp hΔ)

/-- WHOLE original lma:testcurlor: genuine raw PSH, positive original join,
and raw I-goodness for the original positive I-model input unions. -/
theorem source_test_curve_join_whole (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    (∀ τ : ℝ, τ < max Γ.max Δ.max → (ofFixedModel n M).IsThetaPSH θ
      (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) ∧
    SourceTestCurve.join omega Γ Δ ∈ SourceTestCurvesPositive θ ∧
    (Γ ∈ SourceIModelTestCurvesPositive θ → Δ ∈ SourceIModelTestCurvesPositive θ →
      (∀ τ : ℝ, τ < max Γ.max Δ.max → sourceIGood (n := n)
        (sourceTestCurveRawConcaveMaximum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) ∧
      SourceTestCurve.join omega Γ Δ ∈ SourceIModelTestCurvesPositive θ) := by
  refine ⟨?_,SourceTestCurve.join_mem_positive omega Γ Δ,?_⟩
  · intro τ hτ
    exact sourceTestCurveRawConcaveMaximum_thetaPSH omega Γ.toSourceTestCurvePredata
      Δ.toSourceTestCurvePredata hτ.le
  · intro hΓ hΔ
    refine ⟨?_,SourceTestCurve.join_mem_iModelPositive omega Γ Δ hΓ hΔ⟩
    intro τ hτ
    exact sourceTestCurveRawConcaveMaximum_iGood omega Γ Δ
      ((sourceIModelTestCurvesPositive_iff_slices omega Γ).mp hΓ)
      ((sourceIModelTestCurvesPositive_iff_slices omega Δ).mp hΔ) hτ

end SGPT.PSH.VariableComplexAtlas
