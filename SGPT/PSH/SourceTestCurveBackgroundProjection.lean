import SGPT.PSH.SourceTestCurveIntrinsicOrder
import SGPT.PSH.SourceIGoodBackground
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
/-- Strict chords imply the WHOLE original negative-trace epigraph condition. -/
theorem sourceTestCurveNegativeTrace_convex_of_chords {X : Type*} {m : ℝ}
    (u : Iio m → X → EReal)
    (hchord : ∀ (p q : Iio m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1),
      convexComb t (u p) (u q) ≤ u ⟨t * p.1 + (1-t) * q.1, by
        change t*p.1+(1-t)*q.1 < m
        nlinarith [mul_pos ht0 (sub_pos.mpr p.2),
          mul_pos (sub_pos.mpr ht1) (sub_pos.mpr q.2)]⟩)
    (x : X) : SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace m u x) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa only [hb0, ha1, zero_smul, one_smul, add_zero] using hp
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hpopen : p.1 < m := by
    by_contra hn
    change sourceTestCurveNegativeTrace m u x p.1 ≤ (p.2 : EReal) at hp
    rw [sourceTestCurveNegativeTrace, dif_neg hn] at hp
    exact not_le_of_gt (EReal.coe_lt_top p.2) hp
  have hqopen : q.1 < m := by
    by_contra hn
    change sourceTestCurveNegativeTrace m u x q.1 ≤ (q.2 : EReal) at hq
    rw [sourceTestCurveNegativeTrace, dif_neg hn] at hq
    exact not_le_of_gt (EReal.coe_lt_top q.2) hq
  change sourceTestCurveNegativeTrace m u x p.1 ≤ (p.2 : EReal) at hp
  change sourceTestCurveNegativeTrace m u x q.1 ≤ (q.2 : EReal) at hq
  rw [sourceTestCurveNegativeTrace, dif_pos hpopen] at hp
  rw [sourceTestCurveNegativeTrace, dif_pos hqopen] at hq
  have hplow : ((-p.2 : ℝ) : EReal) ≤ u ⟨p.1,hpopen⟩ x := by
    simpa only [neg_neg, ← EReal.coe_neg] using EReal.neg_le_neg_iff.mpr hp
  have hqlow : ((-q.2 : ℝ) : EReal) ≤ u ⟨q.1,hqopen⟩ x := by
    simpa only [neg_neg, ← EReal.coe_neg] using EReal.neg_le_neg_iff.mpr hq
  have hbEq : b = 1-a := by linarith
  have ha1 : a < 1 := by linarith
  have hh := hchord ⟨p.1,hpopen⟩ ⟨q.1,hqopen⟩ haPos ha1 x
  change (a : EReal) * u ⟨p.1,hpopen⟩ x +
    ((1-a : ℝ) : EReal) * u ⟨q.1,hqopen⟩ x ≤ _ at hh
  simp only [← hbEq] at hh
  have hlo := add_le_add
    (mul_le_mul_of_nonneg_left hplow (EReal.coe_nonneg.mpr ha))
    (mul_le_mul_of_nonneg_left hqlow (EReal.coe_nonneg.mpr hb))
  have hfull := hlo.trans hh
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hfull
  have heq : a*(-p.2)+b*(-q.2) = -(a*p.2+b*q.2) := by ring
  rw [heq, EReal.coe_neg] at hfull
  have hcopen : a*p.1+b*q.1 < m := by
    calc
      a*p.1+b*q.1 < a*m+b*m := add_lt_add
        (mul_lt_mul_of_pos_left hpopen haPos) (mul_lt_mul_of_pos_left hqopen hbPos)
      _ = (a+b)*m := by ring
      _ = m := by rw [hab, one_mul]
  change sourceTestCurveNegativeTrace m u x (a*p.1+b*q.1) ≤
    ((a*p.2+b*q.2 : ℝ) : EReal)
  rw [sourceTestCurveNegativeTrace, dif_pos hcopen]
  exact EReal.neg_le_neg_iff.mp (by simpa only [neg_neg] using hfull)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual atlas addition with precisely the original enlarged native form. -/
def sourceTestCurveEnlargedBackground (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    AtlasClosedRealOneOneForm (ofFixedModel n M) := θ.add (nativeClosedFormToAtlas omega.form)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Exact form dictionary, retaining the whole original closed forms. -/
theorem sourceTestCurveEnlargedBackground_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    atlasClosedFormToNative (sourceTestCurveEnlargedBackground omega θ) =
      atlasClosedFormToNative θ + omega.form := by
  simp only [sourceTestCurveEnlargedBackground, sourceNativeClosedForm_add,
    sourceNativeAtlasForm_roundTrip]

/-- Actual enlarged input PSH and mass internally produce each genuine model. -/
theorem SourceTestCurve.backgroundProjectionInput_model (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    SourceModelPotential (sourceTestCurveEnlargedBackground omega θ)
      (sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r)) :=
  sourceOrdinaryEnvelope_model omega (sourceThetaPSH_add_kahler omega (Γ.thetaPSH r))
    (sourcePositiveMass_add_kahler omega (Γ.thetaPSH r))

omit [BorelSpace M] in
/-- Genuine ordinary-envelope concavity, on all original open parameters. -/
private theorem backgroundProjection_concave (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace Γ.max
      (fun r => sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ)
        (Γ.potential r)) x) := by
  apply sourceTestCurveNegativeTrace_convex_of_chords
  intro p q t ht0 ht1 y
  have hP := sourceOrdinaryEnvelope_convexComb_le
    (sourceThetaPSH_add_kahler omega (Γ.thetaPSH p))
    (sourceThetaPSH_add_kahler omega (Γ.thetaPSH q)) ht0 ht1
  have hmono := sourceOrdinaryEnvelope_mono
    (θ := sourceTestCurveEnlargedBackground omega θ)
    (MoreSingularOn.of_le fun z _ => Γ.toSourceTestCurvePredata.convexComb_le p q ht0 ht1 z)
  exact (hP y).trans (hmono y)

/-- All actual original preliminary fields of the projected curve. -/
def SourceTestCurve.backgroundProjectionPredata (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : SourceTestCurvePredata (sourceTestCurveEnlargedBackground omega θ) where
  max := Γ.max
  potential r := sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r)
  thetaPSH r := (Γ.backgroundProjectionInput_model omega r).thetaPSH
  antitone x _p _q hpq := sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun y _ => Γ.antitone y hpq) x
  concave x := backgroundProjection_concave omega Γ x
  fixedPoint r := (Γ.backgroundProjectionInput_model omega r).choose_spec.1.symm

/-- Genuine positive USC limit mass completes the ACTUAL original projected curve. -/
def SourceTestCurve.backgroundProjection (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : SourceTestCurve (sourceTestCurveEnlargedBackground omega θ) where
  toSourceTestCurvePredata := Γ.backgroundProjectionPredata omega
  positiveLimitMass := by
    have : Nonempty (Iio Γ.max) := ⟨⟨Γ.max-1, by change Γ.max-1 < Γ.max; linarith⟩⟩
    have hp := sourceIncreasingOrdinary_sup_positive omega
      (fun r : Iio Γ.max => (Γ.backgroundProjectionInput_model omega r).thetaPSH)
      (fun r => (Γ.backgroundProjectionInput_model omega r).choose_spec.2)
      (C := 0) (fun r x => by
        simpa only [EReal.coe_zero, Pi.zero_apply] using
          sourceSingularityEnvelope_le_zero (sourceTestCurveEnlargedBackground omega θ)
            (Γ.potential r) x)
    have hU : (⨆ r : Iio Γ.max,
        sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r)) =
        fun x => ⨆ r : Iio Γ.max,
          sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r) x := by
      funext x
      exact iSup_apply
    simp only [hU] at hp
    exact hp

/-- Literal original projected cutoff. -/
theorem SourceTestCurve.backgroundProjection_max (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) : (Γ.backgroundProjection omega).max = Γ.max := rfl

/-- Literal original projected potential, at EVERY original open parameter. -/
theorem SourceTestCurve.backgroundProjection_potential (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.backgroundProjection omega).potential r =
      sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r) := rfl

/-- The ENTIRE original enlarged-background spatial USC limit identity. -/
theorem SourceTestCurve.backgroundProjection_limit (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.backgroundProjection omega).toSourceTestCurvePredata =
      sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ)
        (sourceTestCurveLimit Γ.toSourceTestCurvePredata) := by
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max-1, by change Γ.max-1 < Γ.max; linarith⟩⟩
  have hm : Monotone (fun r : OrderDual (Iio Γ.max) => Γ.potential r) := by
    intro r s hrs x
    exact Γ.antitone x hrs
  have hid := sourceOrdinaryEnvelope_increasing_directed_eq omega
    (fun r : OrderDual (Iio Γ.max) => sourceThetaPSH_add_kahler omega (Γ.thetaPSH r))
    (fun r => sourcePositiveMass_add_kahler omega (Γ.thetaPSH r)) hm
    (C := 0) (fun r x => by simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero r x)
  change uscRegularization (fun x => ⨆ r : Iio Γ.max,
    sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r) x) =
    sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ)
      (uscRegularization (fun x => ⨆ r : Iio Γ.max, Γ.potential r x))
  have hraw : (⨆ r : OrderDual (Iio Γ.max), Γ.potential r) =
      fun x => ⨆ r : Iio Γ.max, Γ.potential r x := by
    funext x
    exact iSup_apply
  have hP : (⨆ r : OrderDual (Iio Γ.max),
      sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r)) =
      fun x => ⨆ r : Iio Γ.max,
        sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential r) x := by
    funext x
    exact iSup_apply
  simp only [sourceTestCurveEnlargedBackground] at hP
  simpa only [sourceTestCurveEnlargedBackground, hraw, hP] using hid

/-- Actual global P comparison is literal order of the two projected slices. -/
private theorem backgroundProjection_slice_iff (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) (r : ℝ) (hr : r < Γ.max) (hs : r < Δ.max) :
    SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
      (Γ.potential ⟨r,hr⟩) (Δ.potential ⟨r,hs⟩) ↔
      (Γ.backgroundProjection omega).potential ⟨r,hr⟩ ≤
        (Δ.backgroundProjection omega).potential ⟨r,hs⟩ := by
  have hu := sourceThetaPSH_add_kahler omega (Γ.thetaPSH ⟨r,hr⟩)
  have hv := sourceThetaPSH_add_kahler omega (Δ.thetaPSH ⟨r,hs⟩)
  have hup := sourcePositiveMass_add_kahler omega (Γ.thetaPSH ⟨r,hr⟩)
  have hvp := sourcePositiveMass_add_kahler omega (Δ.thetaPSH ⟨r,hs⟩)
  have hp := SGPT.PSH.GlobalPComparison.sourcePOrder_iff_positive_background omega
    (atlasClosedFormToNative (sourceTestCurveEnlargedBackground omega θ))
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hv) hup hvp
  change SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
    (Γ.potential ⟨r,hr⟩) (Δ.potential ⟨r,hs⟩) ↔
    sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Γ.potential ⟨r,hr⟩) ≤
      sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ) (Δ.potential ⟨r,hs⟩)
  simpa only [FirstPass.POrder.POrderWith, ← sourceSingularityEnvelope_eq_native] using hp

/-- WHOLE original projection/order lemma on ACTUAL projected curves. -/
theorem source_test_curve_background_projection_order_iff (omega : KahlerBackground n M)
    (Γ Δ : SourceTestCurve θ) :
    SourceTestCurvePOrder Γ Δ ↔
      SourceTestCurvePOrder (Γ.backgroundProjection omega) (Δ.backgroundProjection omega) := by
  constructor
  · intro h
    apply (sourceTestCurvePOrder_iff omega _ _).mpr
    exact ⟨h.cutoff_le, fun r hr =>
      (backgroundProjection_slice_iff omega Γ Δ r hr _).mp (h.slice_le r hr)⟩
  · intro h
    obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega _ _).mp h
    exact ⟨hc, fun r hr => (backgroundProjection_slice_iff omega Γ Δ r hr _).mpr (hs r hr)⟩

end SGPT.PSH.VariableComplexAtlas
