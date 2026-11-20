import SGPT.PSH.SourceTestCurveIEnvelope
import SGPT.PSH.SourceTestCurveIncreasingSup
import SGPT.PSH.SourceTestCurveScalingProjection

/-! # Ordinary test-curve projection after arbitrary semipositive addition

The book's positive forms need not be strictly positive. The added form
below is therefore an arbitrary semipositive atlas closed form, independent
of the ambient Kähler metric, and may be zero.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [ConnectedSpace M] in
/-- Original positive slice mass survives every semipositive addition. -/
theorem SourceTestCurve.semipositiveProjectionInput_positive (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    0 < sourcePotentialNonPluripolarMeasure (θ.add η) (Γ.potential r)
      (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r)) univ :=
  (Γ.mass_positive omega r).trans_le
    (sourcePotentialMass_le_add_semipositive η hη (Γ.thetaPSH r))

/-- Each actual original envelope slice is produced as a positive model. -/
theorem SourceTestCurve.semipositiveProjectionInput_model (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    SourceModelPotential (θ.add η) (sourceSingularityEnvelope (θ.add η) (Γ.potential r)) :=
  sourceOrdinaryEnvelope_model omega (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))
    (Γ.semipositiveProjectionInput_positive omega η hη r)

omit [BorelSpace M] in
private theorem semipositiveProjection_concave (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace Γ.max
      (fun r ↦ sourceSingularityEnvelope (θ.add η) (Γ.potential r)) x) := by
  apply sourceTestCurveNegativeTrace_convex_of_chords
  intro p q t ht0 ht1 y
  have hP := sourceOrdinaryEnvelope_convexComb_le
    (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH p))
    (sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH q)) ht0 ht1
  have hmono := sourceOrdinaryEnvelope_mono (θ := θ.add η)
    (MoreSingularOn.of_le fun z _ ↦ Γ.toSourceTestCurvePredata.convexComb_le p q ht0 ht1 z)
  exact (hP y).trans (hmono y)

/-- The exact ordinary projected preliminary family in any added positive form. -/
def SourceTestCurve.semipositiveProjectionPredata (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) : SourceTestCurvePredata (θ.add η) where
  max := Γ.max
  potential r := sourceSingularityEnvelope (θ.add η) (Γ.potential r)
  thetaPSH r := (Γ.semipositiveProjectionInput_model omega η hη r).thetaPSH
  antitone x _p _q hpq := sourceOrdinaryEnvelope_mono
    (MoreSingularOn.of_le fun y _ ↦ Γ.antitone y hpq) x
  concave x := semipositiveProjection_concave η hη Γ x
  fixedPoint r := (Γ.semipositiveProjectionInput_model omega η hη r).choose_spec.1.symm

/-- Whole original def:Ptestcurve for every semipositive added form. -/
def SourceTestCurve.semipositiveProjection (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) : SourceTestCurve (θ.add η) where
  toSourceTestCurvePredata := Γ.semipositiveProjectionPredata omega η hη
  positiveLimitMass := by
    have : Nonempty (Iio Γ.max) :=
      ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
    have hp := sourceIncreasingOrdinary_sup_positive omega
      (fun r : Iio Γ.max ↦ (Γ.semipositiveProjectionInput_model omega η hη r).thetaPSH)
      (fun r ↦ (Γ.semipositiveProjectionInput_model omega η hη r).choose_spec.2)
      (C := 0) (fun r x ↦ by
        simpa only [EReal.coe_zero, Pi.zero_apply] using
          sourceSingularityEnvelope_le_zero (θ.add η) (Γ.potential r) x)
    have hU : (⨆ r : Iio Γ.max, sourceSingularityEnvelope (θ.add η) (Γ.potential r)) =
        fun x ↦ ⨆ r : Iio Γ.max, sourceSingularityEnvelope (θ.add η) (Γ.potential r) x := by
      funext x
      exact iSup_apply
    simp only [hU] at hp
    exact hp

theorem SourceTestCurve.semipositiveProjection_max (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) : (Γ.semipositiveProjection omega η hη).max = Γ.max := rfl

theorem SourceTestCurve.semipositiveProjection_potential (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) (r : Iio Γ.max) :
    (Γ.semipositiveProjection omega η hη).potential r =
      sourceSingularityEnvelope (θ.add η) (Γ.potential r) := rfl

/-- Whole original prop:PpreGammainf with weak positivity exactly as in the book. -/
theorem SourceTestCurve.semipositiveProjection_limit (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : SourceTestCurve θ) :
    sourceTestCurveLimit (Γ.semipositiveProjection omega η hη).toSourceTestCurvePredata =
      sourceSingularityEnvelope (θ.add η) (sourceTestCurveLimit Γ.toSourceTestCurvePredata) := by
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hm : Monotone (fun r : OrderDual (Iio Γ.max) ↦ Γ.potential r) := by
    intro r s hrs x
    exact Γ.antitone x hrs
  have hid := sourceOrdinaryEnvelope_increasing_directed_eq omega
    (fun r : OrderDual (Iio Γ.max) ↦ sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH r))
    (fun r ↦ Γ.semipositiveProjectionInput_positive omega η hη r) hm
    (C := 0) (fun r x ↦ by simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero r x)
  change uscRegularization (fun x ↦ ⨆ r : Iio Γ.max,
    sourceSingularityEnvelope (θ.add η) (Γ.potential r) x) =
      sourceSingularityEnvelope (θ.add η)
        (uscRegularization (fun x ↦ ⨆ r : Iio Γ.max, Γ.potential r x))
  have hraw : (⨆ r : OrderDual (Iio Γ.max), Γ.potential r) =
      fun x ↦ ⨆ r : Iio Γ.max, Γ.potential r x := by
    funext x
    exact iSup_apply
  have hP : (⨆ r : OrderDual (Iio Γ.max),
      sourceSingularityEnvelope (θ.add η) (Γ.potential r)) =
      fun x ↦ ⨆ r : Iio Γ.max, sourceSingularityEnvelope (θ.add η) (Γ.potential r) x := by
    funext x
    exact iSup_apply
  simpa only [hraw, hP] using hid

private theorem semipositiveProjection_slice_iff (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ Δ : SourceTestCurve θ) (r : ℝ) (hr : r < Γ.max) (hs : r < Δ.max) :
    SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
      (Γ.potential ⟨r, hr⟩) (Δ.potential ⟨r, hs⟩) ↔
      (Γ.semipositiveProjection omega η hη).potential ⟨r, hr⟩ ≤
        (Δ.semipositiveProjection omega η hη).potential ⟨r, hs⟩ := by
  have hu := sourceThetaPSH_add_semipositive η hη (Γ.thetaPSH ⟨r, hr⟩)
  have hv := sourceThetaPSH_add_semipositive η hη (Δ.thetaPSH ⟨r, hs⟩)
  have hp := SGPT.PSH.GlobalPComparison.sourcePOrder_iff_positive_background omega
    (atlasClosedFormToNative (θ.add η))
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp hv)
    (Γ.semipositiveProjectionInput_positive omega η hη ⟨r, hr⟩)
    (Δ.semipositiveProjectionInput_positive omega η hη ⟨r, hs⟩)
  change SGPT.PSH.GlobalPComparison.sourcePOrder (n := n)
    (Γ.potential ⟨r, hr⟩) (Δ.potential ⟨r, hs⟩) ↔
      sourceSingularityEnvelope (θ.add η) (Γ.potential ⟨r, hr⟩) ≤
        sourceSingularityEnvelope (θ.add η) (Δ.potential ⟨r, hs⟩)
  simpa only [FirstPass.POrder.POrderWith, ← sourceSingularityEnvelope_eq_native] using hp

/-- Whole original lma:testcurord1, retaining every semipositive added form. -/
theorem source_test_curve_semipositive_projection_order_iff (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ Δ : SourceTestCurve θ) :
    SourceTestCurvePOrder Γ Δ ↔
      SourceTestCurvePOrder (Γ.semipositiveProjection omega η hη)
        (Δ.semipositiveProjection omega η hη) := by
  constructor
  · intro h
    apply (sourceTestCurvePOrder_iff omega _ _).mpr
    exact ⟨h.cutoff_le, fun r hr ↦
      (semipositiveProjection_slice_iff omega η hη Γ Δ r hr _).mp (h.slice_le r hr)⟩
  · intro h
    obtain ⟨hc, hs⟩ := (sourceTestCurvePOrder_iff omega _ _).mp h
    exact ⟨hc, fun r hr ↦ (semipositiveProjection_slice_iff omega η hη Γ Δ r hr _).mpr (hs r hr)⟩

theorem sourceTestCurveSemipositiveProjectedFamily_monotone {I : Type*} [Preorder I]
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j)) :
    ∀ i j, i ≤ j → SourceTestCurvePOrder
      ((Γ i).semipositiveProjection omega η hη) ((Γ j).semipositiveProjection omega η hη) :=
  fun i j hij ↦ (source_test_curve_semipositive_projection_order_iff omega η hη (Γ i) (Γ j)).mp
    (hm i j hij)

theorem sourceTestCurveSemipositiveProjectedFamily_bddAbove {I : Type*}
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : I → SourceTestCurve θ)
    (hbound : BddAbove (range fun i ↦ (Γ i).max)) :
    BddAbove (range fun i ↦ ((Γ i).semipositiveProjection omega η hη).max) := hbound

/-- Genuine whole directed ordinary-envelope continuity on original tail slices. -/
theorem sourceTestCurveSupPotential_semipositiveProjection {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    {r : ℝ} (hr : r < sourceTestCurveSupCutoff Γ) :
    sourceSingularityEnvelope (θ.add η) (sourceTestCurveSupPotential Γ r) =
      sourceTestCurveSupPotential (fun i ↦ (Γ i).semipositiveProjection omega η hη) r := by
  obtain ⟨i₀, hr₀⟩ := sourceTestCurveSupCutoff_exists Γ hr
  let J := {i : I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirectedOrder J := ⟨by
    intro i j
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  have ho (i : J) : r < (Γ i.val).max := hr₀.trans_le (hm i₀ i.val i.property).cutoff_le
  let u : J → M → EReal := fun i ↦ (Γ i.val).potential ⟨r, ho i⟩
  have hmono : Monotone u := by
    intro i j hij
    have h := sourceTestCurveSup_extension_monotone omega Γ hm r hij
    simpa only [sourceTestCurveAt_of_lt _ (ho i), sourceTestCurveAt_of_lt _ (ho j)] using h
  have hraw : (⨆ i : J, u i) = ⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r := by
    have h := sourceIncreasing_iSup_tail
      (fun i ↦ sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega Γ hm r) i₀
    convert h using 1
    exact iSup_congr fun i ↦ (sourceTestCurveAt_of_lt _ (ho i)).symm
  have hrawP : (⨆ i : J, sourceSingularityEnvelope (θ.add η) (u i)) =
      ⨆ i, sourceTestCurveAt ((Γ i).semipositiveProjection omega η hη).toSourceTestCurvePredata r := by
    have h := sourceIncreasing_iSup_tail
      (fun i ↦ sourceTestCurveAt ((Γ i).semipositiveProjection omega η hη).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega
        (fun i ↦ (Γ i).semipositiveProjection omega η hη)
        (sourceTestCurveSemipositiveProjectedFamily_monotone omega η hη Γ hm) r) i₀
    convert h using 1
    apply iSup_congr
    intro i
    rw [sourceTestCurveAt_of_lt ((Γ i.val).semipositiveProjection omega η hη).toSourceTestCurvePredata
      (ho i)]
    rfl
  have hid := sourceOrdinaryEnvelope_increasing_directed_eq omega
    (fun i : J ↦ sourceThetaPSH_add_semipositive η hη ((Γ i.val).thetaPSH ⟨r, ho i⟩))
    (fun i ↦ (Γ i.val).semipositiveProjectionInput_positive omega η hη ⟨r, ho i⟩) hmono
    (C := 0) (fun i x ↦ by
      simpa only [EReal.coe_zero, Pi.zero_apply] using (Γ i.val).le_zero ⟨r, ho i⟩ x)
  change sourceSingularityEnvelope (θ.add η)
      (uscRegularization (⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)) =
    uscRegularization (⨆ i,
      sourceTestCurveAt ((Γ i).semipositiveProjection omega η hη).toSourceTestCurvePredata r)
  rw [← hraw, ← hrawP]
  exact hid.symm

/-- Whole original lma:suptestcurvcompatible for semipositive added forms. -/
theorem source_test_curve_increasingSup_semipositive_projection_compatible
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i ↦ (Γ i).max)) :
    (SourceTestCurve.increasingSup omega Γ hm hbound).semipositiveProjection omega η hη =
      SourceTestCurve.increasingSup omega (fun i ↦ (Γ i).semipositiveProjection omega η hη)
        (sourceTestCurveSemipositiveProjectedFamily_monotone omega η hη Γ hm)
        (sourceTestCurveSemipositiveProjectedFamily_bddAbove omega η hη Γ hbound) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.semipositiveProjection_max, SourceTestCurve.increasingSup_max]
    rfl
  · intro r hr _hs
    simp only [SourceTestCurve.increasingSup_potential]
    exact sourceTestCurveSupPotential_semipositiveProjection omega η hη Γ hm hr

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Nonnegative scaling retains semipositivity of the entire actual added form. -/
theorem sourceScaledSemipositiveForm_isSemipositive
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) {c : ℝ} (hc : 0 ≤ c) :
    (atlasClosedFormToNative
      (nativeClosedFormToAtlas (c • atlasClosedFormToNative η))).val.IsSemipositive := by
  rw [sourceNativeAtlasForm_roundTrip]
  exact KahlerDomination.isSemipositive_smul hη hc

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The two scaled/enlarged backgrounds are equal as actual full atlas forms. -/
theorem sourceScaledSemipositiveProjectionBackground_eq
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)) (c : ℝ) :
    (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)).add
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative η)) =
      nativeClosedFormToAtlas (c • atlasClosedFormToNative (θ.add η)) := by
  apply Function.LeftInverse.injective (fun T ↦ sourceAtlasNativeForm_roundTrip T)
  simp only [sourceNativeClosedForm_add, sourceNativeAtlasForm_roundTrip, smul_add]

/-- Whole original lma:testcurvrescompatible, including every semipositive eta. -/
theorem source_test_curve_scaling_semipositive_projection_compatible
    (omega : KahlerBackground n M) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (Γ : SourceTestCurve θ) {c : ℝ} (hc : 0 < c) :
    ((Γ.positiveScale hc).semipositiveProjection omega
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative η))
        (sourceScaledSemipositiveForm_isSemipositive η hη hc.le)).castBackground
          (sourceScaledSemipositiveProjectionBackground_eq θ η c) =
      (Γ.semipositiveProjection omega η hη).positiveScale hc := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.castBackground_max, SourceTestCurve.semipositiveProjection_max,
      SourceTestCurve.positiveScale_max]
  · intro r hr hs
    have hrl : r < ((Γ.positiveScale hc).semipositiveProjection omega
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative η))
        (sourceScaledSemipositiveForm_isSemipositive η hη hc.le)).max := by
      simpa only [SourceTestCurve.castBackground_max] using hr
    rw [SourceTestCurve.castBackground_potential _ _ r hrl hr]
    change r < c * Γ.max at hs
    have hsrc : r / c < Γ.max := (div_lt_iff₀ hc).mpr (by nlinarith)
    change sourceSingularityEnvelope
      ((nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)).add
        (nativeClosedFormToAtlas (c • atlasClosedFormToNative η)))
      (fun x ↦ (c : EReal) * Γ.potential ⟨r / c, hsrc⟩ x) =
        fun x ↦ (c : EReal) * sourceSingularityEnvelope (θ.add η) (Γ.potential ⟨r / c, hsrc⟩) x
    rw [sourceScaledSemipositiveProjectionBackground_eq θ η c,
      sourceOrdinaryEnvelope_positiveScaling _ hc]

end SGPT.PSH.VariableComplexAtlas
