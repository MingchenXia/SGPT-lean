import SGPT.PSH.SourceNAOrder
import SGPT.PSH.SourceTestCurveSumAlgebra
import SGPT.PSH.SourceGlobalOrderAddition
import SGPT.PSH.SourceGlobalOrderSupremum

/-! # Global P-type of the actual ordinary test-curve sum

The strict-open convolution and a manufactured common smooth background
allow the existing genuine addition and USC-supremum producers to be reused.
No ideal-equivalence operation or new analytic hypothesis is introduced.
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
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ σ θ' σ' : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The same genuine raw convolutions have the same global P-type when
both input curves do, even across four different closed backgrounds. -/
theorem sourceTestCurveRawSum_PEquivalent_of_mutual_order
    (omega : KahlerBackground n M)
    (G : SourceTestCurve θ) (H : SourceTestCurve σ)
    (G' : SourceTestCurve θ') (H' : SourceTestCurve σ')
    (hG : SourceTestCurvePOrder G G') (hG' : SourceTestCurvePOrder G' G)
    (hH : SourceTestCurvePOrder H H') (hH' : SourceTestCurvePOrder H' H)
    {r : ℝ} (hr : r < G.max + H.max) :
    GlobalPComparison.sourcePEquivalent (n := n)
      (sourceTestCurveRawSum G.toSourceTestCurvePredata H.toSourceTestCurvePredata r)
      (sourceTestCurveRawSum G'.toSourceTestCurvePredata H'.toSourceTestCurvePredata r) := by
  have eG : G.max = G'.max := le_antisymm hG.cutoff_le hG'.cutoff_le
  have eH : H.max = H'.max := le_antisymm hH.cutoff_le hH'.cutoff_le
  let J := Ioo (r - H.max) G.max
  have : Nonempty J := ⟨⟨((r - H.max) + G.max) / 2, by constructor <;> linarith⟩⟩
  let u : J → M → EReal := fun d x ↦
    sourceTestCurveAt G.toSourceTestCurvePredata d.val x +
      sourceTestCurveAt H.toSourceTestCurvePredata (r - d.val) x
  let v : J → M → EReal := fun d x ↦
    sourceTestCurveAt G'.toSourceTestCurvePredata d.val x +
      sourceTestCurveAt H'.toSourceTestCurvePredata (r - d.val) x
  let A := atlasClosedFormToNative θ + atlasClosedFormToNative σ
  let B := atlasClosedFormToNative θ' + atlasClosedFormToNative σ'
  obtain ⟨a, ha, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega (A - B)
  let T := nativeClosedFormToAtlas (A + a • omega.form)
  have hAT : (atlasClosedFormToNative T -
      atlasClosedFormToNative (nativeClosedFormToAtlas A)).val.IsSemipositive := by
    simpa only [T, sourceNativeAtlasForm_roundTrip, add_sub_cancel_left] using
      KahlerDomination.isSemipositive_smul omega.isSemipositive ha.le
  have hBT : (atlasClosedFormToNative T -
      atlasClosedFormToNative (nativeClosedFormToAtlas B)).val.IsSemipositive := by
    have he : (A + a • omega.form) - B = (A - B) + a • omega.form := by abel
    simpa only [T, sourceNativeAtlasForm_roundTrip, he] using hsemi
  have hd (d : J) : r - d.val < H.max := by linarith [d.property.1]
  have hdG' (d : J) : d.val < G'.max := by rw [← eG]; exact d.property.2
  have hdH' (d : J) : r - d.val < H'.max := by rw [← eH]; exact hd d
  have hu (d : J) : (ofFixedModel n M).IsThetaPSH T (u d) := by
    dsimp [u]
    rw [sourceTestCurveAt_of_lt G.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt H.toSourceTestCurvePredata (hd d)]
    exact sourceThetaPSH_of_semipositive_difference hAT
      (sourceIndependentSum_thetaPSH (G.thetaPSH _) (H.thetaPSH _))
  have hv (d : J) : (ofFixedModel n M).IsThetaPSH T (v d) := by
    dsimp [v]
    rw [sourceTestCurveAt_of_lt G'.toSourceTestCurvePredata (hdG' d),
      sourceTestCurveAt_of_lt H'.toSourceTestCurvePredata (hdH' d)]
    exact sourceThetaPSH_of_semipositive_difference hBT
      (sourceIndependentSum_thetaPSH (G'.thetaPSH _) (H'.thetaPSH _))
  have hp (d : J) : GlobalPComparison.sourcePEquivalent (n := n) (u d) (v d) := by
    dsimp [u, v]
    rw [sourceTestCurveAt_of_lt G.toSourceTestCurvePredata d.property.2,
      sourceTestCurveAt_of_lt H.toSourceTestCurvePredata (hd d),
      sourceTestCurveAt_of_lt G'.toSourceTestCurvePredata (hdG' d),
      sourceTestCurveAt_of_lt H'.toSourceTestCurvePredata (hdH' d)]
    exact SGPT.PSH.GlobalOrderAddition.sourcePEquivalent_add omega
      ⟨θ, G.thetaPSH _⟩ ⟨σ, H.thetaPSH _⟩
      ⟨θ', G'.thetaPSH _⟩ ⟨σ', H'.thetaPSH _⟩
      ⟨hG.slice_le d.val d.property.2, hG'.slice_le d.val (hdG' d)⟩
      ⟨hH.slice_le (r - d.val) (hd d), hH'.slice_le (r - d.val) (hdH' d)⟩
  have huBound : ∃ C : ℝ, ∀ d x, u d x ≤ (C : EReal) := by
    refine ⟨0, ?_⟩
    intro d x
    change u d x ≤ (0 : EReal)
    exact add_nonpos (G.at_le_zero d.val x) (H.at_le_zero (r - d.val) x)
  have hvBound : ∃ C : ℝ, ∀ d x, v d x ≤ (C : EReal) := by
    refine ⟨0, ?_⟩
    intro d x
    change v d x ≤ (0 : EReal)
    exact add_nonpos (G'.at_le_zero d.val x) (H'.at_le_zero (r - d.val) x)
  have huRaw : sourceTestCurveRawSum G.toSourceTestCurvePredata H.toSourceTestCurvePredata r =
      uscSup u := sourceTestCurveRawSum_eq_uscSup_open _ _ hr
  have hvRaw : sourceTestCurveRawSum G'.toSourceTestCurvePredata H'.toSourceTestCurvePredata r =
      uscSup v := by
    have hr' : r < G'.max + H'.max := by simpa only [← eG, ← eH] using hr
    have hraw := sourceTestCurveRawSum_eq_uscSup_open
      G'.toSourceTestCurvePredata H'.toSourceTestCurvePredata hr'
    change sourceTestCurveRawSum G'.toSourceTestCurvePredata H'.toSourceTestCurvePredata r =
      uscRegularization (fun x ↦ ⨆ d : Ioo (r - H'.max) G'.max,
        sourceTestCurveAt G'.toSourceTestCurvePredata d.val x +
          sourceTestCurveAt H'.toSourceTestCurvePredata (r - d.val) x) at hraw
    rw [← eG, ← eH] at hraw
    exact hraw
  rw [huRaw, hvRaw]
  exact ⟨sourcePOrder_uscSup omega hu hv huBound hvBound (fun d ↦ (hp d).1),
    sourcePOrder_uscSup omega hv hu hvBound huBound (fun d ↦ (hp d).2)⟩

/-- An actual ordinary sum slice retains its genuine raw input's global P-type. -/
theorem SourceTestCurve.sum_slice_raw_PEquivalent (omega : KahlerBackground n M)
    (G : SourceTestCurve θ) (H : SourceTestCurve σ)
    (r : ℝ) (hr : r < (SourceTestCurve.sum omega G H).max) :
    GlobalPComparison.sourcePEquivalent (n := n)
      ((SourceTestCurve.sum omega G H).potential ⟨r, hr⟩)
      (sourceTestCurveRawSum G.toSourceTestCurvePredata H.toSourceTestCurvePredata r) := by
  have hp := SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope omega
    (atlasClosedFormToNative
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))
    ((isThetaPSH_iff_nativeThetaPotential _ _).mp
      (sourceTestCurveRawSum_thetaPSH G.toSourceTestCurvePredata H.toSourceTestCurvePredata hr.le))
  change GlobalPComparison.sourcePEquivalent (n := n)
    (sourceSingularityEnvelope _ _) _
  rw [sourceSingularityEnvelope_eq_native]
  exact ⟨hp.2, hp.1⟩

/-- Mutual global P-comparison of actual sums, allowing independent whole
backgrounds and ambient construction metrics. -/
theorem SourceTestCurve.sum_POrder_equivalent
    (omega omega' : KahlerBackground n M)
    (G : SourceTestCurve θ) (H : SourceTestCurve σ)
    (G' : SourceTestCurve θ') (H' : SourceTestCurve σ')
    (hG : SourceTestCurvePOrder G G') (hG' : SourceTestCurvePOrder G' G)
    (hH : SourceTestCurvePOrder H H') (hH' : SourceTestCurvePOrder H' H) :
    SourceTestCurvePOrder (SourceTestCurve.sum omega G H) (SourceTestCurve.sum omega' G' H') ∧
      SourceTestCurvePOrder (SourceTestCurve.sum omega' G' H') (SourceTestCurve.sum omega G H) := by
  have hc : (SourceTestCurve.sum omega G H).max = (SourceTestCurve.sum omega' G' H').max := by
    simp only [SourceTestCurve.sum_max]
    exact congrArg₂ (fun a b : ℝ ↦ a + b)
      (le_antisymm hG.cutoff_le hG'.cutoff_le) (le_antisymm hH.cutoff_le hH'.cutoff_le)
  have hs (r : ℝ) (hr : r < (SourceTestCurve.sum omega G H).max)
      (hr' : r < (SourceTestCurve.sum omega' G' H').max) :
      GlobalPComparison.sourcePEquivalent (n := n)
        ((SourceTestCurve.sum omega G H).potential ⟨r, hr⟩)
        ((SourceTestCurve.sum omega' G' H').potential ⟨r, hr'⟩) := by
    have hu := SourceTestCurve.sum_slice_raw_PEquivalent omega G H r hr
    have hv := SourceTestCurve.sum_slice_raw_PEquivalent omega' G' H' r hr'
    have hp := sourceTestCurveRawSum_PEquivalent_of_mutual_order omega G H G' H' hG hG' hH hH' hr
    exact ⟨GlobalPComparison.sourcePOrder_trans omega
        (GlobalPComparison.sourcePOrder_trans omega hu.1 hp.1) hv.2,
      GlobalPComparison.sourcePOrder_trans omega
        (GlobalPComparison.sourcePOrder_trans omega hv.1 hp.2) hu.2⟩
  exact ⟨⟨hc.le, fun r hr ↦ (hs r hr (hr.trans_le hc.le)).1⟩,
    ⟨hc.ge, fun r hr ↦ (hs r (hr.trans_le hc.ge) hr).2⟩⟩

end SGPT.PSH.VariableComplexAtlas
