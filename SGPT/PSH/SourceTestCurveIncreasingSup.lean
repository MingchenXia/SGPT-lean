import SGPT.PSH.SourceTestCurveBackgroundProjection
import SGPT.PSH.SourceIModelTestCurves
import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Spatial USC closure preserves arbitrary joins of its own closures. -/
theorem sourceUscRegularization_iSup_closure {X I : Type*} [TopologicalSpace X]
    (f : I → X → EReal) :
    uscRegularization (⨆ i, uscRegularization (f i)) =
      uscRegularization (⨆ i, f i) := by
  apply le_antisymm
  · apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    apply iSup_le
    intro i
    exact uscRegularization_le (upperSemicontinuous_uscRegularization _)
      ((le_iSup f i).trans (le_uscRegularization _))
  · apply uscRegularization_mono
    exact iSup_mono fun i => le_uscRegularization (f i)

/-- Nested genuine spatial USC suprema commute, with the literal raw family. -/
theorem sourceUscRegularization_iSup_comm {X I J : Type*} [TopologicalSpace X]
    (f : I → J → X → EReal) :
    uscRegularization (⨆ i, uscRegularization (⨆ j, f i j)) =
      uscRegularization (⨆ j, uscRegularization (⨆ i, f i j)) := by
  rw [sourceUscRegularization_iSup_closure, sourceUscRegularization_iSup_closure]
  congr 1
  exact iSup_comm


/-- A directed tail retains the literal whole-family pointwise supremum. -/
theorem sourceIncreasing_iSup_tail {I X : Type*} [Preorder I] [IsDirectedOrder I]
    (u : I → X → EReal) (hm : Monotone u) (i₀ : I) :
    (⨆ i : {i : I // i₀ ≤ i}, u i.val) = ⨆ i, u i := by
  apply le_antisymm
  · exact iSup_le fun i => le_iSup u i.val
  · apply iSup_le
    intro j
    obtain ⟨k, hjk, h₀k⟩ := exists_ge_ge j i₀
    exact (hm hjk).trans (le_iSup (fun i : {i : I // i₀ ≤ i} => u i.val) ⟨k,h₀k⟩)

/-- The actual real least upper bound of the original cutoffs. -/
def sourceTestCurveSupCutoff {I : Type*} (Γ : I → SourceTestCurve θ) : ℝ :=
  sSup (range fun i => (Γ i).max)

/-- The literal whole-extension spatial USC supremum, at every real parameter. -/
def sourceTestCurveSupPotential {I : Type*} (Γ : I → SourceTestCurve θ)
    (r : ℝ) : M → EReal :=
  uscRegularization (⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every strict subcutoff parameter is open in some actual original curve. -/
theorem sourceTestCurveSupCutoff_exists {I : Type*} [Nonempty I]
    (Γ : I → SourceTestCurve θ) {r : ℝ} (hr : r < sourceTestCurveSupCutoff Γ) :
    ∃ i, r < (Γ i).max := by
  obtain ⟨a, ⟨i, rfl⟩, ha⟩ := exists_lt_of_lt_csSup (range_nonempty _) hr
  exact ⟨i,ha⟩

/-- Original intrinsic order makes the SAME whole extensions pointwise increasing. -/
theorem sourceTestCurveSup_extension_monotone {I : Type*} [Preorder I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j)) (r : ℝ) :
    Monotone (fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r) := by
  intro i j hij
  exact (sourceTestCurvePOrder_iff_extension omega (Γ i) (Γ j)).mp (hm i j hij) r


/-- The literal entire spatial USC supremum is a genuine positive ordinary model. -/
theorem sourceTestCurveSupPotential_model {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    {r : ℝ} (hr : r < sourceTestCurveSupCutoff Γ) :
    SourceModelPotential θ (sourceTestCurveSupPotential Γ r) := by
  obtain ⟨i₀, hr₀⟩ := sourceTestCurveSupCutoff_exists Γ hr
  let J := {i : I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirectedOrder J := ⟨by
    intro i j
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k,i.property.trans hik⟩,hik,hjk⟩⟩
  have ho (i : J) : r < (Γ i.val).max :=
    hr₀.trans_le (hm i₀ i.val i.property).cutoff_le
  let u : J → M → EReal := fun i => (Γ i.val).potential ⟨r,ho i⟩
  have hmodel (i : J) : SourceModelPotential θ (u i) := (Γ i.val).slice_model omega _
  have hmono : Monotone u := by
    intro i j hij
    have h := sourceTestCurveSup_extension_monotone omega Γ hm r hij
    simpa only [sourceTestCurveAt_of_lt _ (ho i), sourceTestCurveAt_of_lt _ (ho j)] using h
  have hb (i : J) (x : M) : u i x ≤ (0 : EReal) := (Γ i.val).le_zero _ x
  have hp := sourceModelPotential_increasing_uscSup omega hmodel hmono hb
  have heq : (⨆ i : J, u i) =
      ⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r := by
    have htail := sourceIncreasing_iSup_tail
      (fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega Γ hm r) i₀
    convert htail using 1
    congr 1
    funext i
    exact (sourceTestCurveAt_of_lt _ (ho i)).symm
  simpa only [heq, sourceTestCurveSupPotential] using hp


omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal all-index USC majorization of every actual whole slice. -/
theorem sourceTestCurveSupPotential_ge {I : Type*} (Γ : I → SourceTestCurve θ)
    (i : I) (r : ℝ) :
    sourceTestCurveAt (Γ i).toSourceTestCurvePredata r ≤ sourceTestCurveSupPotential Γ r :=
  (le_iSup (fun j => sourceTestCurveAt (Γ j).toSourceTestCurvePredata r) i).trans
    (le_uscRegularization _)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Actual normalization bounds the literal spatial USC supremum on all real parameters. -/
theorem sourceTestCurveSupPotential_le_zero {I : Type*} (Γ : I → SourceTestCurve θ)
    (r : ℝ) : sourceTestCurveSupPotential Γ r ≤ 0 := by
  apply uscRegularization_le upperSemicontinuous_const
  exact iSup_le fun i => (Γ i).toSourceTestCurvePredata.at_le_zero r

private theorem supChord_value_tendsto {F : Filter ℕ}
    {a b : ℕ → EReal} {A B : EReal} (ha : Tendsto a F (𝓝 A))
    (hb : Tendsto b F (𝓝 B)) (hA : A ≤ 0) (hB : B ≤ 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Tendsto (fun i => (t : EReal) * a i + ((1-t : ℝ) : EReal) * b i) F
      (𝓝 ((t : EReal) * A + ((1-t : ℝ) : EReal) * B)) := by
  have hta := EReal.Tendsto.const_mul ha
    (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
  have htb := EReal.Tendsto.const_mul hb
    (Or.inl (EReal.coe_ne_bot (1-t))) (Or.inl (EReal.coe_ne_top (1-t)))
  have hAtop : (t : EReal) * A ≠ ⊤ := ne_of_lt
    ((mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr ht0.le) hA).trans_lt (by simp))
  have hBtop : ((1-t : ℝ) : EReal) * B ≠ ⊤ := ne_of_lt
    ((mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_pos.mpr ht1).le) hB).trans_lt (by simp))
  exact (EReal.continuousAt_add (Or.inl hAtop) (Or.inr hBtop)).tendsto.comp
    (hta.prodMk_nhds htb)


/-- Genuine simultaneous Choquet selection preserves both endpoint limits,
so the literal USC family satisfies every strict chord inequality. -/
theorem sourceTestCurveSupPotential_convexComb_le {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (p q : Iio (sourceTestCurveSupCutoff Γ)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceTestCurveSupPotential Γ p) (sourceTestCurveSupPotential Γ q) ≤
      sourceTestCurveSupPotential Γ (t*p.val+(1-t)*q.val) := by
  classical
  obtain ⟨ip,hip⟩ := sourceTestCurveSupCutoff_exists Γ p.property
  obtain ⟨iq,hiq⟩ := sourceTestCurveSupCutoff_exists Γ q.property
  obtain ⟨i₀,hpi₀,hqi₀⟩ := exists_ge_ge ip iq
  have hp₀ := hip.trans_le (hm ip i₀ hpi₀).cutoff_le
  have hq₀ := hiq.trans_le (hm iq i₀ hqi₀).cutoff_le
  let v : I → Bool → M → EReal := fun i b =>
    sourceTestCurveAt (Γ i).toSourceTestCurvePredata (if b then p.val else q.val)
  have hv : ∀ b, Monotone fun i => v i b := fun b =>
    sourceTestCurveSup_extension_monotone omega Γ hm _
  obtain ⟨j,hj,hj₀,hreg⟩ :=
    IncreasingMixedDirectedNets.exists_monotone_sequence_uscRegularization_iSup_eq i₀ hv
  have hpj (k : ℕ) : p.val < (Γ (j k)).max :=
    hp₀.trans_le (hm i₀ (j k) (hj₀ k)).cutoff_le
  have hqj (k : ℕ) : q.val < (Γ (j k)).max :=
    hq₀.trans_le (hm i₀ (j k) (hj₀ k)).cutoff_le
  let A : ℕ → M → EReal := fun k => (Γ (j k)).potential ⟨p.val,hpj k⟩
  let B : ℕ → M → EReal := fun k => (Γ (j k)).potential ⟨q.val,hqj k⟩
  have hA (k : ℕ) := (Γ (j k)).native_thetaPSH ⟨p.val,hpj k⟩
  have hB (k : ℕ) := (Γ (j k)).native_thetaPSH ⟨q.val,hqj k⟩
  have hAm : Monotone A := by
    intro k l hkl
    have h := (hv true) (hj hkl)
    simpa only [v, Bool.true_eq, if_true, sourceTestCurveAt_of_lt _ (hpj k),
      sourceTestCurveAt_of_lt _ (hpj l)] using h
  have hBm : Monotone B := by
    intro k l hkl
    have h := (hv false) (hj hkl)
    simpa only [v, Bool.false_eq_true, if_false, sourceTestCurveAt_of_lt _ (hqj k),
      sourceTestCurveAt_of_lt _ (hqj l)] using h
  have heqA : uscRegularization (⨆ k, A k) = sourceTestCurveSupPotential Γ p := by
    have h := hreg true
    simpa only [v, if_true, sourceTestCurveAt_of_lt _ (hpj _), sourceTestCurveSupPotential] using h
  have heqB : uscRegularization (⨆ k, B k) = sourceTestCurveSupPotential Γ q := by
    have h := hreg false
    simpa only [v, Bool.false_eq_true, if_false, sourceTestCurveAt_of_lt _ (hqj _), sourceTestCurveSupPotential] using h
  have hUp := (sourceTestCurveSupPotential_model omega Γ hm p.property).thetaPSH
  have hUq := (sourceTestCurveSupPotential_model omega Γ hm q.property).thetaPSH
  have hUpn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hUp
  have hUqn := (isThetaPSH_iff_nativeThetaPotential θ _).mp hUq
  have hregChord : uscRegularization (⨆ k, convexComb t (A k) (B k)) =
      convexComb t (sourceTestCurveSupPotential Γ p) (sourceTestCurveSupPotential Γ q) := by
    apply SingularModelIncreasingAERegularizedLimit.uscRegularization_iSup_eq_of_monotone_ae_chart_tendsto
      (fun k => isThetaPshPotential_convexComb (hA k) (hB k) ht0 ht1)
      (isThetaPshPotential_convexComb hUpn hUqn ht0 ht1)
      (fun x k l hkl => convexComb_mono ht0.le ht1.le (hAm hkl) (hBm hkl) x)
    intro e
    have ha := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hA hAm (heqA.symm ▸ hUpn) e
    have hb := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      hB hBm (heqB.symm ▸ hUqn) e
    rw [heqA] at ha
    rw [heqB] at hb
    filter_upwards [ha,hb] with z ha hb
    have hla : Tendsto (fun k => A k (e.val.symm z)) atTop
        (𝓝 (sourceTestCurveSupPotential Γ p (e.val.symm z))) := by
      change Tendsto (fun k => chartFunction (A k) e z) atTop
        (𝓝 (chartFunction (sourceTestCurveSupPotential Γ p) e z))
      rw [← ha]
      exact tendsto_atTop_iSup (fun k l hkl => hAm hkl (e.val.symm z))
    have hlb : Tendsto (fun k => B k (e.val.symm z)) atTop
        (𝓝 (sourceTestCurveSupPotential Γ q (e.val.symm z))) := by
      change Tendsto (fun k => chartFunction (B k) e z) atTop
        (𝓝 (chartFunction (sourceTestCurveSupPotential Γ q) e z))
      rw [← hb]
      exact tendsto_atTop_iSup (fun k l hkl => hBm hkl (e.val.symm z))
    exact supChord_value_tendsto hla hlb
      (sourceTestCurveSupPotential_le_zero Γ p _)
      (sourceTestCurveSupPotential_le_zero Γ q _) ht0 ht1
  rw [← hregChord]
  apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
  apply iSup_le
  intro k x
  have hc := (Γ (j k)).toSourceTestCurvePredata.convexComb_le
    ⟨p.val,hpj k⟩ ⟨q.val,hqj k⟩ ht0 ht1 x
  have hmid : t*p.val+(1-t)*q.val < (Γ (j k)).max := by
    nlinarith [mul_pos ht0 (sub_pos.mpr (hpj k)),
      mul_pos (sub_pos.mpr ht1) (sub_pos.mpr (hqj k))]
  exact hc.trans (by
    have h := sourceTestCurveSupPotential_ge Γ (j k) (t*p.val+(1-t)*q.val) x
    simpa only [sourceTestCurveAt_of_lt _ hmid, sourceTestCurveSupPotential] using h)


omit [BorelSpace M] [ConnectedSpace M] in
/-- The original finite cutoff bound gives its actual least-upper-bound comparison. -/
theorem sourceTestCurveSupCutoff_ge {I : Type*} (Γ : I → SourceTestCurve θ)
    (hbound : BddAbove (range fun i => (Γ i).max)) (i : I) :
    (Γ i).max ≤ sourceTestCurveSupCutoff Γ := le_csSup hbound (mem_range_self i)

/-- Genuine original preliminary data for the increasing spatial USC supremum. -/
def sourceTestCurveIncreasingSupPredata {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j)) :
    SourceTestCurvePredata θ where
  max := sourceTestCurveSupCutoff Γ
  potential r := sourceTestCurveSupPotential Γ r
  thetaPSH r := (sourceTestCurveSupPotential_model omega Γ hm r.property).thetaPSH
  antitone x _p _q hpq := uscRegularization_mono
    (iSup_mono fun i y => (Γ i).toSourceTestCurvePredata.at_antitone y hpq) x
  concave x := sourceTestCurveNegativeTrace_convex_of_chords _
    (fun p q _ ht0 ht1 => sourceTestCurveSupPotential_convexComb_le omega Γ hm p q ht0 ht1) x
  fixedPoint r := (sourceTestCurveSupPotential_model omega Γ hm r.property).choose_spec.1.symm

/-- The actual increasing supremum, with positive limit mass produced internally. -/
def SourceTestCurve.increasingSup {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (_hbound : BddAbove (range fun i => (Γ i).max)) : SourceTestCurve θ where
  toSourceTestCurvePredata := sourceTestCurveIncreasingSupPredata omega Γ hm
  positiveLimitMass := by
    have : Nonempty (Iio (sourceTestCurveSupCutoff Γ)) :=
      ⟨⟨sourceTestCurveSupCutoff Γ-1, by change sourceTestCurveSupCutoff Γ-1 < _; linarith⟩⟩
    have hp := sourceIncreasingOrdinary_sup_positive omega
      (fun r : Iio (sourceTestCurveSupCutoff Γ) =>
        (sourceTestCurveSupPotential_model omega Γ hm r.property).thetaPSH)
      (fun r => (sourceTestCurveSupPotential_model omega Γ hm r.property).choose_spec.2)
      (C := 0) (fun r x => by
        simpa only [EReal.coe_zero, Pi.zero_apply] using sourceTestCurveSupPotential_le_zero Γ r x)
    have heq : (⨆ r : Iio (sourceTestCurveSupCutoff Γ), sourceTestCurveSupPotential Γ r) =
        fun x => ⨆ r : Iio (sourceTestCurveSupCutoff Γ), sourceTestCurveSupPotential Γ r x := by
      funext x
      exact iSup_apply
    simpa only [heq, sourceTestCurveLimit, sourceTestCurveIncreasingSupPredata, uscSup] using hp

/-- The literal real least upper bound is the actual output cutoff. -/
theorem SourceTestCurve.increasingSup_max {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.increasingSup omega Γ hm hbound).max = sourceTestCurveSupCutoff Γ := rfl

/-- Every actual open output potential is the literal all-index spatial USC supremum. -/
theorem SourceTestCurve.increasingSup_potential {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max))
    (r : Iio (SourceTestCurve.increasingSup omega Γ hm hbound).max) :
    (SourceTestCurve.increasingSup omega Γ hm hbound).potential r =
      sourceTestCurveSupPotential Γ r := rfl


/-- Under the ORIGINAL standing big-class hypothesis, every actual output slice
is I-model whenever every original input slice is I-model. -/
theorem SourceTestCurve.increasingSup_isIModel {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hI : ∀ i, SourceTestCurveIsIModel (Γ i)) :
    SourceTestCurveIsIModel (SourceTestCurve.increasingSup omega Γ hm hbound) := by
  intro r
  obtain ⟨i₀,hr₀⟩ := sourceTestCurveSupCutoff_exists Γ r.property
  let u : I → M → EReal := fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r
  have hu : Monotone u := sourceTestCurveSup_extension_monotone omega Γ hm r
  obtain ⟨j,hj,hj₀,hreg⟩ :=
    IncreasingMixedDirectedNets.exists_monotone_sequence_uscRegularization_iSup_eq
      (u := fun i (_ : Unit) => u i) i₀ (fun _ => hu)
  have hopen (k : ℕ) : r.val < (Γ (j k)).max :=
    hr₀.trans_le (hm i₀ (j k) (hj₀ k)).cutoff_le
  let v : ℕ → M → EReal := fun k => (Γ (j k)).potential ⟨r.val,hopen k⟩
  have hv (k : ℕ) := (Γ (j k)).native_thetaPSH ⟨r.val,hopen k⟩
  have hvm : Monotone v := by
    intro k l hkl
    have h := hu (hj hkl)
    simpa only [u, sourceTestCurveAt_of_lt _ (hopen k),
      sourceTestCurveAt_of_lt _ (hopen l)] using h
  have heq : uscRegularization (⨆ k, v k) = sourceTestCurveSupPotential Γ r := by
    have h := hreg ()
    simpa only [u, sourceTestCurveAt_of_lt _ (hopen _), sourceTestCurveSupPotential] using h
  have hmodel := (sourceTestCurveSupPotential_model omega Γ hm r.property).toNative
  have hid := IEnvelopeIncreasingRegularizedSupremum.iSingularityEnvelope_regularized_iSup_eq
    omega (atlasClosedFormToNative θ) hbig hv hvm hmodel.plurisubharmonic heq hmodel.positive_mass
  have hfix (k : ℕ) : IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val (v k) = v k :=
    (hI (j k) ⟨r.val,hopen k⟩).2.symm
  have hsup : (⨆ k, IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val (v k)) =
      ⨆ k, v k := iSup_congr hfix
  have hnormalized := congrArg uscRegularization hsup
  have hfinal := hnormalized.symm.trans hid
  have hout : sourceTestCurveSupPotential Γ r =
      IEnvelope.iSingularityEnvelope (atlasClosedFormToNative θ).val (sourceTestCurveSupPotential Γ r) :=
    heq.symm.trans hfinal
  exact ⟨hmodel.plurisubharmonic,hout⟩

/-- Actual produced-limit basedness puts the I-model supremum in the original positive union. -/
theorem SourceTestCurve.increasingSup_mem_iModelPositive {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hI : ∀ i, SourceTestCurveIsIModel (Γ i)) :
    SourceTestCurve.increasingSup omega Γ hm hbound ∈ SourceIModelTestCurvesPositive θ :=
  (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
    (SourceTestCurve.increasingSup_isIModel omega Γ hm hbound hbig hI)


omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Any original lower open interval computes the SAME actual minus-infinity limit. -/
theorem SourceTestCurvePredata.limit_eq_usc_iSup_below (Γ : SourceTestCurvePredata θ)
    (b : ℝ) (hb : b ≤ Γ.max) :
    sourceTestCurveLimit Γ = uscRegularization
      (⨆ r : Iio b, sourceTestCurveAt Γ r) := by
  have hraw : (⨆ r : Iio Γ.max, Γ.potential r) =
      ⨆ r : Iio b, sourceTestCurveAt Γ r := by
    apply le_antisymm
    · apply iSup_le
      intro r
      let s : Iio b := ⟨min r.val b-1, by change min r.val b-1 < b; linarith [min_le_right r.val b]⟩
      have hsr : s.val ≤ r.val := by dsimp [s]; linarith [min_le_left r.val b]
      have hsopen : s.val < Γ.max := s.property.trans_le hb
      have hle : Γ.potential r ≤ sourceTestCurveAt Γ s := by
        rw [sourceTestCurveAt_of_lt _ hsopen]
        exact fun x => Γ.antitone x hsr
      exact hle.trans (le_iSup (fun s : Iio b => sourceTestCurveAt Γ s) s)
    · apply iSup_le
      intro r
      rw [sourceTestCurveAt_of_lt _ (r.property.trans_le hb)]
      exact le_iSup Γ.potential ⟨r.val,r.property.trans_le hb⟩
  unfold sourceTestCurveLimit uscSup
  have hfun : (fun x => ⨆ r : Iio Γ.max, Γ.potential r x) =
      ⨆ r : Iio Γ.max, Γ.potential r := by funext x; exact (iSup_apply).symm
  rw [hfun,hraw]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Whole-extension order preserves the SAME original spatial-USC limits. -/
theorem sourceTestCurveLimit_mono_of_extension (Γ Δ : SourceTestCurve θ)
    (h : ∀ r, sourceTestCurveAt Γ.toSourceTestCurvePredata r ≤
      sourceTestCurveAt Δ.toSourceTestCurvePredata r) :
    sourceTestCurveLimit Γ.toSourceTestCurvePredata ≤
      sourceTestCurveLimit Δ.toSourceTestCurvePredata := by
  rw [Γ.toSourceTestCurvePredata.limit_eq_usc_iSup_below (min Γ.max Δ.max) (min_le_left _ _),
    Δ.toSourceTestCurvePredata.limit_eq_usc_iSup_below (min Γ.max Δ.max) (min_le_right _ _)]
  exact uscRegularization_mono (iSup_mono fun r => h r)


/-- The exact ORIGINAL minus-infinity limit commutes with the increasing USC supremum. -/
theorem SourceTestCurve.increasingSup_limit {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max)) :
    sourceTestCurveLimit (SourceTestCurve.increasingSup omega Γ hm hbound).toSourceTestCurvePredata =
      uscRegularization (⨆ i, sourceTestCurveLimit (Γ i).toSourceTestCurvePredata) := by
  classical
  let i₀ : I := Classical.arbitrary I
  let b := (Γ i₀).max
  let J := {i : I // i₀ ≤ i}
  have hbm : b ≤ sourceTestCurveSupCutoff Γ := sourceTestCurveSupCutoff_ge Γ hbound i₀
  have hU (r : ℝ) : sourceTestCurveSupPotential Γ r =
      uscRegularization (⨆ i : J, sourceTestCurveAt (Γ i.val).toSourceTestCurvePredata r) :=
    congrArg uscRegularization (sourceIncreasing_iSup_tail
      (fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega Γ hm r) i₀).symm
  have hstart : sourceTestCurveLimit
      (SourceTestCurve.increasingSup omega Γ hm hbound).toSourceTestCurvePredata =
      uscRegularization (⨆ r : Iio b, sourceTestCurveSupPotential Γ r) := by
    rw [(SourceTestCurve.increasingSup omega Γ hm hbound).toSourceTestCurvePredata.limit_eq_usc_iSup_below b hbm]
    apply congrArg uscRegularization
    apply iSup_congr
    intro r
    rw [sourceTestCurveAt_of_lt _ (r.property.trans_le hbm)]
    rfl
  have hlimitMono : Monotone (fun i => sourceTestCurveLimit (Γ i).toSourceTestCurvePredata) := by
    intro i j hij
    exact sourceTestCurveLimit_mono_of_extension (Γ i) (Γ j)
      ((sourceTestCurvePOrder_iff_extension omega (Γ i) (Γ j)).mp (hm i j hij))
  calc
    _ = uscRegularization (⨆ r : Iio b, sourceTestCurveSupPotential Γ r) := hstart
    _ = uscRegularization (⨆ r : Iio b,
        uscRegularization (⨆ i : J, sourceTestCurveAt (Γ i.val).toSourceTestCurvePredata r)) :=
      congrArg uscRegularization (iSup_congr fun r => hU r)
    _ = uscRegularization (⨆ i : J,
        uscRegularization (⨆ r : Iio b, sourceTestCurveAt (Γ i.val).toSourceTestCurvePredata r)) :=
      sourceUscRegularization_iSup_comm _
    _ = uscRegularization (⨆ i : J, sourceTestCurveLimit (Γ i.val).toSourceTestCurvePredata) := by
      apply congrArg uscRegularization
      exact iSup_congr fun i =>
        ((Γ i.val).toSourceTestCurvePredata.limit_eq_usc_iSup_below b
          (hm i₀ i.val i.property).cutoff_le).symm
    _ = _ := congrArg uscRegularization (sourceIncreasing_iSup_tail _ hlimitMono i₀)


/-- The existing whole projection/order identity preserves the actual directed order. -/
theorem sourceTestCurveProjectedFamily_monotone {I : Type*} [Preorder I]
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j)) :
    ∀ i j, i ≤ j → SourceTestCurvePOrder
      ((Γ i).backgroundProjection omega) ((Γ j).backgroundProjection omega) :=
  fun i j hij => (source_test_curve_background_projection_order_iff omega (Γ i) (Γ j)).mp (hm i j hij)

/-- The SAME finite original cutoff bound is valid for the actual projected family. -/
theorem sourceTestCurveProjectedFamily_bddAbove {I : Type*}
    (omega : KahlerBackground n M) (Γ : I → SourceTestCurve θ)
    (hbound : BddAbove (range fun i => (Γ i).max)) :
    BddAbove (range fun i => ((Γ i).backgroundProjection omega).max) := hbound

/-- Whole directed ordinary-envelope continuity identifies the literal output slice. -/
theorem sourceTestCurveSupPotential_backgroundProjection {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    {r : ℝ} (hr : r < sourceTestCurveSupCutoff Γ) :
    sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ)
      (sourceTestCurveSupPotential Γ r) =
      sourceTestCurveSupPotential (fun i => (Γ i).backgroundProjection omega) r := by
  obtain ⟨i₀,hr₀⟩ := sourceTestCurveSupCutoff_exists Γ hr
  let J := {i : I // i₀ ≤ i}
  have : Nonempty J := ⟨⟨i₀,le_rfl⟩⟩
  have : IsDirectedOrder J := ⟨by
    intro i j
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k,i.property.trans hik⟩,hik,hjk⟩⟩
  have ho (i : J) : r < (Γ i.val).max := hr₀.trans_le (hm i₀ i.val i.property).cutoff_le
  let u : J → M → EReal := fun i => (Γ i.val).potential ⟨r,ho i⟩
  have hmono : Monotone u := by
    intro i j hij
    have h := sourceTestCurveSup_extension_monotone omega Γ hm r hij
    simpa only [sourceTestCurveAt_of_lt _ (ho i), sourceTestCurveAt_of_lt _ (ho j)] using h
  have hraw : (⨆ i : J, u i) = ⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r := by
    have h := sourceIncreasing_iSup_tail
      (fun i => sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega Γ hm r) i₀
    convert h using 1
    exact iSup_congr fun i => (sourceTestCurveAt_of_lt _ (ho i)).symm
  have hrawP : (⨆ i : J, sourceSingularityEnvelope
      (sourceTestCurveEnlargedBackground omega θ) (u i)) =
      ⨆ i, sourceTestCurveAt ((Γ i).backgroundProjection omega).toSourceTestCurvePredata r := by
    have h := sourceIncreasing_iSup_tail
      (fun i => sourceTestCurveAt ((Γ i).backgroundProjection omega).toSourceTestCurvePredata r)
      (sourceTestCurveSup_extension_monotone omega (fun i => (Γ i).backgroundProjection omega)
        (sourceTestCurveProjectedFamily_monotone omega Γ hm) r) i₀
    convert h using 1
    apply iSup_congr
    intro i
    rw [sourceTestCurveAt_of_lt ((Γ i.val).backgroundProjection omega).toSourceTestCurvePredata (ho i)]
    rfl
  have hid := sourceOrdinaryEnvelope_increasing_directed_eq omega
    (fun i : J => sourceThetaPSH_add_kahler omega ((Γ i.val).thetaPSH ⟨r,ho i⟩))
    (fun i => sourcePositiveMass_add_kahler omega ((Γ i.val).thetaPSH ⟨r,ho i⟩))
    hmono (C := 0) (fun i x => by
      simpa only [EReal.coe_zero, Pi.zero_apply] using (Γ i.val).le_zero ⟨r,ho i⟩ x)
  change sourceSingularityEnvelope (sourceTestCurveEnlargedBackground omega θ)
      (uscRegularization (⨆ i, sourceTestCurveAt (Γ i).toSourceTestCurvePredata r)) =
      uscRegularization (⨆ i, sourceTestCurveAt ((Γ i).backgroundProjection omega).toSourceTestCurvePredata r)
  rw [← hraw, ← hrawP]
  exact hid.symm

/-- ENTIRE actual original test curves satisfy projection/supremum compatibility. -/
theorem source_test_curve_increasingSup_projection_compatible {I : Type*} [Preorder I]
    [IsDirectedOrder I] [Nonempty I] (omega : KahlerBackground n M)
    (Γ : I → SourceTestCurve θ)
    (hm : ∀ i j, i ≤ j → SourceTestCurvePOrder (Γ i) (Γ j))
    (hbound : BddAbove (range fun i => (Γ i).max)) :
    (SourceTestCurve.increasingSup omega Γ hm hbound).backgroundProjection omega =
      SourceTestCurve.increasingSup omega (fun i => (Γ i).backgroundProjection omega)
        (sourceTestCurveProjectedFamily_monotone omega Γ hm)
        (sourceTestCurveProjectedFamily_bddAbove omega Γ hbound) := by
  apply SourceTestCurve.ext_of_max_potential
  · simp only [SourceTestCurve.backgroundProjection_max, SourceTestCurve.increasingSup_max]
    rfl
  · intro r hr _hs
    simp only [SourceTestCurve.increasingSup_potential]
    exact sourceTestCurveSupPotential_backgroundProjection omega Γ hm hr

end SGPT.PSH.VariableComplexAtlas
