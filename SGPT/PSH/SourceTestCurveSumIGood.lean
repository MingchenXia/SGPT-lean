import SGPT.PSH.SourceTestCurveSum
import SGPT.PSH.SourceIGoodOperations
import SGPT.PSH.SourceIModelTestCurves
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Actual spatial USC of the STRICT open sum family, with no claim of raw open equality. -/
def sourceTestCurveOpenSumUSC (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) (τ : ℝ) : M → EReal :=
  uscRegularization (fun x => ⨆ d : Ioo (τ-Δ.max) Γ.max,
    sourceTestCurveAt Γ d.1 x + sourceTestCurveAt Δ (τ-d.1) x)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- ONLY actual OPEN I-model slices are asserted I-good, with genuine produced positive mass. -/
theorem SourceTestCurve.iModel_openSlice_good (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : SourceTestCurveIsIModel Γ) (r : Iio Γ.max) :
    sourceIGood (n := n) (Γ.potential r) := by
  have hI : Γ.potential r = sourceIEnvelope θ (Γ.potential r) := by
    rw [sourceIEnvelope_eq_native θ _ (Γ.thetaPSH r)]
    exact (hΓ r).2
  exact ⟨θ, Γ.thetaPSH r, Γ.mass_positive omega r, (Γ.fixedPoint r).trans hI⟩

private def sumWeight (j : ℕ) : ℝ := 1 / ((j : ℝ)+2)

private theorem sumWeight_properties :
    (∀ j, 0 < sumWeight j ∧ sumWeight j < 1) ∧
      Tendsto sumWeight atTop (𝓝 (0 : ℝ)) := by
  constructor
  · intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor
    · dsimp [sumWeight]; positivity
    · dsimp [sumWeight]
      exact (div_lt_one (by positivity)).mpr (by linarith)
  · change Tendsto (fun j : ℕ => 1 / ((j : ℝ)+2)) atTop (𝓝 (0 : ℝ))
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, sumWeight, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using h

private theorem finite_affine_le_limit {A B D U : EReal}
    (hA : A ≠ ⊥ ∧ A ≠ ⊤) (hB : B ≠ ⊥ ∧ B ≠ ⊤) (hD : D ≠ ⊥ ∧ D ≠ ⊤)
    (h : ∀ j, A + (((1-sumWeight j : ℝ) : EReal)*B) +
      (((sumWeight j : ℝ) : EReal)*D) ≤ U) : A+B ≤ U := by
  cases hAe : A using EReal.rec with
  | bot => exact False.elim (hA.1 hAe)
  | top => exact False.elim (hA.2 hAe)
  | coe a =>
    cases hBe : B using EReal.rec with
    | bot => exact False.elim (hB.1 hBe)
    | top => exact False.elim (hB.2 hBe)
    | coe b =>
      cases hDe : D using EReal.rec with
      | bot => exact False.elim (hD.1 hDe)
      | top => exact False.elim (hD.2 hDe)
      | coe d =>
        have hlim : Tendsto (fun j => A + (((1-sumWeight j : ℝ) : EReal)*B) +
            (((sumWeight j : ℝ) : EReal)*D)) atTop (𝓝 (A+B)) := by
          rw [hAe, hBe, hDe]
          have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub sumWeight_properties.2).mul_const b
          have h2 := ((tendsto_const_nhds (x := a)).add h1).add
            (sumWeight_properties.2.mul_const d)
          have hr : Tendsto (fun j => a+(1-sumWeight j)*b+sumWeight j*d)
              atTop (𝓝 (a+b)) := by
            simpa only [sub_zero, one_mul, zero_mul, add_zero] using h2
          simpa only [EReal.coe_add, EReal.coe_mul] using EReal.tendsto_coe.mpr hr
        have hh : A+B ≤ U :=
          le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall h)
        simpa only [hAe, hBe] using hh

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem open_sum_thetaPSH (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {τ : ℝ} (hτ : τ < Γ.max+Δ.max) :
    (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+atlasClosedFormToNative σ))
      (sourceTestCurveOpenSumUSC Γ Δ τ) := by
  let J := Ioo (τ-Δ.max) Γ.max
  let : Nonempty J := ⟨⟨((τ-Δ.max)+Γ.max)/2, by constructor <;> linarith⟩⟩
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ+atlasClosedFormToNative σ)
  have hF (d : J) : (ofFixedModel n M).IsThetaPSH T
      (fun x => sourceTestCurveAt Γ d.1 x+sourceTestCurveAt Δ (τ-d.1) x) := by
    have hd : d.1 < Γ.max := d.2.2
    have hs : τ-d.1 < Δ.max := by have hh := d.2.1; linarith
    rw [sourceTestCurveAt_of_lt Γ hd, sourceTestCurveAt_of_lt Δ hs]
    exact sourceIndependentSum_thetaPSH (Γ.thetaPSH _) (Δ.thetaPSH _)
  let w : J → SourceThetaPotentialL1 T := fun d => ⟨_, hF d⟩
  have h := sourceIncreasingSingularitySupremum_thetaPSH T w (C := 0)
    (fun d x => add_nonpos (Γ.at_le_zero d.1 x) (Δ.at_le_zero (τ-d.1) x))
  have he : (⨆ d : J, (w d).val) =
      fun x => ⨆ d : J, sourceTestCurveAt Γ d.1 x+sourceTestCurveAt Δ (τ-d.1) x := by
    funext x
    simp only [iSup_apply, w]
  rw [he] at h
  exact h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem at_open_chord (Γ : SourceTestCurvePredata θ) (a b : ℝ)
    (ha : a < Γ.max) (hb : b < Γ.max) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (x : M) :
    ((t : EReal)*sourceTestCurveAt Γ a x) +
      (((1-t : ℝ) : EReal)*sourceTestCurveAt Γ b x) ≤
      sourceTestCurveAt Γ (t*a+(1-t)*b) x := by
  have hc : t*a+(1-t)*b < Γ.max := by
    nlinarith [mul_pos ht (sub_pos.mpr ha), mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hb)]
  rw [sourceTestCurveAt_of_lt Γ ha, sourceTestCurveAt_of_lt Γ hb,
    sourceTestCurveAt_of_lt Γ hc]
  exact Γ.convexComb_le ⟨a,ha⟩ ⟨b,hb⟩ ht ht1 x

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem right_endpoint_le (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {τ : ℝ} (hτ : τ < Γ.max+Δ.max) (x : M)
    (hΓ : ∀ r ≤ Γ.max, sourceTestCurveAt Γ r x ≠ ⊥ ∧ sourceTestCurveAt Γ r x ≠ ⊤)
    (hΔ : ∀ r ≤ Δ.max, sourceTestCurveAt Δ r x ≠ ⊥ ∧ sourceTestCurveAt Δ r x ≠ ⊤)
    (U : EReal)
    (hopen : ∀ d ∈ Ioo (τ-Δ.max) Γ.max,
      sourceTestCurveAt Γ d x+sourceTestCurveAt Δ (τ-d) x ≤ U) :
    sourceTestCurveAt Γ Γ.max x+sourceTestCurveAt Δ (τ-Γ.max) x ≤ U := by
  let d₀ := ((τ-Δ.max)+Γ.max)/2
  have hd₀ : d₀ ∈ Ioo (τ-Δ.max) Γ.max := by dsimp [d₀]; constructor <;> linarith
  have hs₀ : τ-Γ.max < Δ.max := by linarith
  have hs₁ : τ-d₀ < Δ.max := by linarith [hd₀.1]
  apply finite_affine_le_limit (hΓ _ le_rfl) (hΔ _ hs₀.le) (hΔ _ hs₁.le)
  intro j
  have he := sumWeight_properties.1 j
  let d := (1-sumWeight j)*Γ.max+sumWeight j*d₀
  have hd : d ∈ Ioo (τ-Δ.max) Γ.max := by
    dsimp [d]
    constructor <;> nlinarith [hd₀.1, hd₀.2]
  have hg : sourceTestCurveAt Γ Γ.max x ≤ sourceTestCurveAt Γ d x :=
    Γ.at_antitone x hd.2.le
  have hh := at_open_chord Δ (τ-Γ.max) (τ-d₀) hs₀ hs₁
    (sub_pos.mpr he.2) (by linarith : 1-sumWeight j < 1) x
  have heq : (1-sumWeight j)*(τ-Γ.max)+(1-(1-sumWeight j))*(τ-d₀) = τ-d := by
    dsimp [d]; ring
  rw [heq] at hh
  have hcancel : 1-(1-sumWeight j) = sumWeight j := by ring
  rw [hcancel] at hh
  have hh' := (add_le_add hg hh).trans (hopen d hd)
  simpa only [add_assoc] using hh'

omit [MeasurableSpace M] [BorelSpace M] in
/-- Strictly below the sum cutoff, the literal ALL-real raw supremum is the
USC-regularized OPEN supremum. No goodness at either cutoff is assumed. -/
theorem sourceTestCurveRawSum_eq_uscSup_open (Γ : SourceTestCurvePredata θ)
    (Δ : SourceTestCurvePredata σ) {τ : ℝ} (hτ : τ < Γ.max+Δ.max) :
    sourceTestCurveRawSum Γ Δ τ = sourceTestCurveOpenSumUSC Γ Δ τ := by
  have hR := sourceTestCurveRawSum_thetaPSH Γ Δ hτ.le
  have hU := open_sum_thetaPSH Γ Δ hτ
  apply le_antisymm
  · apply (sourceQuasiEverywhere_le_iff hR hU).mp
    apply (sourceQuasiEverywhere_iff_native _).mpr
    have hΓqe := quasiPsh_finite_quasiEverywhere
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.cutoff_thetaPSH).quasiPshPotential
    have hΔqe := quasiPsh_finite_quasiEverywhere
      ((isThetaPSH_iff_nativeThetaPotential σ _).mp Δ.cutoff_thetaPSH).quasiPshPotential
    apply (quasiEverywhere_and hΓqe hΔqe).mono
    intro x hx
    have hΓfin : ∀ r ≤ Γ.max,
        sourceTestCurveAt Γ r x ≠ ⊥ ∧ sourceTestCurveAt Γ r x ≠ ⊤ := by
      intro r hr
      have hl : sourceTestCurveCutoff Γ x ≤ sourceTestCurveAt Γ r x := by
        simpa only [sourceTestCurveAt_eq_max] using Γ.at_antitone x hr
      exact ⟨ne_bot_of_le_ne_bot hx.1.1 hl,
        ne_of_lt ((Γ.at_le_zero r x).trans_lt (by simp))⟩
    have hΔfin : ∀ r ≤ Δ.max,
        sourceTestCurveAt Δ r x ≠ ⊥ ∧ sourceTestCurveAt Δ r x ≠ ⊤ := by
      intro r hr
      have hl : sourceTestCurveCutoff Δ x ≤ sourceTestCurveAt Δ r x := by
        simpa only [sourceTestCurveAt_eq_max] using Δ.at_antitone x hr
      exact ⟨ne_bot_of_le_ne_bot hx.2.1 hl,
        ne_of_lt ((Δ.at_le_zero r x).trans_lt (by simp))⟩
    have hopen : ∀ d ∈ Ioo (τ-Δ.max) Γ.max,
        sourceTestCurveAt Γ d x+sourceTestCurveAt Δ (τ-d) x ≤
          sourceTestCurveOpenSumUSC Γ Δ τ x := by
      intro d hd
      exact (le_iSup (fun d : Ioo (τ-Δ.max) Γ.max =>
        sourceTestCurveAt Γ d.1 x+sourceTestCurveAt Δ (τ-d.1) x) ⟨d,hd⟩).trans
          (le_uscRegularization (fun y => ⨆ d : Ioo (τ-Δ.max) Γ.max,
            sourceTestCurveAt Γ d.1 y+sourceTestCurveAt Δ (τ-d.1) y) x)
    have hright := right_endpoint_le Γ Δ hτ x hΓfin hΔfin _ hopen
    have hleft := right_endpoint_le Δ Γ (by linarith : τ < Δ.max+Γ.max)
      x hΔfin hΓfin (sourceTestCurveOpenSumUSC Γ Δ τ x) (by
        intro d hd
        have hr : τ-d ∈ Ioo (τ-Δ.max) Γ.max := by constructor <;> linarith [hd.1,hd.2]
        have h := hopen (τ-d) hr
        have he : τ-(τ-d)=d := by ring
        rw [he] at h
        simpa only [add_comm] using h)
    change (⨆ d : ℝ, sourceTestCurveAt Γ d x+sourceTestCurveAt Δ (τ-d) x) ≤ _
    apply iSup_le
    intro d
    by_cases hdleft : d < τ-Δ.max
    · simp only [sourceTestCurveAt_of_gt Δ (by linarith : Δ.max < τ-d), Pi.bot_apply, EReal.add_bot]
      exact bot_le
    by_cases hdright : Γ.max < d
    · simp only [sourceTestCurveAt_of_gt Γ hdright, Pi.bot_apply, EReal.bot_add]
      exact bot_le
    by_cases heleft : d = τ-Δ.max
    · subst d
      have he : τ-(τ-Δ.max)=Δ.max := by ring
      rw [he]
      simpa only [add_comm] using hleft
    by_cases heright : d = Γ.max
    · subst d
      exact hright
    exact hopen d ⟨lt_of_le_of_ne (not_lt.mp hdleft) (Ne.symm heleft),
      lt_of_le_of_ne (not_lt.mp hdright) heright⟩
  · apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential _ _).mp hR).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro d
    exact le_iSup (fun d : ℝ => sourceTestCurveAt Γ d x+sourceTestCurveAt Δ (τ-d) x) d.1

/-- Actual raw I-goodness is recovered only at strict subcutoffs. -/
theorem sourceTestCurveRawSum_iGood (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ)
    (hΓ : SourceTestCurveIsIModel Γ) (hΔ : SourceTestCurveIsIModel Δ)
    {τ : ℝ} (hτ : τ < Γ.max+Δ.max) :
    sourceIGood (n := n)
      (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ) := by
  let J := Ioo (τ-Δ.max) Γ.max
  let : Nonempty J := ⟨⟨((τ-Δ.max)+Γ.max)/2,by constructor <;> linarith⟩⟩
  let T := nativeClosedFormToAtlas (atlasClosedFormToNative θ+atlasClosedFormToNative σ)
  let u : J → M → EReal := fun d x =>
    sourceTestCurveAt Γ.toSourceTestCurvePredata d.1 x+
      sourceTestCurveAt Δ.toSourceTestCurvePredata (τ-d.1) x
  have hpsh (d : J) : (ofFixedModel n M).IsThetaPSH T (u d) := by
    have hs : τ-d.1 < Δ.max := by have hh := d.2.1; linarith
    dsimp [u]
    rw [sourceTestCurveAt_of_lt _ d.2.2,sourceTestCurveAt_of_lt _ hs]
    exact sourceIndependentSum_thetaPSH (Γ.thetaPSH _) (Δ.thetaPSH _)
  have hgood (d : J) : sourceIGood (n := n) (u d) := by
    have hs : τ-d.1 < Δ.max := by have hh := d.2.1; linarith
    dsimp [u]
    rw [sourceTestCurveAt_of_lt _ d.2.2,sourceTestCurveAt_of_lt _ hs]
    exact sourceIGood_add omega (Γ.iModel_openSlice_good omega hΓ ⟨d.1,d.2.2⟩)
      (Δ.iModel_openSlice_good omega hΔ ⟨τ-d.1,hs⟩)
  have hb : FirstPass.LocallyUniformlyBoundedAbove (range u) univ := by
    intro x hx
    refine ⟨univ,Filter.univ_mem,0,?_⟩
    rintro f ⟨d,rfl⟩ y hy
    exact add_nonpos (Γ.at_le_zero d.1 y) (Δ.at_le_zero (τ-d.1) y)
  have h := sourceIGood_uscSup omega u hpsh hgood hb
  have he : (⨆ d : J,u d) = fun x => ⨆ d : J,
      sourceTestCurveAt Γ.toSourceTestCurvePredata d.1 x+
        sourceTestCurveAt Δ.toSourceTestCurvePredata (τ-d.1) x := by
    funext x
    simp only [iSup_apply,u]
  rw [he] at h
  rw [sourceTestCurveRawSum_eq_uscSup_open _ _ hτ]
  exact h

/-- WHOLE original sum lemma: actual positive sum, genuine raw PSH, and the
literal same raw function I-good for inputs in the original I-model unions. -/
theorem source_test_curve_sum_whole (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (Δ : SourceTestCurve σ) :
    SourceTestCurve.sum omega Γ Δ ∈ SourceTestCurvesPositive
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+atlasClosedFormToNative σ)) ∧
    (∀ τ < Γ.max+Δ.max, (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ+atlasClosedFormToNative σ))
      (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) ∧
    (Γ ∈ SourceIModelTestCurvesPositive θ → Δ ∈ SourceIModelTestCurvesPositive σ →
      ∀ τ < Γ.max+Δ.max, sourceIGood (n := n)
        (sourceTestCurveRawSum Γ.toSourceTestCurvePredata Δ.toSourceTestCurvePredata τ)) := by
  refine ⟨SourceTestCurve.sum_mem_positive omega Γ Δ,?_,?_⟩
  · intro τ hτ
    exact sourceTestCurveRawSum_thetaPSH _ _ hτ.le
  · intro hΓ hΔ τ hτ
    exact sourceTestCurveRawSum_iGood omega Γ Δ
      ((sourceIModelTestCurvesPositive_iff_slices omega Γ).mp hΓ)
      ((sourceIModelTestCurvesPositive_iff_slices omega Δ).mp hΔ) hτ

end SGPT.PSH.VariableComplexAtlas
