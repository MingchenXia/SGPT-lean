import SGPT.PSH.SourceTestCurveFiniteEnergyRegularization
import SGPT.Envelopes.SourceDecreasingOrdinaryFixedPoints
import SGPT.Foundations.Analysis.Pending.ActualIndependentConvexMassPolynomial
import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelMixedMass
import SGPT.Foundations.Analysis.Pending.EqualMassEnvelope
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- The closed coefficient of the SAME original two-branch input. -/
def sourceRegularizationCoefficient (ε r : ℝ) : ℝ := max 0 (1 + ε * r)

/-- Canonical positive sequence of original regularization parameters. -/
def sourceRegularizationParameter (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem convexComb_coefficient_order {u v : M → EReal}
    (huv : u ≤ v) (hv0 : v ≤ 0) {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) (ha : a < 1) :
    convexComb a u v ≤ convexComb b u v := by
  intro x
  have ha0 : 0 ≤ a := hb.trans hba
  cases hv : v x using EReal.rec with
  | top => exact False.elim (not_le_of_gt (EReal.coe_lt_top 0) (by simpa [hv] using hv0 x))
  | bot =>
    simp only [convexComb, hv, EReal.coe_mul_bot_of_pos (sub_pos.mpr ha), EReal.add_bot]
    exact bot_le
  | coe q =>
    cases hu : u x using EReal.rec with
    | top => exact False.elim (not_le_of_gt (EReal.coe_lt_top q) (by simpa only [hu, hv] using huv x))
    | bot =>
      by_cases haeq : a = 0
      · have hbeq : b = 0 := le_antisymm (haeq ▸ hba) hb
        rw [haeq, hbeq]
      · simp only [convexComb, hu, EReal.coe_mul_bot_of_pos (lt_of_le_of_ne ha0 (Ne.symm haeq)), EReal.bot_add]
        exact bot_le
    | coe p =>
      have hpq : p ≤ q := EReal.coe_le_coe_iff.mp (by simpa only [hu, hv] using huv x)
      simp only [convexComb, hu, hv, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hpq)]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal input dictionary, including the original constant branch and poles. -/
theorem sourceTestCurveRegularizationInput_eq_closed
    (Γ : SourceTestCurve θ) {ε r : ℝ} (hε : 0 < ε) (_hr : r < 0) :
    sourceTestCurveRegularizationInput Γ φ ε r =
      convexComb (sourceRegularizationCoefficient ε r)
        (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ := by
  have hi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  by_cases h : r ≤ -ε⁻¹
  · have hc : 1 + ε * r ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hε.le (sub_nonpos.mpr h)]
    simp only [sourceTestCurveRegularizationInput, if_pos h, sourceRegularizationCoefficient, max_eq_left hc]
    funext x
    simp [convexComb]
  · have hc : 0 < 1 + ε * r := by nlinarith [mul_pos hε (sub_pos.mpr (lt_of_not_ge h))]
    simp only [sourceTestCurveRegularizationInput, if_neg h, sourceRegularizationCoefficient, max_eq_right hc.le]

omit [BorelSpace M] [ConnectedSpace M] in
/-- Positive epsilon order produces the actual input order before enveloping. -/
theorem sourceTestCurveRegularizationInput_mono_parameter
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε δ r : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hr : r < 0) :
    sourceTestCurveRegularizationInput Γ φ ε r ≤ sourceTestCurveRegularizationInput Γ φ δ r := by
  have hδ : 0 < δ := hε.trans_le hεδ
  rw [sourceTestCurveRegularizationInput_eq_closed Γ hε hr,
    sourceTestCurveRegularizationInput_eq_closed Γ hδ hr]
  have hb := sourceTestCurveRegularizationInput_bounds Γ hΓ hε hr
  apply convexComb_coefficient_order (Γ.toSourceTestCurvePredata.at_le_limit r |>.trans_eq hΓ) hb.2.2
  · exact le_max_left _ _
  · exact max_le_max le_rfl (by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hεδ) hr.le])
  · exact max_lt (by norm_num) (by nlinarith [mul_neg_of_pos_of_neg hε hr])

omit [BorelSpace M] [ConnectedSpace M] in
/-- Monotonicity is for the ACTUAL ordinary envelopes, with no limit premise. -/
theorem sourceTestCurveRegularizationFamily_mono_parameter
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε δ r : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hr : r < 0) :
    sourceTestCurveRegularizationFamily Γ φ ε r ≤ sourceTestCurveRegularizationFamily Γ φ δ r :=
  sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ =>
    sourceTestCurveRegularizationInput_mono_parameter Γ hΓ hε hεδ hr x)

/-- Every canonical parameter is genuinely positive. -/
theorem sourceRegularizationParameter_pos (k : ℕ) : 0 < sourceRegularizationParameter k := by
  unfold sourceRegularizationParameter
  positivity

/-- The canonical parameters decrease to zero from the positive side. -/
theorem sourceRegularizationParameter_antitone : Antitone sourceRegularizationParameter := by
  intro i j hij
  unfold sourceRegularizationParameter
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)

/-- Actual closed coefficients approach one; no potential readback is used. -/
theorem sourceRegularizationCoefficient_tendsto (r : ℝ) :
    Tendsto (fun k => sourceRegularizationCoefficient (sourceRegularizationParameter k) r)
      atTop (𝓝 1) := by
  have he : Tendsto sourceRegularizationParameter atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x := (0 : ℝ))).max ((tendsto_const_nhds (x := (1 : ℝ))).add (he.mul_const r))
  simpa only [sourceRegularizationCoefficient, zero_mul, add_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using h

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal ordinary-envelope sequence is pointwise decreasing. -/
theorem sourceTestCurveRegularizationFamily_antitone_sequence
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {r : ℝ} (hr : r < 0) :
    Antitone (fun k => sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r) := by
  intro i j hij
  exact sourceTestCurveRegularizationFamily_mono_parameter Γ hΓ
    (sourceRegularizationParameter_pos j) (sourceRegularizationParameter_antitone hij) hr

omit [ConnectedSpace M] in
private theorem actual_mass_ne_top (omega : KahlerBackground n M)
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourcePotentialNonPluripolarMeasure θ u hu univ ≠ ⊤ := by
  exact ne_of_lt (by simpa only [sourceMixedNonPluripolarMass_diagonal] using
    sourceMixedNonPluripolarMass_lt_top omega (fun _ => θ) (fun _ => u) (fun _ => hu))

omit [ConnectedSpace M] in
private theorem actual_convex_mass_polynomial (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) :
    ∃ p : Polynomial ℝ, ∀ (a : ℝ) (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1),
      ∀ hc : (ofFixedModel n M).IsThetaPSH θ (convexComb a u v),
      (sourcePotentialNonPluripolarMeasure θ (convexComb a u v) hc univ).toReal = p.eval a := by
  let hnu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  let hnv := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  refine ⟨ActualIndependentConvexMassPolynomial.convexMixedMassPolynomial
    (fun _ => atlasClosedFormToNative θ) (fun _ => u) (fun _ => v)
    (fun _ => hnu) (fun _ => hnv), ?_⟩
  intro a ha0 ha1 hc
  exact ActualIndependentConvexMassPolynomial.globalMixedMass_convexComb_toReal_eq_eval
    omega (fun _ => hnu) (fun _ => hnv) ha0 ha1

omit [ConnectedSpace M] in
private theorem actual_closed_convex_mass_tendsto (omega : KahlerBackground n M)
    {u v : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (hc : ∀ k, (ofFixedModel n M).IsThetaPSH θ (convexComb (a k) u v))
    (hlim : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => (sourcePotentialNonPluripolarMeasure θ
      (convexComb (a k) u v) (hc k) univ).toReal) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal) := by
  have _huFinite := actual_mass_ne_top omega hu
  have _hcFinite (k : ℕ) := actual_mass_ne_top omega (hc k)
  obtain ⟨p, hp⟩ := actual_convex_mass_polynomial omega hu hv
  have h1 : convexComb 1 u v = u := by funext x; simp [convexComb]
  have hp1 : p.eval 1 = (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal := by
    have hh := hp 1 (by norm_num) le_rfl (h1.symm ▸ hu)
    simpa only [h1] using hh.symm
  have ht := p.continuous.continuousAt.tendsto.comp hlim
  change Tendsto (fun k => p.eval (a k)) atTop (𝓝 (p.eval 1)) at ht
  have heq := funext (fun k => hp (a k) (ha0 k) (ha1 k) (hc k))
  rw [heq, ← hp1]
  exact ht

omit [ConnectedSpace M] in
private theorem original_negative_model (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hmax : Γ.max = 0) {r : ℝ} (hr : r < 0) :
    SourceModelPotential θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r) := by
  have h : r < Γ.max := by rwa [hmax]
  rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata h]
  exact Γ.slice_model omega ⟨r, h⟩

/-- Actual regularized slice masses converge in real readback, with finite
actual masses and genuine input PSH established before the polynomial formula. -/
theorem sourceTestCurveRegularizationFamily_realMass_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {r : ℝ} (hr : r < 0) :
    Tendsto (fun k => (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r)
      (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax
        (sourceRegularizationParameter_pos k) hr).thetaPSH univ).toReal) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r)
        (original_negative_model omega Γ hmax hr).thetaPSH univ).toReal) := by
  let a := fun k => sourceRegularizationCoefficient (sourceRegularizationParameter k) r
  have ha0 (k : ℕ) : 0 ≤ a k := le_max_left _ _
  have ha1 (k : ℕ) : a k ≤ 1 := max_le (by norm_num) (by
    have h := mul_neg_of_pos_of_neg (sourceRegularizationParameter_pos k) hr
    change 1 + sourceRegularizationParameter k * r ≤ 1
    linarith)
  have hc (k : ℕ) : (ofFixedModel n M).IsThetaPSH θ
      (convexComb (a k) (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ) := by
    rw [← sourceTestCurveRegularizationInput_eq_closed Γ (sourceRegularizationParameter_pos k) hr]
    exact sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax (sourceRegularizationParameter_pos k) hr
  have hlim := actual_closed_convex_mass_tendsto omega
    (original_negative_model omega Γ hmax hr).thetaPSH hφ.thetaPSH
    a ha0 ha1 hc (sourceRegularizationCoefficient_tendsto r)
  have heq (k : ℕ) : sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r)
      (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax
        (sourceRegularizationParameter_pos k) hr).thetaPSH univ =
      sourcePotentialNonPluripolarMeasure θ
        (convexComb (a k) (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ) (hc k) univ := by
    have h := sourceOrdinaryEnvelope_diagonalMass_eq omega
      (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax (sourceRegularizationParameter_pos k) hr)
    simpa only [sourceTestCurveRegularizationFamily,
      sourceTestCurveRegularizationInput_eq_closed Γ (sourceRegularizationParameter_pos k) hr] using h
  simpa only [heq] using hlim

/-- The SAME actual extended masses converge, not just their real encodings. -/
theorem sourceTestCurveRegularizationFamily_mass_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {r : ℝ} (hr : r < 0) :
    Tendsto (fun k => sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r)
      (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax
        (sourceRegularizationParameter_pos k) hr).thetaPSH univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r)
        (original_negative_model omega Γ hmax hr).thetaPSH univ)) := by
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (sourceTestCurveRegularizationFamily_realMass_tendsto omega Γ hΓ hmax hr)
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (actual_mass_ne_top omega _)] using ht

/-- Positive actual models and equal ACTUAL mass identify the literal infimum
with the original slice, retaining all extended-real poles. -/
theorem sourceTestCurveRegularizationFamily_iInf (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {r : ℝ} (hr : r < 0) :
    (fun x => ⨅ k, sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r x) =
      sourceTestCurveAt Γ.toSourceTestCurvePredata r := by
  let u := fun k => sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r
  let hu := fun k => sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax
    (sourceRegularizationParameter_pos k) hr
  have hanti : Antitone u := sourceTestCurveRegularizationFamily_antitone_sequence Γ hΓ hr
  let v := fun x => ⨅ k, u k x
  have hv : (ofFixedModel n M).IsThetaPSH θ v :=
    sourceOrdinaryFixedPoint_directedInf_thetaPSH u (fun k => (hu k).thetaPSH)
      (fun k => (hu k).choose_spec.1.symm) (fun x i j hij => hanti hij x)
  have hγ := original_negative_model omega Γ hmax hr
  have hlo : sourceTestCurveAt Γ.toSourceTestCurvePredata r ≤ v := by
    intro x
    exact le_iInf fun k => (sourceTestCurveRegularizationFamily_bounds Γ hΓ hmax
      (sourceRegularizationParameter_pos k) hr).1 x
  have hv0 : v ≤ 0 := by
    have hφ0 := (sourceTestCurveRegularizationInput_bounds Γ hΓ
      (sourceRegularizationParameter_pos 0) hr).2.2
    intro x
    exact (iInf_le (fun k => u k x) 0).trans
      (((sourceTestCurveRegularizationFamily_bounds Γ hΓ hmax
        (sourceRegularizationParameter_pos 0) hr).2 x).trans (hφ0 x))
  have hpos : 0 < sourcePotentialNonPluripolarMeasure θ v hv univ :=
    hγ.choose_spec.2.trans_le (sourcePotentialNonPluripolarMass_mono omega hγ.thetaPSH hv
      (MoreSingularOn.of_le fun x _ => hlo x))
  have hlim (x : M) : Tendsto (fun k => u k x) atTop (𝓝 (v x)) :=
    tendsto_atTop_iInf (fun i j hij => hanti hij x)
  have hmass := ActualDecreasingModelMixedMass.tendsto_diagonalPotentialMass_of_antitone_model
    omega (atlasClosedFormToNative θ) u (fun k => (hu k).toNative) hanti
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hpos hlim
  have heq : sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveAt Γ.toSourceTestCurvePredata r) hγ.thetaPSH univ =
      sourcePotentialNonPluripolarMeasure θ v hv univ :=
    tendsto_nhds_unique (sourceTestCurveRegularizationFamily_mass_tendsto omega Γ hΓ hmax hr) hmass
  have hrigid := equalMassLeSingularityEnvelope omega (atlasClosedFormToNative θ)
    (sourceTestCurveAt Γ.toSourceTestCurvePredata r) v hγ.toNative.plurisubharmonic
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hγ.toNative.positive_mass hv0
    (MoreSingularOn.of_le fun x _ => hlo x) heq
  have hup : v ≤ sourceTestCurveAt Γ.toSourceTestCurvePredata r := by
    simpa only [← sourceSingularityEnvelope_eq_native, ← hγ.choose_spec.1] using hrigid
  exact le_antisymm hup hlo

/-- EVERY point of the SAME actual slice converges, including all poles. -/
theorem sourceTestCurveRegularizationFamily_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {r : ℝ} (hr : r < 0) (x : M) :
    Tendsto (fun k => sourceTestCurveRegularizationFamily Γ φ (sourceRegularizationParameter k) r x)
      atTop (𝓝 (sourceTestCurveAt Γ.toSourceTestCurvePredata r x)) := by
  have ht := tendsto_atTop_iInf (fun i j hij =>
    sourceTestCurveRegularizationFamily_antitone_sequence Γ hΓ hr hij x)
  have heq := congrFun (sourceTestCurveRegularizationFamily_iInf omega Γ hΓ hmax hr) x
  simpa only [heq] using ht

end SGPT.PSH.VariableComplexAtlas
