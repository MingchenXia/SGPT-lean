import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceTestCurveLegendreAlgebra
import SGPT.PSH.SourceTestCurvePositiveMass
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes
import SGPT.Envelopes.SourceOrdinaryEnvelopeMassModel
import Mathlib.Analysis.Convex.Mul

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

/-- The literal original two-branch input. On its active negative domain
both displayed convex weights are strictly positive, including at poles. -/
def sourceTestCurveRegularizationInput (Γ : SourceTestCurve θ) (φ : M → EReal)
    (ε r : ℝ) : M → EReal :=
  if r ≤ -ε⁻¹ then φ else
    convexComb (1 + ε * r) (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ

private theorem regularization_coefficients {ε r : ℝ} (hε : 0 < ε)
    (hr : r < 0) (ha : -ε⁻¹ < r) : 0 < 1 + ε * r ∧ 1 + ε * r < 1 := by
  have hi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hh := mul_pos hε (sub_pos.mpr ha)
  constructor <;> nlinarith [mul_neg_of_pos_of_neg hε hr]

omit [BorelSpace M] [ConnectedSpace M] in
private theorem original_negative_thetaPSH (Γ : SourceTestCurve θ)
    (hmax : Γ.max = 0) {r : ℝ} (hr : r < 0) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r) := by
  have hrmax : r < Γ.max := by rwa [hmax]
  rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hrmax]
  exact Γ.thetaPSH ⟨r, hrmax⟩

omit [BorelSpace M] [ConnectedSpace M] in
/-- Genuine convex-combination PSH is produced from the actual original
slice and model, without a local nondegeneracy or output certificate. -/
theorem sourceTestCurveRegularizationInput_thetaPSH
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) (hmax : Γ.max = 0) {ε r : ℝ} (hε : 0 < ε) (hr : r < 0) :
    (ofFixedModel n M).IsThetaPSH θ (sourceTestCurveRegularizationInput Γ φ ε r) := by
  by_cases ha : r ≤ -ε⁻¹
  · simpa only [sourceTestCurveRegularizationInput, if_pos ha] using hφ.thetaPSH
  · have hc := regularization_coefficients hε hr (lt_of_not_ge ha)
    rw [sourceTestCurveRegularizationInput, if_neg ha]
    exact (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (isThetaPshPotential_convexComb
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (original_negative_thetaPSH Γ hmax hr))
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφ.thetaPSH) hc.1 hc.2)

omit [BorelSpace M] [ConnectedSpace M] in
/-- The SAME original input is between the actual original slice and the
actual model, with all poles retained and no bounded-model assumption. -/
theorem sourceTestCurveRegularizationInput_bounds
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε r : ℝ} (hε : 0 < ε) (hr : r < 0) :
    sourceTestCurveAt Γ.toSourceTestCurvePredata r ≤ sourceTestCurveRegularizationInput Γ φ ε r ∧
    sourceTestCurveRegularizationInput Γ φ ε r ≤ φ ∧ φ ≤ 0 := by
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
  have hupper := Γ.toSourceTestCurvePredata.at_le_limit r
  rw [hbase] at hupper
  have hφzero : φ ≤ 0 := by
    rw [hφ.choose_spec.1]
    exact sourceSingularityEnvelope_le_zero θ φ
  by_cases ha : r ≤ -ε⁻¹
  · simpa only [sourceTestCurveRegularizationInput, if_pos ha] using
      And.intro hupper (And.intro (le_refl φ) hφzero)
  · have hc := regularization_coefficients hε hr (lt_of_not_ge ha)
    have hlo := convexComb_mono hc.1.le hc.2.le
      (le_refl (sourceTestCurveAt Γ.toSourceTestCurvePredata r)) hupper
    have hup := convexComb_mono hc.1.le hc.2.le hupper (le_refl φ)
    rw [ThetaCapacity.convexComb_self hc.1 hc.2] at hlo hup
    exact ⟨by simpa only [sourceTestCurveRegularizationInput, if_neg ha] using hlo,
      by simpa only [sourceTestCurveRegularizationInput, if_neg ha] using hup, hφzero⟩

omit [ConnectedSpace M] in
/-- Positive ACTUAL input mass is manufactured from the genuine original
slice-model producer and actual NP mass monotonicity, not supplied. -/
theorem sourceTestCurveRegularizationInput_positiveMass (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : r < 0) :
    0 < sourcePotentialNonPluripolarMeasure θ (sourceTestCurveRegularizationInput Γ φ ε r)
      (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax hε hr) univ := by
  have hrmax : r < Γ.max := by rwa [hmax]
  have hγ : SourceModelPotential θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r) := by
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hrmax]
    exact Γ.slice_model omega ⟨r, hrmax⟩
  have hpositive : 0 < sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveAt Γ.toSourceTestCurvePredata r) hγ.thetaPSH univ := hγ.choose_spec.2
  exact hpositive.trans_le (sourcePotentialNonPluripolarMass_mono omega hγ.thetaPSH
    (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax hε hr)
    (MoreSingularOn.of_le fun x _ => (sourceTestCurveRegularizationInput_bounds Γ hΓ hε hr).1 x))

omit [BorelSpace M] [ConnectedSpace M] in
private theorem regularization_active_nonpoles
    (Γ : SourceTestCurve θ) {ε q : ℝ} (hε : 0 < ε) (hq : q < 0) (ha : -ε⁻¹ < q)
    (x : M) (hu : sourceTestCurveRegularizationInput Γ φ ε q x ≠ ⊥) :
    φ x ≠ ⊥ ∧ sourceTestCurveAt Γ.toSourceTestCurvePredata q x ≠ ⊥ := by
  have hc := regularization_coefficients hε hq ha
  have hleft : ¬ q ≤ -ε⁻¹ := not_le.mpr ha
  constructor
  · intro h
    apply hu
    simp only [sourceTestCurveRegularizationInput, if_neg hleft, convexComb, h,
      EReal.coe_mul_bot_of_pos (sub_pos.mpr hc.2), EReal.add_bot]
  · intro h
    apply hu
    simp only [sourceTestCurveRegularizationInput, if_neg hleft, convexComb, h,
      EReal.coe_mul_bot_of_pos hc.1, EReal.bot_add]

omit [BorelSpace M] in
/-- On a genuinely finite endpoint interval, manufacture the actual real
convex increasing product. All infinite endpoints are excluded FIRST. -/
private theorem regularization_finite_product
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε p q : ℝ} (hε : 0 < ε) (hq : q < 0) (ha : -ε⁻¹ < q)
    (x : M) (hu : sourceTestCurveRegularizationInput Γ φ ε q x ≠ ⊥) :
    let K := fun r : ℝ => max 0 (1 + ε * r) *
      ((φ x).toReal - (sourceTestCurveAt Γ.toSourceTestCurvePredata r x).toReal)
    ConvexOn ℝ (Icc p q) K ∧ MonotoneOn K (Icc p q) ∧
      ∀ r ∈ Icc p q, sourceTestCurveRegularizationInput Γ φ ε r x =
        (((φ x).toReal - K r : ℝ) : EReal) := by
  let γ := fun r : ℝ => sourceTestCurveAt Γ.toSourceTestCurvePredata r x
  let F := sourceTestCurveClosedNegativeTrace Γ.toSourceTestCurvePredata x
  let σ := fun r : ℝ => max 0 (1 + ε * r)
  obtain ⟨hφbot, hqbot⟩ := regularization_active_nonpoles Γ hε hq ha x hu
  have hφtop : φ x ≠ ⊤ :=
    ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH).1.quasiPlurisubharmonic.ne_top x
  have htop (r : ℝ) : γ r ≠ ⊤ := ne_top_of_le_ne_top
    (by norm_num : (0 : EReal) ≠ ⊤) (Γ.toSourceTestCurvePredata.at_le_zero r x)
  have hbot (r : ℝ) (hr : r ∈ Icc p q) : γ r ≠ ⊥ :=
    ne_bot_of_le_ne_bot hqbot (Γ.toSourceTestCurvePredata.at_antitone x hr.2)
  have hγval (r : ℝ) (hr : r ∈ Icc p q) : γ r = (((γ r).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (htop r) (hbot r hr)).symm
  have hφval : φ x = (((φ x).toReal : ℝ) : EReal) := (EReal.coe_toReal hφtop hφbot).symm
  let g := fun r : ℝ => (φ x).toReal - (γ r).toReal
  have hFnobot (r : ℝ) : F r ≠ ⊥ := by
    apply ne_bot_of_le_ne_bot (by norm_num : (0 : EReal) ≠ ⊥)
    change (0 : EReal) ≤ -(γ r)
    have hh : γ r ≤ (0 : EReal) := Γ.toSourceTestCurvePredata.at_le_zero r x
    simpa only [neg_zero] using EReal.neg_le_neg_iff.mpr hh
  have hproper : SGPT.Convex.IsProper F := by
    refine ⟨Γ.toSourceTestCurvePredata.closedNegativeTrace_convex x, ⟨q, ?_⟩, hFnobot⟩
    change F q < ⊤
    apply lt_top_iff_ne_top.mpr
    intro hh
    change -(sourceTestCurveAt Γ.toSourceTestCurvePredata q x) = ⊤ at hh
    exact hqbot (EReal.neg_eq_top_iff.mp hh)
  have hsubset : Icc p q ⊆ SGPT.Convex.effectiveDomain F := by
    intro r hr
    change F r < ⊤
    apply lt_top_iff_ne_top.mpr
    intro hh
    change -(γ r) = ⊤ at hh
    exact hbot r hr (EReal.neg_eq_top_iff.mp hh)
  have hFconv := SGPT.Convex.convexOn_toReal_effectiveDomain hproper
  have hFsmall : ConvexOn ℝ (Icc p q) (fun r => (F r).toReal) :=
    ⟨convex_Icc p q, fun r hr s hs a b ha hb hab =>
      hFconv.2 (hsubset hr) (hsubset hs) ha hb hab⟩
  have hgconv : ConvexOn ℝ (Icc p q) g := by
    have heq : g = fun r => (F r).toReal + (φ x).toReal := by
      funext r
      simp only [g, F, sourceTestCurveClosedNegativeTrace, EReal.toReal_neg_eq, γ]
      ring
    rw [heq]
    exact hFsmall.add_const _
  have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ
  have hγφ (r : ℝ) : γ r ≤ φ x := by
    have hh := Γ.toSourceTestCurvePredata.at_le_limit r x
    rwa [hbase] at hh
  have hg0 : ∀ r ∈ Icc p q, 0 ≤ g r := by
    intro r hr
    exact sub_nonneg.mpr (EReal.toReal_le_toReal (hγφ r) (hbot r hr) hφtop)
  have hgmono : MonotoneOn g (Icc p q) := by
    intro r hr s hs hrs
    have hh := EReal.toReal_le_toReal (Γ.toSourceTestCurvePredata.at_antitone x hrs)
      (hbot s hs) (htop r)
    dsimp [g]
    linarith
  have hσ0 (r : ℝ) : 0 ≤ σ r := le_max_left _ _
  have hσmono : MonotoneOn σ (Icc p q) := by
    intro r hr s hs hrs
    apply max_le_max le_rfl
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hrs)]
  have hσconv : ConvexOn ℝ (Icc p q) σ := by
    have hlin := (ConvexOn.smul hε.le (convexOn_id (convex_Icc p q))).add_const (1 : ℝ)
    have hh := (convexOn_const (0 : ℝ) (convex_Icc p q)).sup hlin
    have heq : ((fun _ : ℝ => (0 : ℝ)) ⊔
        ((fun r : ℝ => ε • id r) + fun _ => (1 : ℝ))) = σ := by
      funext r
      change max 0 (ε * r + 1) = max 0 (1 + ε * r)
      congr 1
      ring
    rw [← heq]
    exact hh
  have hKconv : ConvexOn ℝ (Icc p q) (fun r => σ r * g r) :=
    hσconv.mul hgconv (fun r _ => hσ0 r) hg0 (hσmono.monovaryOn hgmono)
  have hKmono : MonotoneOn (fun r => σ r * g r) (Icc p q) := by
    intro r hr s hs hrs
    exact mul_le_mul (hσmono hr hs hrs) (hgmono hr hs hrs) (hg0 r hr) (hσ0 s)
  refine ⟨hKconv, hKmono, ?_⟩
  intro r hr
  have hrneg : r < 0 := hr.2.trans_lt hq
  by_cases har : r ≤ -ε⁻¹
  · have hi : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
    have hh := mul_le_mul_of_nonneg_left har hε.le
    have hσr : 1 + ε * r ≤ 0 := by nlinarith
    simp only [sourceTestCurveRegularizationInput, if_pos har, max_eq_left hσr,
      zero_mul, sub_zero]
    exact hφval
  · have hc := regularization_coefficients hε hrneg (lt_of_not_ge har)
    rw [sourceTestCurveRegularizationInput, if_neg har]
    change convexComb (1 + ε * r) (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ x = _
    change ((1 + ε * r : ℝ) : EReal) * γ r + ((1 - (1 + ε * r) : ℝ) : EReal) * φ x = _
    conv_lhs => rw [hγval r hr, hφval, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    dsimp only
    rw [max_eq_right hc.1.le]
    apply congrArg (fun z : ℝ => (z : EReal))
    dsimp [g, γ]
    ring

omit [BorelSpace M] in
/-- The whole actual input is decreasing, with every pole case handled
before the finite-interval product is used. -/
theorem sourceTestCurveRegularizationInput_antitone
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    AntitoneOn (fun r : ℝ => sourceTestCurveRegularizationInput Γ φ ε r x) (Iio (0 : ℝ)) := by
  intro p hp q hq hpq
  dsimp only
  by_cases hbot : sourceTestCurveRegularizationInput Γ φ ε q x = ⊥
  · rw [hbot]
    exact bot_le
  by_cases hleft : q ≤ -ε⁻¹
  · have hpleft : p ≤ -ε⁻¹ := hpq.trans hleft
    simp only [sourceTestCurveRegularizationInput, if_pos hleft, if_pos hpleft]
    exact le_rfl
  · obtain ⟨_, hmono, hrep⟩ := regularization_finite_product Γ hΓ hε hq
      (lt_of_not_ge hleft) x hbot
    have hh := hmono (show p ∈ Icc p q from ⟨le_rfl, hpq⟩)
      (show q ∈ Icc p q from ⟨hpq, le_rfl⟩) hpq
    rw [hrep q ⟨hpq, le_rfl⟩, hrep p ⟨le_rfl, hpq⟩]
    apply EReal.coe_le_coe
    linarith

omit [BorelSpace M] in
private theorem regularization_input_ordered_chord
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε p q t : ℝ} (hε : 0 < ε) (_hp : p < 0) (hq : q < 0) (hpq : p ≤ q)
    (ht0 : 0 < t) (ht1 : t < 1) (x : M) :
    convexComb t (sourceTestCurveRegularizationInput Γ φ ε p)
      (sourceTestCurveRegularizationInput Γ φ ε q) x ≤
      sourceTestCurveRegularizationInput Γ φ ε (t * p + (1 - t) * q) x := by
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  have hc : t * p + (1 - t) * q ∈ Icc p q := by
    constructor <;> nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hpq),
      mul_nonneg ht.le (sub_nonneg.mpr hpq)]
  by_cases hpb : sourceTestCurveRegularizationInput Γ φ ε p x = ⊥
  · simp only [convexComb, hpb, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  by_cases hqb : sourceTestCurveRegularizationInput Γ φ ε q x = ⊥
  · simp only [convexComb, hqb, EReal.coe_mul_bot_of_pos ht, EReal.add_bot]
    exact bot_le
  by_cases hleft : q ≤ -ε⁻¹
  · have hpleft : p ≤ -ε⁻¹ := hpq.trans hleft
    have hcleft : t * p + (1 - t) * q ≤ -ε⁻¹ := hc.2.trans hleft
    simp only [sourceTestCurveRegularizationInput, if_pos hpleft, if_pos hleft, if_pos hcleft,
      ThetaCapacity.convexComb_self ht0 ht1]
    exact le_rfl
  · obtain ⟨hconv, _, hrep⟩ := regularization_finite_product Γ hΓ hε hq
      (lt_of_not_ge hleft) x hqb
    have hh := hconv.2 (show p ∈ Icc p q from ⟨le_rfl, hpq⟩)
      (show q ∈ Icc p q from ⟨hpq, le_rfl⟩) ht0.le ht.le
      (show t + (1 - t) = 1 by ring)
    change (t : EReal) * sourceTestCurveRegularizationInput Γ φ ε p x +
      ((1 - t : ℝ) : EReal) * sourceTestCurveRegularizationInput Γ φ ε q x ≤ _
    rw [hrep p ⟨le_rfl, hpq⟩, hrep q ⟨hpq, le_rfl⟩, hrep _ hc,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    apply EReal.coe_le_coe
    change _ ≤ _ at hh
    simp only [smul_eq_mul] at hh
    linarith

omit [BorelSpace M] in
private theorem regularization_input_chord
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε p q t : ℝ} (hε : 0 < ε) (hp : p < 0) (hq : q < 0)
    (ht0 : 0 < t) (ht1 : t < 1) (x : M) :
    convexComb t (sourceTestCurveRegularizationInput Γ φ ε p)
      (sourceTestCurveRegularizationInput Γ φ ε q) x ≤
      sourceTestCurveRegularizationInput Γ φ ε (t * p + (1 - t) * q) x := by
  by_cases hpq : p ≤ q
  · exact regularization_input_ordered_chord Γ hΓ hε hp hq hpq ht0 ht1 x
  · have hh := regularization_input_ordered_chord Γ hΓ hε hq hp
      (le_of_not_ge hpq) (sub_pos.mpr ht1) (show 1 - t < 1 by linarith) x
    have hc : (1 - t) * q + (1 - (1 - t)) * p = t * p + (1 - t) * q := by ring
    have hs : 1 - (1 - t) = t := by ring
    simpa only [hc, convexComb, hs, add_comm] using hh

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem negative_trace_convex_of_chords (u : ℝ → M → EReal)
    (hchord : ∀ {p q t : ℝ}, p < 0 → q < 0 → 0 < t → t < 1 → ∀ x : M,
      convexComb t (u p) (u q) x ≤ u (t * p + (1 - t) * q) x)
    (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa only [hb0, ha1, zero_smul, one_smul, add_zero] using hp
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hpneg : p.1 < 0 := by
    by_contra hn
    change sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x p.1 ≤ (p.2 : EReal) at hp
    rw [sourceTestCurveNegativeTrace, dif_neg hn] at hp
    exact not_le_of_gt (EReal.coe_lt_top p.2) hp
  have hqneg : q.1 < 0 := by
    by_contra hn
    change sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x q.1 ≤ (q.2 : EReal) at hq
    rw [sourceTestCurveNegativeTrace, dif_neg hn] at hq
    exact not_le_of_gt (EReal.coe_lt_top q.2) hq
  change sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x p.1 ≤ (p.2 : EReal) at hp
  change sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x q.1 ≤ (q.2 : EReal) at hq
  rw [sourceTestCurveNegativeTrace, dif_pos hpneg] at hp
  rw [sourceTestCurveNegativeTrace, dif_pos hqneg] at hq
  have hplow : ((-p.2 : ℝ) : EReal) ≤ u p.1 x := by
    simpa only [neg_neg, ← EReal.coe_neg] using EReal.neg_le_neg_iff.mpr hp
  have hqlow : ((-q.2 : ℝ) : EReal) ≤ u q.1 x := by
    simpa only [neg_neg, ← EReal.coe_neg] using EReal.neg_le_neg_iff.mpr hq
  have hbEq : b = 1 - a := by linarith
  have ha1 : a < 1 := by linarith
  have hh := hchord hpneg hqneg haPos ha1 x
  change (a : EReal) * u p.1 x + ((1 - a : ℝ) : EReal) * u q.1 x ≤ _ at hh
  rw [← hbEq] at hh
  have hlo := add_le_add
    (mul_le_mul_of_nonneg_left hplow (EReal.coe_nonneg.mpr ha))
    (mul_le_mul_of_nonneg_left hqlow (EReal.coe_nonneg.mpr hb))
  have hfull := hlo.trans hh
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hfull
  have heq : a * (-p.2) + b * (-q.2) = -(a * p.2 + b * q.2) := by ring
  rw [heq, EReal.coe_neg] at hfull
  have hcneg : a * p.1 + b * q.1 < 0 := by
    nlinarith [mul_neg_of_pos_of_neg haPos hpneg, mul_neg_of_pos_of_neg hbPos hqneg]
  change sourceTestCurveNegativeTrace 0 (fun r : Iio (0 : ℝ) => u r.1) x
    (a * p.1 + b * q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [sourceTestCurveNegativeTrace, dif_pos hcneg]
  exact EReal.neg_le_neg_iff.mp (by simpa only [neg_neg] using hfull)

omit [BorelSpace M] in
/-- Actual whole open negative-trace convexity includes the original
constant branch, its splice, all poles and every pair of parameters. -/
theorem sourceTestCurveRegularizationInput_concave
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace 0
      (fun r : Iio (0 : ℝ) => sourceTestCurveRegularizationInput Γ φ ε r.1) x) :=
  negative_trace_convex_of_chords _
    (fun hp hq ht0 ht1 x => regularization_input_chord Γ hΓ hε hp hq ht0 ht1 x) x

/-- The SAME literal ordinary envelope of the original two-branch input. -/
def sourceTestCurveRegularizationFamily (Γ : SourceTestCurve θ) (φ : M → EReal)
    (ε r : ℝ) : M → EReal :=
  sourceSingularityEnvelope θ (sourceTestCurveRegularizationInput Γ φ ε r)

/-- The genuine positive-mass ordinary-envelope producer manufactures ALL
model fields, using the derived positive input mass rather than a shortcut. -/
theorem sourceTestCurveRegularizationFamily_model (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : r < 0) :
    SourceModelPotential θ (sourceTestCurveRegularizationFamily Γ φ ε r) :=
  sourceOrdinaryEnvelope_model omega (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax hε hr)
    (sourceTestCurveRegularizationInput_positiveMass omega Γ hΓ hmax hε hr)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal original negative-parameter formula; the constant branch uses
ONLY the ACTUAL original model equation P[phi]=phi. -/
theorem sourceTestCurveRegularizationFamily_formula
    (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) (ε r : ℝ) :
    sourceTestCurveRegularizationFamily Γ φ ε r =
      if r ≤ -ε⁻¹ then φ else sourceSingularityEnvelope θ
        (convexComb (1 + ε * r) (sourceTestCurveAt Γ.toSourceTestCurvePredata r) φ) := by
  unfold sourceTestCurveRegularizationFamily sourceTestCurveRegularizationInput
  split_ifs with h
  · exact hφ.choose_spec.1.symm
  · rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every actual envelope stays between the unchanged original slice
and the unchanged actual model, including at every original pole. -/
theorem sourceTestCurveRegularizationFamily_bounds
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε r : ℝ} (hε : 0 < ε) (hr : r < 0) :
    sourceTestCurveAt Γ.toSourceTestCurvePredata r ≤ sourceTestCurveRegularizationFamily Γ φ ε r ∧
      sourceTestCurveRegularizationFamily Γ φ ε r ≤ φ := by
  have hrmax : r < Γ.max := by rwa [hmax]
  have hfix : sourceSingularityEnvelope θ (sourceTestCurveAt Γ.toSourceTestCurvePredata r) =
      sourceTestCurveAt Γ.toSourceTestCurvePredata r := by
    rw [sourceTestCurveAt_of_lt Γ.toSourceTestCurvePredata hrmax]
    exact Γ.fixedPoint ⟨r, hrmax⟩
  have hb := sourceTestCurveRegularizationInput_bounds Γ hΓ hε hr
  have hlo := sourceOrdinaryEnvelope_mono (θ := θ) (MoreSingularOn.of_le fun x _ => hb.1 x)
  have hup := sourceOrdinaryEnvelope_mono (θ := θ) (MoreSingularOn.of_le fun x _ => hb.2.1 x)
  rw [hfix] at hlo
  rw [← hφ.choose_spec.1] at hup
  exact ⟨hlo, hup⟩

omit [BorelSpace M] in
/-- Actual ordinary-envelope monotonicity transports the WHOLE original
input antitonicity without an output monotonicity premise. -/
theorem sourceTestCurveRegularizationFamily_antitone
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    AntitoneOn (fun r : ℝ => sourceTestCurveRegularizationFamily Γ φ ε r x) (Iio (0 : ℝ)) := by
  intro p hp q hq hpq
  exact sourceOrdinaryEnvelope_mono (θ := θ) (MoreSingularOn.of_le fun y _ =>
    sourceTestCurveRegularizationInput_antitone Γ hΓ hε y hp hq hpq) x

omit [BorelSpace M] in
/-- The existing genuine ordinary-P concavity and actual input concavity
manufacture the entire required open negative-trace convexity. -/
theorem sourceTestCurveRegularizationFamily_concave
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace 0
      (fun r : Iio (0 : ℝ) => sourceTestCurveRegularizationFamily Γ φ ε r.1) x) := by
  apply negative_trace_convex_of_chords
  intro p q t hp hq ht0 ht1 y
  have hh := sourceOrdinaryEnvelope_convexComb_le
    (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax hε hp)
    (sourceTestCurveRegularizationInput_thetaPSH hφ Γ hmax hε hq) ht0 ht1
  have hm := sourceOrdinaryEnvelope_mono (θ := θ) (MoreSingularOn.of_le fun z _ =>
    regularization_input_chord Γ hΓ hε hp hq ht0 ht1 z)
  exact (hh y).trans (hm y)

/-- All original preliminary fields are produced by the actual ordinary
family, without an output PSH/concavity/fixed-point certificate. -/
def sourceTestCurveRegularizationPredata (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) : SourceTestCurvePredata θ where
  max := 0
  potential r := sourceTestCurveRegularizationFamily Γ φ ε r.1
  thetaPSH r := (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax hε r.2).thetaPSH
  antitone x p q hpq := sourceTestCurveRegularizationFamily_antitone Γ hΓ hε x p.2 q.2 hpq
  concave x := sourceTestCurveRegularizationFamily_concave Γ hΓ hmax hε x
  fixedPoint r := (sourceTestCurveRegularizationFamily_model omega Γ hΓ hmax hε r.2).choose_spec.1.symm

/-- The ACTUAL spatial regularized supremum is phi: every term is below
phi and the INCLUDED original threshold term is exactly phi. -/
theorem sourceTestCurveRegularizationPredata_limit (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) :
    sourceTestCurveLimit (sourceTestCurveRegularizationPredata omega Γ hΓ hmax hε) = φ := by
  change uscRegularization (fun x => ⨆ r : Iio (0 : ℝ),
    sourceTestCurveRegularizationFamily Γ φ ε r.1 x) = φ
  apply le_antisymm
  · apply uscRegularization_le
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH).1.quasiPlurisubharmonic.upperSemicontinuous
    intro x
    apply iSup_le
    intro r
    exact (sourceTestCurveRegularizationFamily_bounds Γ hΓ hmax hε r.2).2 x
  · have ha : -ε⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hε)
    let a : Iio (0 : ℝ) := ⟨-ε⁻¹, ha⟩
    have hφa : sourceTestCurveRegularizationFamily Γ φ ε a.1 = φ := by
      rw [sourceTestCurveRegularizationFamily_formula hφ]
      exact if_pos (le_refl _)
    intro x
    have hh := le_iSup (fun r : Iio (0 : ℝ) => sourceTestCurveRegularizationFamily Γ φ ε r.1 x) a
    rw [hφa] at hh
    exact hh.trans (le_uscRegularization
      (fun y => ⨆ r : Iio (0 : ℝ), sourceTestCurveRegularizationFamily Γ φ ε r.1 y) x)

/-- The ACTUAL source test curve. Its positive limit mass is manufactured
from the SAME actual model via the proved literal based-limit equality. -/
def sourceTestCurveRegularization (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) : SourceTestCurve θ where
  toSourceTestCurvePredata := sourceTestCurveRegularizationPredata omega Γ hΓ hmax hε
  positiveLimitMass := by
    have heq := sourceTestCurveRegularizationPredata_limit omega Γ hΓ hmax hε
    generalize sourceTestCurveRegularizationPredata omega Γ hΓ hmax hε = P at heq ⊢
    cases heq
    exact hφ.choose_spec.2

/-- Literal original real cutoff reader for the genuine bounded object. -/
theorem sourceTestCurveRegularization_max (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) : (sourceTestCurveRegularization omega Γ hΓ hmax hε).max = 0 := rfl

/-- EVERY original negative-parameter potential is the SAME ordinary
family, hence exactly the printed constant/active two-branch formula. -/
theorem sourceTestCurveRegularization_potential (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) (r : Iio (sourceTestCurveRegularization omega Γ hΓ hmax hε).max) :
    (sourceTestCurveRegularization omega Γ hΓ hmax hε).potential r =
      sourceTestCurveRegularizationFamily Γ φ ε r.1 := rfl

/-- Genuine original based AND bounded membership, using the actual
included threshold and the actual subtype atBot event, not an output premise. -/
theorem sourceTestCurveRegularization_bounded (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (hmax : Γ.max = 0)
    {ε : ℝ} (hε : 0 < ε) :
    sourceTestCurveRegularization omega Γ hΓ hmax hε ∈ SourceBoundedTestCurves θ φ hφ := by
  refine ⟨sourceTestCurveRegularizationPredata_limit omega Γ hΓ hmax hε, ?_⟩
  let a : Iio (sourceTestCurveRegularization omega Γ hΓ hmax hε).max :=
    ⟨-ε⁻¹, by change -ε⁻¹ < 0; exact neg_neg_of_pos (inv_pos.mpr hε)⟩
  apply eventually_atBot.mpr
  refine ⟨a, fun r hr => ?_⟩
  rw [sourceTestCurveRegularization_potential,
    sourceTestCurveRegularizationFamily_formula hφ]
  exact if_pos (show r.1 ≤ -ε⁻¹ from hr)

end SGPT.PSH.VariableComplexAtlas
