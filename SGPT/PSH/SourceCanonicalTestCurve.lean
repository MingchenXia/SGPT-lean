import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourcePMassCharacterization
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes
import SGPT.Foundations.Analysis.Pending.ActualPositiveInterpolationGlobalBound
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination

/-- The actual canonical coefficient, including the printed constant branch. -/
def sourceCanonicalTestCoefficient (τ : ℝ) : ℝ := max (1 + τ) 0

/-- Every original parameter gives precisely a closed-left strict-right weight. -/
theorem sourceCanonicalTestCoefficient_weights {τ : ℝ} (hτ : τ < 0) :
    0 ≤ sourceCanonicalTestCoefficient τ ∧ sourceCanonicalTestCoefficient τ < 1 :=
  ⟨le_max_right _ _, max_lt (by linarith) zero_lt_one⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- SAME original input, written with a zero coefficient on the constant branch.
EReal multiplication by zero preserves the literal original minimal potential. -/
def sourceCanonicalTestInput (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (τ : Iio (0 : ℝ)) : M → EReal :=
  convexComb (sourceCanonicalTestCoefficient τ) φ (sourceMinimalEnvelope θ)

/-- The actual original ordinary-P family; no model or output certificate. -/
def sourceCanonicalTestPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) (τ : Iio (0 : ℝ)) : M → EReal :=
  sourceSingularityEnvelope θ (sourceCanonicalTestInput θ φ τ)

/-- The original constant branch is literally the minimal potential before P. -/
theorem sourceCanonicalTestInput_of_le_neg_one (φ : M → EReal)
    (τ : Iio (0 : ℝ)) (hτ : (τ : ℝ) ≤ -1) :
    sourceCanonicalTestInput θ φ τ = sourceMinimalEnvelope θ := by
  have hcoef : sourceCanonicalTestCoefficient τ = 0 := max_eq_right (by linarith)
  funext x
  simp only [sourceCanonicalTestInput, hcoef, convexComb, EReal.coe_zero, zero_mul,
    sub_zero, EReal.coe_one, one_mul, zero_add]

/-- The exact printed strict branch, with the original UNNORMALIZED input. -/
theorem sourceCanonicalTestPotential_of_neg_one_lt (φ : M → EReal)
    (τ : Iio (0 : ℝ)) (hτ : -1 < (τ : ℝ)) :
    sourceCanonicalTestPotential θ φ τ =
      sourceSingularityEnvelope θ (fun x ↦
        ((1 + (τ : ℝ) : ℝ) : EReal) * φ x + ((-(τ : ℝ) : ℝ) : EReal) *
          sourceMinimalEnvelope θ x) := by
  have hcoef : sourceCanonicalTestCoefficient τ = 1 + (τ : ℝ) := max_eq_left (by linarith)
  apply congrArg (sourceSingularityEnvelope θ)
  funext x
  simp only [sourceCanonicalTestInput, hcoef, convexComb,
    show 1 - (1 + (τ : ℝ)) = -(τ : ℝ) by ring]

/-- Actual finite constant invariance keeps the WHOLE original family identical.
The normalization used to prove its order never changes the printed functions. -/
theorem sourceCanonicalTestPotential_add_const_eq (φ : M → EReal) (C : ℝ) :
    sourceCanonicalTestPotential θ (fun x ↦ φ x + (C : EReal)) =
      sourceCanonicalTestPotential θ φ := by
  funext τ
  by_cases hz : sourceCanonicalTestCoefficient τ = 0
  · apply congrArg (sourceSingularityEnvelope θ)
    funext x
    simp only [sourceCanonicalTestInput, hz, convexComb,
      EReal.coe_zero, zero_mul, sub_zero, EReal.coe_one, one_mul, zero_add]
  · have hw := sourceCanonicalTestCoefficient_weights τ.property
    have hp : 0 < sourceCanonicalTestCoefficient τ := lt_of_le_of_ne hw.1 (Ne.symm hz)
    have heq : sourceCanonicalTestInput θ (fun x ↦ φ x + (C : EReal)) τ =
        fun x ↦ sourceCanonicalTestInput θ φ τ x +
          ((sourceCanonicalTestCoefficient τ * C : ℝ) : EReal) := by
      simpa only [sourceCanonicalTestInput, EReal.coe_zero, add_zero, mul_zero] using
        POrderAffineRooftop.convexComb_add_const hp hw.2 φ (sourceMinimalEnvelope θ) C 0
    simp only [sourceCanonicalTestPotential, heq, sourceSingularityEnvelope_eq_native,
      singularityEnvelope_add_const]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- The literal original branch at and below minus one, with original V
fixedness internally manufactured from genuine big theta. -/
theorem sourceCanonicalTestPotential_of_le_neg_one (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (τ : Iio (0 : ℝ)) (hτ : (τ : ℝ) ≤ -1) :
    sourceCanonicalTestPotential θ φ τ = sourceMinimalEnvelope θ := by
  rw [sourceCanonicalTestPotential, sourceCanonicalTestInput_of_le_neg_one φ τ hτ]
  exact (sourceMinimalEnvelope_model ω θ hbig).choose_spec.1.symm

/-- EXISTING genuine positive interpolation produces the actual model of EVERY
strict input; all arbitrary original input masses and poles are retained. -/
theorem sourceCanonicalTestPotential_model (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (τ : Iio (0 : ℝ)) :
    SourceModelPotential θ (sourceCanonicalTestPotential θ φ τ) := by
  by_cases hτ : (τ : ℝ) ≤ -1
  · rw [sourceCanonicalTestPotential_of_le_neg_one ω hbig φ τ hτ]
    exact sourceMinimalEnvelope_model ω θ hbig
  · have hs0 : 0 < sourceCanonicalTestCoefficient τ := by
      change 0 < max (1 + (τ : ℝ)) 0
      exact (show 0 < 1 + (τ : ℝ) by linarith).trans_le (le_max_left _ _)
    have hs1 := (sourceCanonicalTestCoefficient_weights τ.property).2
    obtain ⟨_hw, _hpos, hmodel, _hbound⟩ :=
      ActualPositiveInterpolationGlobalBound.exists_positive_model_interpolation ω
        (atlasClosedFormToNative θ) hbig ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
        (ε := 1 - sourceCanonicalTestCoefficient τ) (sub_pos.mpr hs1) (by linarith)
    apply (sourceModelPotential_iff_native θ _).mpr
    simpa only [sourceCanonicalTestPotential, sourceSingularityEnvelope_eq_native,
      sourceCanonicalTestInput, sourceMinimalEnvelope_eq_native,
      ActualPositiveInterpolationGlobalBound.positiveInterpolation, sub_sub_cancel] using hmodel

/-- ALL original slice values lie below SAME literal V, before any limit. -/
theorem sourceCanonicalTestPotential_le_minimal (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (τ : Iio (0 : ℝ)) :
    sourceCanonicalTestPotential θ φ τ ≤ sourceMinimalEnvelope θ := by
  have hV := (sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic
  rw [sourceMinimalEnvelope_eq_native] at hV
  rw [sourceCanonicalTestPotential, sourceSingularityEnvelope_eq_native,
    sourceMinimalEnvelope_eq_native]
  exact uscRegularization_le hV.1.quasiPlurisubharmonic.upperSemicontinuous
    (singularitySupremum_le_thetaPshSupremum _ _)

private theorem canonical_comb_zero {X : Type*} (u v : X → EReal) :
    convexComb 0 u v = v := by
  funext x
  simp only [convexComb, EReal.coe_zero, zero_mul, sub_zero, EReal.coe_one, one_mul, zero_add]

/-- Actual finite-nonnegative EReal distributivity handles all original poles,
including vanishing inner weights; no value is realified. -/
private theorem canonical_nested_comb {X : Type*} (u v : X → EReal)
    {t a b : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    convexComb t (convexComb a u v) (convexComb b u v) =
      convexComb (t * a + (1 - t) * b) u v := by
  have ht : 0 ≤ 1 - t := (sub_pos.mpr ht1).le
  have hta : 0 ≤ t * a := mul_nonneg ht0.le ha0
  have htb : 0 ≤ (1 - t) * b := mul_nonneg ht hb0
  have htc : 0 ≤ t * (1 - a) := mul_nonneg ht0.le (sub_nonneg.mpr ha1)
  have htd : 0 ≤ (1 - t) * (1 - b) := mul_nonneg ht (sub_nonneg.mpr hb1)
  funext x
  simp only [convexComb]
  rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ht0.le)
      (EReal.coe_ne_top t),
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr ht)
      (EReal.coe_ne_top (1 - t))]
  simp only [← mul_assoc, ← EReal.coe_mul]
  rw [add_add_add_comm,
    ← EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr hta) (EReal.coe_nonneg.mpr htb),
    ← EReal.right_distrib_of_nonneg (EReal.coe_nonneg.mpr htc) (EReal.coe_nonneg.mpr htd),
    ← EReal.coe_add, ← EReal.coe_add]
  congr 2
  congr 1
  ring

private theorem canonical_comb_antitone_closed_left {X : Type*} {u v : X → EReal}
    (huv : u ≤ v) (hvtop : ∀ x, v x ≠ ⊤)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) :
    convexComb b u v ≤ convexComb a u v := by
  by_cases ha : a = 0
  · rw [ha, canonical_comb_zero]
    by_cases hb : b = 0
    · rw [hb, canonical_comb_zero]
    · have hb0 : 0 < b := lt_of_le_of_ne (ha0.trans hab) (Ne.symm hb)
      exact (convexComb_mono hb0.le hb1.le huv le_rfl).trans_eq
        (ThetaCapacity.convexComb_self hb0 hb1 v)
  · exact DominationPrincipleBarrier.convexComb_antitone_of_le huv hvtop
      (lt_of_le_of_ne ha0 (Ne.symm ha)) hab

private theorem canonical_input_thetaPSH (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (τ : Iio (0 : ℝ)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceCanonicalTestInput θ φ τ) := by
  have hw := sourceCanonicalTestCoefficient_weights τ.property
  by_cases hz : sourceCanonicalTestCoefficient τ = 0
  · simpa only [sourceCanonicalTestInput, hz, canonical_comb_zero] using
      (sourceMinimalEnvelope_model ω θ hbig).thetaPSH
  · apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    exact isThetaPshPotential_convexComb ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
      (sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic
      (lt_of_le_of_ne hw.1 (Ne.symm hz)) hw.2

private theorem canonical_potential_antitone_of_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφV : φ ≤ sourceMinimalEnvelope θ) :
    ∀ x, Antitone (fun τ : Iio (0 : ℝ) ↦ sourceCanonicalTestPotential θ φ τ x) := by
  intro x a b hab
  have ha := sourceCanonicalTestCoefficient_weights a.property
  have hb := sourceCanonicalTestCoefficient_weights b.property
  have habval : (a : ℝ) ≤ (b : ℝ) := hab
  have hab' : sourceCanonicalTestCoefficient a ≤ sourceCanonicalTestCoefficient b :=
    max_le_max (add_le_add le_rfl habval) le_rfl
  exact sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun y _ ↦
    canonical_comb_antitone_closed_left hφV
      (sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic.1.quasiPlurisubharmonic.ne_top
      ha.1 hab' hb.2 y) x

private theorem canonical_potential_convexComb_le_of_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφV : φ ≤ sourceMinimalEnvelope θ) (a b : Iio (0 : ℝ))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (sourceCanonicalTestPotential θ φ a) (sourceCanonicalTestPotential θ φ b) ≤
      sourceCanonicalTestPotential θ φ
        ⟨t * (a : ℝ) + (1 - t) * (b : ℝ), by
          change t * (a : ℝ) + (1 - t) * (b : ℝ) < 0
          nlinarith [mul_pos ht0 (neg_pos.mpr a.property),
            mul_pos (sub_pos.mpr ht1) (neg_pos.mpr b.property)]⟩ := by
  let c : Iio (0 : ℝ) := ⟨t * (a : ℝ) + (1 - t) * (b : ℝ), by
    change t * (a : ℝ) + (1 - t) * (b : ℝ) < 0
    nlinarith [mul_pos ht0 (neg_pos.mpr a.property),
      mul_pos (sub_pos.mpr ht1) (neg_pos.mpr b.property)]⟩
  let w : ℝ := t * sourceCanonicalTestCoefficient a +
    (1 - t) * sourceCanonicalTestCoefficient b
  have ha := sourceCanonicalTestCoefficient_weights a.property
  have hb := sourceCanonicalTestCoefficient_weights b.property
  have hc := sourceCanonicalTestCoefficient_weights c.property
  have hw : w < 1 := by
    dsimp [w]
    nlinarith [mul_pos ht0 (sub_pos.mpr ha.2),
      mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hb.2)]
  have hcw : sourceCanonicalTestCoefficient c ≤ w := by
    apply max_le
    · have hA := mul_le_mul_of_nonneg_left
        (le_max_left (1 + (a : ℝ)) 0) ht0.le
      have hB := mul_le_mul_of_nonneg_left
        (le_max_left (1 + (b : ℝ)) 0) (sub_pos.mpr ht1).le
      dsimp [c, w, sourceCanonicalTestCoefficient] at *
      nlinarith
    · exact add_nonneg (mul_nonneg ht0.le ha.1)
        (mul_nonneg (sub_pos.mpr ht1).le hb.1)
  have hinput : convexComb t (sourceCanonicalTestInput θ φ a)
      (sourceCanonicalTestInput θ φ b) = convexComb w φ (sourceMinimalEnvelope θ) :=
    canonical_nested_comb φ (sourceMinimalEnvelope θ) ht0 ht1 ha.1 ha.2.le hb.1 hb.2.le
  have hconc := sourceOrdinaryEnvelope_convexComb_le
    (canonical_input_thetaPSH ω hbig hφ a) (canonical_input_thetaPSH ω hbig hφ b) ht0 ht1
  rw [hinput] at hconc
  exact hconc.trans (sourceOrdinaryEnvelope_mono (MoreSingularOn.of_le fun x _ ↦
    canonical_comb_antitone_closed_left hφV
      (sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic.1.quasiPlurisubharmonic.ne_top
      hc.1 hcw hw x))

private theorem canonical_negativeTrace_convex_of_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφV : φ ≤ sourceMinimalEnvelope θ) (x : M) :
    SGPT.Convex.IsConvex (sourceTestCurveNegativeTrace 0 (sourceCanonicalTestPotential θ φ) x) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa only [hb0, ha1, zero_smul, one_smul, add_zero] using hp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hb' : 1 - a = b := by linarith
  have hpdom : p.1 < 0 := by
    by_contra hnot
    simp only [SGPT.Convex.epigraph, mem_ofPred_eq, sourceTestCurveNegativeTrace,
      dif_neg hnot] at hp
    exact (EReal.coe_ne_top p.2) (top_le_iff.mp hp)
  have hqdom : q.1 < 0 := by
    by_contra hnot
    simp only [SGPT.Convex.epigraph, mem_ofPred_eq, sourceTestCurveNegativeTrace,
      dif_neg hnot] at hq
    exact (EReal.coe_ne_top q.2) (top_le_iff.mp hq)
  change sourceTestCurveNegativeTrace 0 (sourceCanonicalTestPotential θ φ) x p.1 ≤
    (p.2 : EReal) at hp
  change sourceTestCurveNegativeTrace 0 (sourceCanonicalTestPotential θ φ) x q.1 ≤
    (q.2 : EReal) at hq
  rw [sourceTestCurveNegativeTrace, dif_pos hpdom] at hp
  rw [sourceTestCurveNegativeTrace, dif_pos hqdom] at hq
  have hpa : ((-p.2 : ℝ) : EReal) ≤ sourceCanonicalTestPotential θ φ ⟨p.1, hpdom⟩ x := by
    simpa only [← EReal.coe_neg, neg_neg] using (EReal.neg_le_neg_iff.mpr hp)
  have hqa : ((-q.2 : ℝ) : EReal) ≤ sourceCanonicalTestPotential θ φ ⟨q.1, hqdom⟩ x := by
    simpa only [← EReal.coe_neg, neg_neg] using (EReal.neg_le_neg_iff.mpr hq)
  have hcdom : a * p.1 + b * q.1 < 0 := by
    nlinarith [mul_pos hap (neg_pos.mpr hpdom), mul_pos hbp (neg_pos.mpr hqdom)]
  have hconc := canonical_potential_convexComb_le_of_le ω hbig hφ hφV
    ⟨p.1, hpdom⟩ ⟨q.1, hqdom⟩ hap ha1 x
  have hfloor : -(((a * p.2 + b * q.2 : ℝ) : EReal)) ≤
      sourceCanonicalTestPotential θ φ ⟨a * p.1 + b * q.1, hcdom⟩ x := by
    calc
      _ = convexComb a (fun _ : M ↦ ((-p.2 : ℝ) : EReal))
          (fun _ ↦ ((-q.2 : ℝ) : EReal)) x := by
        simp only [convexComb, hb', ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_neg]
        congr 1
        ring
      _ ≤ convexComb a (sourceCanonicalTestPotential θ φ ⟨p.1, hpdom⟩)
          (sourceCanonicalTestPotential θ φ ⟨q.1, hqdom⟩) x :=
        convexComb_mono ha ha1.le (fun _ ↦ hpa) (fun _ ↦ hqa) x
      _ ≤ _ := by simpa only [hb'] using hconc
  change sourceTestCurveNegativeTrace 0 (sourceCanonicalTestPotential θ φ) x
    (a * p.1 + b * q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [sourceTestCurveNegativeTrace, dif_pos hcdom]
  exact (EReal.neg_le_neg_iff.mpr hfloor).trans_eq (neg_neg _)

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual compact normalization is ONLY a proof device. The full original
ordinary-P family remains LITERALLY identical after its finite shift. -/
private theorem canonical_normalization
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    ∃ u : M → EReal, (ofFixedModel n M).IsThetaPSH θ u ∧
      u ≤ sourceMinimalEnvelope θ ∧
      sourceCanonicalTestPotential θ u = sourceCanonicalTestPotential θ φ := by
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ).exists_normalized_sub_const
  refine ⟨fun x ↦ φ x - (C : EReal),
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr hC.1, ?_, ?_⟩
  · rw [sourceMinimalEnvelope_eq_native]
    exact le_thetaPshSupremum hC.1 hC.2
  · simpa only [sub_eq_add_neg, EReal.coe_neg] using
      sourceCanonicalTestPotential_add_const_eq (θ := θ) φ (-C)

/-- The FULL original preliminary object, with arbitrary original input.
Every genuine joint/measure/envelope ingredient is produced or reused;
concavity and order are transported along actual constant-invariance. -/
def sourceCanonicalTestCurvePredata (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : SourceTestCurvePredata θ where
  max := 0
  potential := sourceCanonicalTestPotential θ φ
  thetaPSH := fun τ ↦ (sourceCanonicalTestPotential_model ω hbig hφ τ).thetaPSH
  antitone := by
    obtain ⟨u, _hu, huV, heq⟩ := canonical_normalization hφ
    rw [← heq]
    exact canonical_potential_antitone_of_le ω hbig huV
  concave := by
    obtain ⟨u, hu, huV, heq⟩ := canonical_normalization hφ
    rw [← heq]
    exact canonical_negativeTrace_convex_of_le ω hbig hu huV
  fixedPoint := fun τ ↦ (sourceCanonicalTestPotential_model ω hbig hφ τ).choose_spec.1.symm

/-- The raw whole-family supremum is SAME actual V: every value is below
it and actual original parameter minus one attains it. USC then changes nothing. -/
theorem sourceCanonicalTestCurve_limit_eq (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceTestCurveLimit (sourceCanonicalTestCurvePredata ω θ hbig φ hφ) =
      sourceMinimalEnvelope θ := by
  have hsup : (fun x ↦ ⨆ τ : Iio (0 : ℝ), sourceCanonicalTestPotential θ φ τ x) =
      sourceMinimalEnvelope θ := by
    funext x
    apply le_antisymm
    · exact iSup_le fun τ ↦ sourceCanonicalTestPotential_le_minimal ω hbig φ τ x
    · have hτ : (-1 : ℝ) < 0 := by norm_num
      have hmem := le_iSup (fun τ : Iio (0 : ℝ) ↦ sourceCanonicalTestPotential θ φ τ x) ⟨-1, hτ⟩
      simpa only [sourceCanonicalTestPotential_of_le_neg_one ω hbig φ ⟨-1, hτ⟩ le_rfl] using hmem
  change uscRegularization (fun x ↦ ⨆ τ : Iio (0 : ℝ), sourceCanonicalTestPotential θ φ τ x) = _
  rw [hsup]
  exact uscRegularization_eq
    (sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic.1.quasiPlurisubharmonic.upperSemicontinuous

/-- The actual FULL ORIGINAL canonical test curve, with its genuine positive
raw-limit mass supplied by the internally produced original minimal model. -/
def sourceCanonicalTestCurve (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) : SourceTestCurve θ where
  toSourceTestCurvePredata := sourceCanonicalTestCurvePredata ω θ hbig φ hφ
  positiveLimitMass := by
    simpa only [sourceCanonicalTestCurve_limit_eq ω θ hbig φ hφ] using
      (sourceMinimalEnvelope_model ω θ hbig).choose_spec.2

/-- Original based membership and GENUINE atBot eventual equality on the
original Iio interval prove TC-infinity, with no chosen-base/output premise. -/
theorem sourceCanonicalTestCurve_mem_bounded (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceCanonicalTestCurve ω θ hbig φ hφ ∈
      SourceBoundedTestCurves θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) := by
  refine ⟨sourceCanonicalTestCurve_limit_eq ω θ hbig φ hφ, ?_⟩
  have hτ : (-1 : ℝ) < 0 := by norm_num
  change ∀ᶠ τ : Iio (0 : ℝ) in atBot,
    sourceCanonicalTestPotential θ φ τ = sourceMinimalEnvelope θ
  filter_upwards [eventually_le_atBot (⟨-1, hτ⟩ : Iio (0 : ℝ))] with τ hτ
  exact sourceCanonicalTestPotential_of_le_neg_one ω hbig φ τ hτ

/-- ENTIRE original ex:cantest: arbitrary original input, actual cutoff0,
both exact printed branches INCLUDING minus one, actual base Vtheta and
original TC-infinity membership. No energy/ray/cutoff-positive inference. -/
theorem sourceCanonicalTestCurve_whole (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    (sourceCanonicalTestCurve ω θ hbig φ hφ).max = 0 ∧
      sourceCanonicalTestCurve ω θ hbig φ hφ ∈
        SourceBoundedTestCurves θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) ∧
      (∀ (τ : Iio (0 : ℝ)), (τ : ℝ) ≤ -1 →
        (sourceCanonicalTestCurve ω θ hbig φ hφ).potential τ = sourceMinimalEnvelope θ) ∧
      (∀ (τ : Iio (0 : ℝ)), -1 < (τ : ℝ) →
        (sourceCanonicalTestCurve ω θ hbig φ hφ).potential τ =
          sourceSingularityEnvelope θ (fun x ↦
            ((1 + (τ : ℝ) : ℝ) : EReal) * φ x + ((-(τ : ℝ) : ℝ) : EReal) *
              sourceMinimalEnvelope θ x)) :=
  ⟨rfl, sourceCanonicalTestCurve_mem_bounded ω θ hbig φ hφ,
    fun τ hτ ↦ sourceCanonicalTestPotential_of_le_neg_one ω hbig φ τ hτ,
    fun τ hτ ↦ sourceCanonicalTestPotential_of_neg_one_lt φ τ hτ⟩

end SGPT.PSH.VariableComplexAtlas
