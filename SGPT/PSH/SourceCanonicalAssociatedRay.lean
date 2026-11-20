import SGPT.PSH.SourceCanonicalTestCurve
import SGPT.PSH.SourceAssociatedRay
import SGPT.PSH.SourceTestCurveFiniteEnergyCorrespondence
import SGPT.PSH.SourceTestCurveBoundedEnergyGeneral
import SGPT.Foundations.Analysis.Pending.SingularBoundedRayJoinStageOrder

/-! # The actual canonical test curve and associated ray

Complete source-facing proof of SGPT ex:testcurve:L843 (69360cfd), including
its original unnormalized energy formula. The proof retains every pole and
repairs only the printed raw supremum by including its actual slope −1 branch.
The false strict-open raw identity is excluded; an exact pole counterexample
is retained. Source blueprint: source-canonical-associated-ray.tex.
Private checked component sources and receipts: validation/canonical-associated-ray-20261105.
-/

/-! # The pole-safe closed-left raw canonical transform

The intermediate raw open-interval identity in source eq:lvarphigeq_temp1
omits the actual constant branch at slope −1. This file keeps that branch
and the original EReal convention zero times bottom equals zero.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.CanonicalRayDraft

open Set Filter
open scoped Topology

def rawCanonicalAffine (a b : EReal) (t τ : ℝ) : EReal :=
  ((1 + τ : ℝ) : EReal) * a + ((-τ : ℝ) : EReal) * b + ((t * τ : ℝ) : EReal)

theorem rawCanonicalAffine_neg_one (a b : EReal) (t : ℝ) :
    rawCanonicalAffine a b t (-1) = b - (t : EReal) := by
  simp [rawCanonicalAffine, sub_eq_add_neg, EReal.coe_neg]

theorem rawCanonicalAffine_le_max {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (t : ℝ) {τ : ℝ} (hτ : τ ∈ Ico (-1 : ℝ) 0) :
    rawCanonicalAffine a b t τ ≤ max a (b - (t : EReal)) := by
  by_cases hm : τ = -1
  · rw [hm, rawCanonicalAffine_neg_one]
    exact le_max_right _ _
  have hstrict : (-1 : ℝ) < τ := lt_of_le_of_ne hτ.1 (Ne.symm hm)
  have hα : 0 < 1 + τ := by linarith
  have hβ : 0 < -τ := by linarith [hτ.2]
  by_cases hab : a = ⊥
  · simp only [rawCanonicalAffine, hab, EReal.coe_mul_bot_of_pos hα,
      EReal.bot_add, bot_le]
  by_cases hbb : b = ⊥
  · simp only [rawCanonicalAffine, hbb, EReal.coe_mul_bot_of_pos hβ,
      EReal.add_bot, EReal.bot_add, bot_le]
  rw [← EReal.coe_toReal ha hab, ← EReal.coe_toReal hb hbb,
    rawCanonicalAffine, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub,
    ← EReal.coe_strictMono.monotone.map_max, EReal.coe_le_coe_iff]
  have hA := le_max_left a.toReal (b.toReal - t)
  have hB := le_max_right a.toReal (b.toReal - t)
  nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hA),
    mul_nonneg hβ.le (sub_nonneg.mpr hB)]

/-- Corrected literal raw identity, including the source's actual constant
branch. Order a≤b retains the common-pole behavior of u≤V_theta. -/
theorem rawCanonicalAffine_iSup_closed_left {a b : EReal} (hab : a ≤ b) (hb : b ≠ ⊤)
    (t : ℝ) :
    (⨆ τ : Ico (-1 : ℝ) 0, rawCanonicalAffine a b t τ.val) =
      max a (b - (t : EReal)) := by
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  apply le_antisymm
  · exact iSup_le fun τ => rawCanonicalAffine_le_max ha hb t τ.property
  apply max_le
  · by_cases habot : a = ⊥
    · simp only [habot, bot_le]
    have hbb : b ≠ ⊥ := ne_bot_of_le_ne_bot habot hab
    have hA : (a.toReal : EReal) = a := EReal.coe_toReal ha habot
    have hB : (b.toReal : EReal) = b := EReal.coe_toReal hb hbb
    have hfun (τ : ℝ) : rawCanonicalAffine a b t τ =
        (((1 + τ) * a.toReal + (-τ) * b.toReal + t * τ : ℝ) : EReal) := by
      rw [← hA, ← hB, rawCanonicalAffine]
      simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.toReal_coe]
    have hfunEq : rawCanonicalAffine a b t = (fun τ : ℝ =>
        (((1 + τ) * a.toReal + (-τ) * b.toReal + t * τ : ℝ) : EReal)) :=
      funext hfun
    have hc : Continuous (fun τ : ℝ =>
        (((1 + τ) * a.toReal + (-τ) * b.toReal + t * τ : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    have hl : Tendsto (rawCanonicalAffine a b t) (𝓝[<] (0 : ℝ)) (𝓝 a) := by
      rw [hfunEq]
      simpa only [add_zero, one_mul, neg_zero, zero_mul, mul_zero, hA] using
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))] with τ hτ hlow
    exact le_iSup (fun σ : Ico (-1 : ℝ) 0 => rawCanonicalAffine a b t σ.val)
      ⟨τ, ⟨hlow.le, hτ⟩⟩
  · have h := le_iSup
      (fun τ : Ico (-1 : ℝ) 0 => rawCanonicalAffine a b t τ.val)
      ⟨-1, ⟨le_rfl, by norm_num⟩⟩
    simpa only [rawCanonicalAffine_neg_one] using h

/-- The printed open-interval identity is not used at a pole. This exact
scalar obstruction is preserved separately from the repaired source proof. -/
theorem rawCanonicalAffine_open_pole_counterexample :
    (⨆ τ : Ioo (-1 : ℝ) 0, rawCanonicalAffine ⊥ 0 1 τ.val) = ⊥ ∧
      max (⊥ : EReal) ((0 : EReal) - (1 : EReal)) ≠ ⊥ := by
  constructor
  · apply le_antisymm (iSup_le fun τ => ?_) bot_le
    have hα : 0 < 1 + τ.val := by linarith [τ.property.1]
    simp only [rawCanonicalAffine, EReal.coe_mul_bot_of_pos hα,
      EReal.bot_add, le_refl]
  · norm_num
    exact EReal.coe_ne_top (1 : ℝ)

end SGPT.PSH.CanonicalRayDraft

end

/-! # The actual canonical test curve corresponds to the actual associated ray

Source ex:testcurve:L843, latest source commit 69360cfd, chapter_testcurve829–866.
The proof uses actual Perron competitors and endpoint order, retaining the
original slope −1 branch, arbitrary original input, every pole and all n.
The printed open-interval raw identity is repaired separately; it is not bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.CanonicalRayDraft
open ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem canonicalInput_add_linear_eq_raw
    (u : M → EReal) (τ : Iio (0 : ℝ)) (hτ : (-1 : ℝ) ≤ τ.val)
    (t : ℝ) (x : M) :
    sourceCanonicalTestInput θ u τ x + ((t * τ.val : ℝ) : EReal) =
      rawCanonicalAffine (u x) (sourceMinimalEnvelope θ x) t τ.val := by
  have hcoef : sourceCanonicalTestCoefficient τ.val = 1 + τ.val :=
    max_eq_left (by linarith)
  simp only [sourceCanonicalTestInput, hcoef, convexComb, rawCanonicalAffine,
    show 1 - (1 + τ.val) = -τ.val by ring]

private theorem canonicalInput_thetaPSH (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (τ : Iio (0 : ℝ)) :
    (ofFixedModel n M).IsThetaPSH θ (sourceCanonicalTestInput θ u τ) := by
  have hw := sourceCanonicalTestCoefficient_weights τ.property
  by_cases hz : sourceCanonicalTestCoefficient τ.val = 0
  · change (ofFixedModel n M).IsThetaPSH θ (fun x =>
      ((sourceCanonicalTestCoefficient τ.val : ℝ) : EReal) * u x +
        ((1 - sourceCanonicalTestCoefficient τ.val : ℝ) : EReal) * sourceMinimalEnvelope θ x)
    simpa only [hz, EReal.coe_zero, zero_mul,
      sub_zero, EReal.coe_one, one_mul, zero_add] using sourceMinimalEnvelope_thetaPSH ω θ hbig
  · apply (isThetaPSH_iff_nativeThetaPotential θ _).mpr
    exact isThetaPshPotential_convexComb
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceMinimalEnvelope_thetaPSH ω θ hbig))
      (lt_of_le_of_ne hw.1 (Ne.symm hz)) hw.2

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem canonicalInput_nonpositive {u : M → EReal} (hu0 : u ≤ 0)
    (τ : Iio (0 : ℝ)) : sourceCanonicalTestInput θ u τ ≤ 0 := by
  have hw := sourceCanonicalTestCoefficient_weights τ.property
  intro x
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr hw.1) (hu0 x))
    (mul_nonpos_of_nonneg_of_nonpos (EReal.coe_nonneg.mpr (sub_nonneg.mpr hw.2.le))
      (sourceMinimalEnvelope_le_zero θ x))

/-- The original ordinary envelope dominates the actual original canonical
input, with genuine PSH and nonpositivity internally produced. -/
theorem sourceCanonicalInput_le_potential (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (τ : Iio (0 : ℝ)) :
    sourceCanonicalTestInput θ u τ ≤ sourceCanonicalTestPotential θ u τ :=
  le_sourceSingularityEnvelope (canonicalInput_thetaPSH ω hbig hu τ)
    (canonicalInput_nonpositive hu0 τ) (MoreSingularOn.refl _ univ)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Literal inclusion of every actual original real-horizon stage into its
defined neighborhood-USC supremum, at the same original time. -/
theorem sourceAssociatedStage_le_cutoffRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (t : Ici (0 : ℝ)) {C : ℝ} (hC : t.val < C) :
    sourceAssociatedRayStage ω θ u C t.val ≤ sourceAssociatedCutoffRay ω θ u t := by
  intro x
  change sourceAssociatedRayStage ω θ u C t.val x ≤
    uscRegularization (fun y => ⨆ D : {D : ℝ // t.val < D},
      sourceAssociatedRayStage ω θ u D.val t.val y) x
  exact (le_iSup (fun D : {D : ℝ // t.val < D} =>
    sourceAssociatedRayStage ω θ u D.val t.val x) ⟨C, hC⟩).trans
      (le_uscRegularization (fun y => ⨆ D : {D : ℝ // t.val < D},
        sourceAssociatedRayStage ω θ u D.val t.val y) x)

/-- The actual canonical raw transform dominates the actual cutoff at every
real time. The slope −1 is retained, including at a pole of u. -/
theorem sourceCanonicalRawLegendre_cutoff_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (t : ℝ) (x : M) :
    max (u x) (sourceMinimalEnvelope θ x - (t : EReal)) ≤
      sourceTestCurveRawLegendre (sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata t x := by
  rw [(sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata.rawLegendre_eq_iSup_open]
  have hVt : sourceMinimalEnvelope θ x ≠ ⊤ :=
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceMinimalEnvelope_thetaPSH ω θ hbig)).quasiPshPotential.1.ne_top x
  rw [← rawCanonicalAffine_iSup_closed_left (sourceAssociatedInput_le_minimal hu hu0 x)
    hVt t]
  apply iSup_le
  intro τ
  let σ : Iio (0 : ℝ) := ⟨τ.val, τ.property.2⟩
  have hin := sourceCanonicalInput_le_potential ω hbig hu hu0 σ x
  have hdom := add_le_add hin (le_rfl : ((t * τ.val : ℝ) : EReal) ≤ ((t * τ.val : ℝ) : EReal))
  rw [canonicalInput_add_linear_eq_raw u σ τ.property.1 t x] at hdom
  exact hdom.trans (by
    simpa only [sourceCanonicalTestCurve, sourceCanonicalTestCurvePredata, σ, add_comm] using
      le_iSup (fun s : Iio (0 : ℝ) =>
        ((t * s.val : ℝ) : EReal) + sourceCanonicalTestPotential θ u s x) σ)

/-- Every ACTUAL original ordinary-envelope competitor gives an affine
Perron competitor at every real horizon. Its finite singularity error is
removed internally by the positive-right limit; no ray-order certificate. -/
theorem sourceCanonicalCompetitor_le_associatedCutoff (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (τ : Iio (0 : ℝ)) (hτ : -1 < τ.val)
    (w : sourceSingularityCompetitors θ (sourceCanonicalTestInput θ u τ))
    (t : Ici (0 : ℝ)) :
    (fun x => w.val x + ((t.val * τ.val : ℝ) : EReal)) ≤
      sourceAssociatedCutoffRay ω θ u t := by
  have hwV : w.val ≤ sourceMinimalEnvelope θ :=
    sourceAssociatedInput_le_minimal w.property.1 w.property.2.1
  have hut : ∀ y, u y ≠ ⊤ :=
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu).quasiPshPotential.1.ne_top
  have hVt : ∀ y, sourceMinimalEnvelope θ y ≠ ⊤ :=
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp
      (sourceMinimalEnvelope_thetaPSH ω θ hbig)).quasiPshPotential.1.ne_top
  have hR := sourceAssociatedCutoffRay_mem_boundedRays ω θ hbig hu hu0
  by_cases ht0 : t.val = 0
  · have ht : t = (⟨0, by simp⟩ : Ici (0 : ℝ)) := Subtype.ext ht0
    rw [ht, hR.2]
    simpa only [zero_mul, EReal.coe_zero, add_zero] using hwV
  have ht : 0 < t.val := lt_of_le_of_ne t.property (Ne.symm ht0)
  obtain ⟨D, hD⟩ := w.property.2.2
  intro x
  have htime (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      w.val x + ((t.val * τ.val - D * s : ℝ) : EReal) ≤
        sourceAssociatedCutoffRay ω θ u t x := by
    let C : ℝ := t.val / s
    have hC : 0 < C := div_pos ht hs.1
    have htC : t.val < C := (lt_div_iff₀ hs.1).mpr (by nlinarith [hs.2])
    have hterminal (y : M) :
        w.val y + ((C * τ.val - D : ℝ) : EReal) ≤ sourceAssociatedCutoff θ u C y := by
      calc
        w.val y + ((C * τ.val - D : ℝ) : EReal) ≤
            (sourceCanonicalTestInput θ u τ y + (D : EReal)) +
              ((C * τ.val - D : ℝ) : EReal) := add_le_add (hD y (mem_univ y)) le_rfl
        _ = sourceCanonicalTestInput θ u τ y + ((C * τ.val : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
          congr 2
          ring
        _ = rawCanonicalAffine (u y) (sourceMinimalEnvelope θ y) C τ.val :=
          canonicalInput_add_linear_eq_raw u τ hτ.le C y
        _ ≤ sourceAssociatedCutoff θ u C y :=
          rawCanonicalAffine_le_max (hut y) (hVt y) C ⟨hτ.le, τ.property⟩
    have hc : (fun r : ℝ => fun y => w.val y + ((r * (C * τ.val - D) : ℝ) : EReal)) ∈
        sourcePerronCompetitors ω θ (sourceMinimalEnvelope θ) (sourceAssociatedCutoff θ u C) :=
      ⟨w.val, (fun y => w.val y + ((C * τ.val - D : ℝ) : EReal)), w.property.1,
        sourceThetaPSH_add_const w.property.1 (C * τ.val - D), hwV, hterminal,
        sourceSubgeodesic_affine ω w.property.1 (C * τ.val - D)⟩
    have hstage := sourcePerron_competitor_le hc s x
    have hratio : t.val / C = s := by dsimp only [C]; field_simp [hs.1.ne', ht.ne']
    have hcoeff : s * (C * τ.val - D) = t.val * τ.val - D * s := by
      dsimp only [C]
      field_simp [hs.1.ne']
    have hst : sourcePerronGeodesic ω θ (sourceMinimalEnvelope θ)
        (sourceAssociatedCutoff θ u C) s = sourceAssociatedRayStage ω θ u C t.val := by
      rw [sourceAssociatedRayStage, hratio, sourcePerronClosedSlice,
        closedSubgeodesicSlice_eq_curve hs]
    rw [hcoeff, hst] at hstage
    exact hstage.trans (sourceAssociatedStage_le_cutoffRay ω θ u t htC x)
  have hc : Continuous (fun s : ℝ => ((t.val * τ.val - D * s : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  have hscalar : Tendsto (fun s : ℝ => ((t.val * τ.val - D * s : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 ((t.val * τ.val : ℝ) : EReal)) := by
    simpa only [mul_zero, sub_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hadd : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (w.val x, ((t.val * τ.val : ℝ) : EReal)) :=
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  apply le_of_tendsto (hadd.tendsto.comp (tendsto_const_nhds.prodMk_nhds hscalar))
  filter_upwards [sourceRay_endpoint_filters.1] with s hs
  exact htime s hs

/-- Actual envelope regularization preserves the internally proved affine
competitor bound, including every original pole. -/
theorem sourceCanonicalPotential_le_associatedCutoff (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (τ : Iio (0 : ℝ)) (hτ : -1 < τ.val) (t : Ici (0 : ℝ)) :
    (fun x => sourceCanonicalTestPotential θ u τ x + ((t.val * τ.val : ℝ) : EReal)) ≤
      sourceAssociatedCutoffRay ω θ u t := by
  have hR := sourceAssociatedCutoffRay_mem_boundedRays ω θ hbig hu hu0
  have hPSH := sourceThetaPSH_add_const (hR.1.1.1 t).choose (-(t.val * τ.val))
  have hUSC : UpperSemicontinuous (fun x =>
      sourceAssociatedCutoffRay ω θ u t x - ((t.val * τ.val : ℝ) : EReal)) := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hPSH).quasiPshPotential.1.upperSemicontinuous
  have henv : sourceCanonicalTestPotential θ u τ ≤ fun x =>
      sourceAssociatedCutoffRay ω θ u t x - ((t.val * τ.val : ℝ) : EReal) := by
    apply uscRegularization_le hUSC
    intro x
    apply iSup_le
    intro w
    exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
      (Or.inl (EReal.coe_ne_top _))).mpr
      (sourceCanonicalCompetitor_le_associatedCutoff ω hbig hu hu0 τ hτ w t x)
  intro x
  exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _))).mp (henv x)

end SGPT.PSH.VariableComplexAtlas

end

/-! # Whole original canonical-curve/associated-ray equality

The original open-interval raw proof is repaired using the actual slope −1
branch. Actual Perron order proves equality internally; the already genuine
energy formulas then identify the original canonical test-curve energy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem assignedLegendre_zero (Γ : SourceTestCurvePredata θ) :
    sourceTestCurveLegendreRay Γ (⟨0, by simp⟩ : Ici (0 : ℝ)) = sourceTestCurveLimit Γ := by
  change (if (0 : ℝ) = 0 then sourceTestCurveLimit Γ else sourceTestCurveRawLegendre Γ 0) = _
  exact if_pos rfl

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem assignedLegendre_eq_raw (Γ : SourceTestCurvePredata θ)
    (t : Ici (0 : ℝ)) (ht : t.val ≠ 0) :
    sourceTestCurveLegendreRay Γ t = sourceTestCurveRawLegendre Γ t.val := by
  change (if t.val = 0 then sourceTestCurveLimit Γ else sourceTestCurveRawLegendre Γ t.val) = _
  exact if_neg ht

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem extendedLegendre_eq_raw (Γ : SourceTestCurvePredata θ)
    {t : ℝ} (ht : 0 < t) :
    sourceRayExtension (sourceTestCurveLegendreRay Γ) t = sourceTestCurveRawLegendre Γ t := by
  rw [sourceRayExtension_nonneg _ t ht.le]
  exact assignedLegendre_eq_raw Γ ⟨t, ht.le⟩ ht.ne'

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem nativeCutoffStage_eq_identicalJoin
    (η : ClosedRealOneOneForm n M) (φ v : M → EReal) (C t : ℝ) :
    SingularCanonicalCutoffStages.cutoffStage η φ v C t =
      SingularBoundedRayJoinStages.joinStage η φ
        (fun s => SingularModelNormalizedMixedCutoff.realCutoff φ v s)
        (fun s => SingularModelNormalizedMixedCutoff.realCutoff φ v s) C t := by
  simp only [SingularCanonicalCutoffStages.cutoffStage,
    SingularBoundedRayJoinStages.joinStage, max_self]

/-- The actual original associated cutoff ray dominates its whole original
maximum barrier at every assigned time, including every pole. -/
theorem sourceAssociatedCutoffRay_cutoff_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (t : Ici (0 : ℝ)) :
    sourceAssociatedCutoff θ u t.val ≤ sourceAssociatedCutoffRay ω θ u t := by
  have hUV : u ≤ sourceMinimalEnvelope θ := sourceAssociatedInput_le_minimal hu hu0
  have h := (SingularCanonicalCutoffSlices.cutoffSlice_bounds
    ((sourceMinimalEnvelope_model ω θ hbig).toNative.plurisubharmonic)
    ((isThetaPSH_iff_nativeThetaPotential (n := n) (M := M) θ _).mp hu) hUV t.property).1
  have heq := congrFun (sourceAssociatedCutoffRay_extension_eq_native ω θ u) t.val
  rw [sourceRayExtension_nonneg _ t.val t.property] at heq
  simpa only [sourceAssociatedCutoff_eq_native, heq, sourceMinimalEnvelope_eq_native (n := n) (M := M) θ] using h

/-- Actual ordinary-envelope competitors and the genuine slope −1 branch
give the whole original ray order, with no inverse-cutoff certificate. -/
theorem sourceCanonicalLegendreRay_le_associatedCutoff (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    SourceRayLE
      (sourceTestCurveLegendreRay (sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata)
      (sourceAssociatedCutoffRay ω θ u) := by
  let Γ := sourceCanonicalTestCurve ω θ hbig u hu
  have hΓ := sourceCanonicalTestCurve_mem_bounded ω θ hbig u hu
  have hG := (source_test_curve_legendre_geodesic_whole ω Γ hΓ.1).1
  have hA := sourceAssociatedCutoffRay_mem_boundedRays ω θ hbig hu hu0
  intro t
  by_cases ht0 : t.val = 0
  · have ht : t = (⟨0, by simp⟩ : Ici (0 : ℝ)) := Subtype.ext ht0
    rw [ht, hG.2, hA.2]
  intro x
  rw [assignedLegendre_eq_raw Γ.toSourceTestCurvePredata t ht0]
  rw [Γ.toSourceTestCurvePredata.rawLegendre_eq_iSup_open]
  change (⨆ τ : Iio (0 : ℝ), ((t.val * τ.val : ℝ) : EReal) +
    sourceCanonicalTestPotential θ u τ x) ≤ sourceAssociatedCutoffRay ω θ u t x
  apply iSup_le
  intro τ
  by_cases hτ : -1 < τ.val
  · simpa only [add_comm] using
      sourceCanonicalPotential_le_associatedCutoff ω hbig hu hu0 τ hτ t x
  have hτ' : τ.val ≤ -1 := le_of_not_gt hτ
  rw [sourceCanonicalTestPotential_of_le_neg_one ω hbig u τ hτ']
  have hb := sourceAssociatedCutoffRay_cutoff_le ω hbig hu hu0 t x
  calc
    ((t.val * τ.val : ℝ) : EReal) + sourceMinimalEnvelope θ x ≤
        ((-t.val : ℝ) : EReal) + sourceMinimalEnvelope θ x :=
      add_le_add (EReal.coe_le_coe_iff.mpr (by
        simpa only [mul_neg_one] using mul_le_mul_of_nonneg_left hτ' t.property)) le_rfl
    _ = sourceMinimalEnvelope θ x - (t.val : EReal) := by
      simp only [sub_eq_add_neg, EReal.coe_neg, add_comm]
    _ ≤ sourceAssociatedCutoffRay ω θ u t x := (le_max_right _ _).trans hb

/-- Every actual original stage is dominated by the canonical Legendre ray
via its actual terminal cutoff bound and genuine finite Perron geometry. -/
theorem sourceAssociatedCutoffRay_le_canonicalLegendre (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    SourceRayLE (sourceAssociatedCutoffRay ω θ u)
      (sourceTestCurveLegendreRay (sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata) := by
  let Γ := sourceCanonicalTestCurve ω θ hbig u hu
  let R := sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata
  let hV := sourceMinimalEnvelope_model ω θ hbig
  have hΓ := sourceCanonicalTestCurve_mem_bounded ω θ hbig u hu
  have hR := (source_test_curve_legendre_geodesic_whole ω Γ hΓ.1).1
  have hNative := (mem_sourceGeodesicRays_iff_native ω θ _ hV R).mp hR
  intro t
  have hPSH := (hR.1.1 t).choose
  have hUSC := ((isThetaPSH_iff_nativeThetaPotential (n := n) (M := M) θ _).mp hPSH).quasiPshPotential.1.upperSemicontinuous
  apply uscRegularization_le hUSC
  intro x
  apply iSup_le
  intro C
  have hC : 0 < C.val := lt_of_le_of_lt t.property C.property
  have hcut : SingularModelNormalizedMixedCutoff.realCutoff (sourceMinimalEnvelope θ) u C.val ≤
      sourceRayExtension R C.val := by
    intro y
    have hlower := sourceCanonicalRawLegendre_cutoff_le ω hbig hu hu0 C.val y
    change max (u y) (sourceMinimalEnvelope θ y - (C.val : EReal)) ≤
      sourceRayExtension (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata) C.val y
    rw [extendedLegendre_eq_raw Γ.toSourceTestCurvePredata hC]
    exact hlower
  have hs := SingularBoundedRayJoinStageOrder.joinStage_le_upperRay
    (ℓ := fun s => SingularModelNormalizedMixedCutoff.realCutoff (sourceMinimalEnvelope θ) u s)
    (ℓ' := fun s => SingularModelNormalizedMixedCutoff.realCutoff (sourceMinimalEnvelope θ) u s)
    hNative hC ⟨t.property, C.property.le⟩ hcut hcut
  have hstage : sourceAssociatedRayStage ω θ u C.val t.val =
      SingularCanonicalCutoffStages.cutoffStage (atlasClosedFormToNative θ)
        (sourceMinimalEnvelope θ) u C.val t.val :=
    (sourceAssociatedRayStage_eq_native ω θ u C.val t.val).trans
      (congrArg (fun v : M → EReal => SingularCanonicalCutoffStages.cutoffStage
        (atlasClosedFormToNative θ) v u C.val t.val) (sourceMinimalEnvelope_eq_native (n := n) (M := M) θ).symm)
  have hjoin := nativeCutoffStage_eq_identicalJoin (n := n) (M := M) (atlasClosedFormToNative θ)
    (sourceMinimalEnvelope θ) u C.val t.val
  have hval : sourceAssociatedRayStage ω θ u C.val t.val x ≤ sourceRayExtension R t.val x :=
    (congrFun (hstage.trans hjoin) x).le.trans (hs x)
  exact hval.trans_eq (congrFun (sourceRayExtension_nonneg R t.val t.property) x)

/-- Actual finite-constant invariance of the original Legendre ray follows
pointwise from the original canonical potential family and its exact limit.
No dependent whole-object normalization or ray-equality input is used. -/
theorem sourceCanonicalLegendreRay_add_const_eq (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ) :
    sourceTestCurveLegendreRay
      (sourceCanonicalTestCurve ω θ hbig (fun x => u x + (c : EReal))
        (sourceThetaPSH_add_const (n := n) (M := M) (θ := θ) hu c)).toSourceTestCurvePredata =
      sourceTestCurveLegendreRay (sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata := by
  let Γc := sourceCanonicalTestCurve ω θ hbig (fun x => u x + (c : EReal))
    (sourceThetaPSH_add_const (n := n) (M := M) (θ := θ) hu c)
  let Γ := sourceCanonicalTestCurve ω θ hbig u hu
  funext t
  by_cases ht0 : t.val = 0
  · have ht : t = (⟨0, by simp⟩ : Ici (0 : ℝ)) := Subtype.ext ht0
    rw [ht, assignedLegendre_zero, assignedLegendre_zero]
    exact (sourceCanonicalTestCurve_limit_eq ω θ hbig _
      (sourceThetaPSH_add_const (n := n) (M := M) (θ := θ) hu c)).trans
        (sourceCanonicalTestCurve_limit_eq ω θ hbig u hu).symm
  rw [assignedLegendre_eq_raw Γc.toSourceTestCurvePredata t ht0,
    assignedLegendre_eq_raw Γ.toSourceTestCurvePredata t ht0]
  funext x
  rw [Γc.toSourceTestCurvePredata.rawLegendre_eq_iSup_open,
    Γ.toSourceTestCurvePredata.rawLegendre_eq_iSup_open]
  change (⨆ τ : Iio (0 : ℝ), ((t.val * τ.val : ℝ) : EReal) +
    sourceCanonicalTestPotential θ (fun y => u y + (c : EReal)) τ x) =
    (⨆ τ : Iio (0 : ℝ), ((t.val * τ.val : ℝ) : EReal) + sourceCanonicalTestPotential θ u τ x)
  rw [sourceCanonicalTestPotential_add_const_eq (n := n) (M := M) (θ := θ) u c]

/-- WHOLE original main equation eq:RWNsingtype: identical actual rays for
every genuine input, original zero mass, every pole, and all natural n.
Order and equality are produced from actual Perron competitors internally. -/
theorem sourceCanonicalAssociatedRay_eq (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceAssociatedRay ω θ u =
      sourceTestCurveLegendreRay (sourceCanonicalTestCurve ω θ hbig u hu).toSourceTestCurvePredata := by
  have normalized {v : M → EReal} (hv : (ofFixedModel n M).IsThetaPSH θ v) (hv0 : v ≤ 0) :
      sourceAssociatedRay ω θ v =
        sourceTestCurveLegendreRay (sourceCanonicalTestCurve ω θ hbig v hv).toSourceTestCurvePredata := by
    apply (sourceAssociatedRay_eq_cutoff_of_nonpositive ω θ hbig hv hv0).trans
    funext t x
    exact le_antisymm (sourceAssociatedCutoffRay_le_canonicalLegendre ω hbig hv hv0 t x)
      (sourceCanonicalLegendreRay_le_associatedCutoff ω hbig hv hv0 t x)
  obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential (n := n) (M := M) θ u).mp hu).exists_normalized_sub_const
  have hv : (ofFixedModel n M).IsThetaPSH θ (fun x => u x + ((-C : ℝ) : EReal)) :=
    sourceThetaPSH_add_const (n := n) (M := M) (θ := θ) hu (-C)
  have hv0 : (fun x => u x + ((-C : ℝ) : EReal)) ≤ 0 := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using hC.2
  have h := normalized hv hv0
  have hAssoc : sourceAssociatedRay ω θ (fun x => u x + ((-C : ℝ) : EReal)) =
      sourceAssociatedRay ω θ u := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using sourceAssociatedRay_sub_const_eq ω θ hu C
  exact hAssoc.symm.trans (h.trans (sourceCanonicalLegendreRay_add_const_eq ω hbig hu (-C)))

/-- The corrected all-point lower barrier of the original proof, after its
explicit nonpositive normalization. No open-interval supremum is asserted. -/
theorem sourceAssociatedRay_cutoff_le (ω : KahlerBackground n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (t : Ici (0 : ℝ)) : sourceAssociatedCutoff θ u t.val ≤ sourceAssociatedRay ω θ u t := by
  rw [sourceAssociatedRay_eq_cutoff_of_nonpositive ω θ hbig hu hu0]
  exact sourceAssociatedCutoffRay_cutoff_le ω hbig hu hu0 t

/-- The actual original canonical test-curve energy is the original
unnormalized mixed-mass deficit. Actual boundedness and equality of actual
rays produce this formula; no energy-equality input or mass restriction. -/
theorem sourceCanonicalTestCurveEnergy_eq_mixedMassDeficit (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceTestCurveEnergy ω (sourceMinimalEnvelope_model ω θ hbig)
      (sourceCanonicalTestCurve ω θ hbig u hu)
      (sourceCanonicalTestCurve_mem_bounded ω θ hbig u hu).1 =
      (((∑ j : Fin (n + 1), ((sourceMinimalMixedMass ω θ hbig u hu j).toReal -
        (sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
          (sourceMinimalEnvelope_thetaPSH ω θ hbig) univ).toReal)) / (n + 1 : ℝ) : ℝ) : EReal) := by
  let Γ := sourceCanonicalTestCurve ω θ hbig u hu
  have hb := sourceCanonicalTestCurve_mem_bounded ω θ hbig u hu
  have hE := (Γ.boundedEnergy_finite_all_cutoffs ω hb).1
  have hL := (source_test_curve_legendre_geodesic_whole ω Γ hb.1).1
  have hsame : (⟨sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata, hL⟩ :
      SourceGeodesicRay ω θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig)) =
      sourceBoundedRayToGeodesicRay ω (sourceAssociatedBoundedRay ω θ hbig hu) :=
    Subtype.ext (sourceCanonicalAssociatedRay_eq ω θ hbig hu).symm
  have hid := source_test_curve_legendre_radial_energy_identity ω Γ hb.1 hE
  exact hid.trans ((congrArg (sourceRadialEnergy ω) hsame).trans
    (sourceAssociatedRay_radialEnergy_eq_mixed_mass_deficit ω θ hbig hu))

end SGPT.PSH.VariableComplexAtlas

end
