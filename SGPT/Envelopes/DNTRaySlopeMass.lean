import SGPT.Envelopes.DNTEnvelopes
import SGPT.PSH.SourceRayLegendreTestCurve
import SGPT.PSH.SourceSubgeodesicConvexity

/-!
# Hisamoto's mass formula for the Legendre transform of a geodesic ray

Source `prop:His_mass_tc` (chapter_testcurve): for a relative geodesic ray `ℓ ∈ R(X, θ; φ)`
emanating from the model potential `φ`, and `τ < ℓ*_max`,

  `∫_X (θ + ddᶜℓ*_τ)ⁿ = ∫_{\{ℓ̇₀ ≥ τ\}} θ_φⁿ`,

where `ℓ*_τ = inf_{t>0} (ℓ_t - tτ)` is the Legendre transform (`sourcePositiveRayInverse`) and `ℓ̇₀`
is the right derivative of `t ↦ ℓ_t` at `t = 0`, defined quasi-everywhere.

* `sourceRayQuotient ℓ x t = (ℓ_t(x) - ℓ_0(x))/t`, `sourceRayRightSlope ℓ x` = its infimum over
  `t > 0`.
* `sourceRayQuotient_mono`: for a subgeodesic ray and `ℓ_0(x)` finite, the difference quotient is
  nondecreasing on `t > 0` (the chord inequality of the closed segment `[0, t]`, endpoint included);
  `tendsto_sourceRayQuotient`, `sourceRayRightSlope_isRightDerivative_qe`: hence the right
  derivative `ℓ̇₀(x)` exists in `[-∞, ∞]` and equals `sourceRayRightSlope ℓ x` wherever `φ(x)` is
  finite, i.e. quasi-everywhere.
* `le_slope_iff_inverse_eq`: at such points `ℓ̇₀(x) ≥ τ ⟺ ℓ*_τ(x) = φ(x)` (the book's
  `eq:dotell_temp1`).
* `sourceRay_legendre_mass_eq` (`prop:His_mass_tc`): the formula, for every function `D` that is
  the right derivative quasi-everywhere (so the statement does not depend on the choice of `ℓ̇₀` on
  a pluripolar set), and `sourceRay_legendre_mass_eq_rightSlope` for `D = sourceRayRightSlope ℓ`.

The proof is the book's: `θⁿ_{ℓ*_τ} = 𝟙_{ℓ*_τ = 0} θⁿ` and `θ_φⁿ = 𝟙_{φ = 0} θⁿ` because both are
model potentials (`prop:DNTenvelope2`, proved as
`TranscendentalWNReg.sourceSingularityEnvelope_measure_eq`), `ℓ*_τ ≤ φ ≤ 0`, and
`{ℓ̇₀ ≥ τ} = {ℓ*_τ = φ}` outside the pluripolar set `{φ = -∞}`, which `θ_φⁿ` does not charge.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNT

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Difference quotients at `t = 0` -/

/-- The difference quotient `(ℓ_t(x) - ℓ_0(x))/t` of a ray (extended-real valued). -/
def sourceRayQuotient (ℓ : SourceRayFamily M) (x : M) (t : ℝ) : EReal :=
  ((t⁻¹ : ℝ) : EReal) * (sourceRayExtension ℓ t x - ℓ ⟨0, self_mem_Ici⟩ x)

/-- The right slope `ℓ̇₀(x) = inf_{t>0} (ℓ_t(x) - ℓ_0(x))/t`; it is the right derivative of
`t ↦ ℓ_t(x)` at `0` wherever `ℓ_0(x)` is finite (`tendsto_sourceRayQuotient`). -/
def sourceRayRightSlope (ℓ : SourceRayFamily M) (x : M) : EReal :=
  sInf (sourceRayQuotient ℓ x '' Ioi 0)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `τ ≤ (y - a)/t ⟺ a ≤ y - tτ` in `[-∞, ∞]`, for real `a`, `τ` and `t > 0`. -/
theorem coe_le_inv_mul_sub_iff {a τ t : ℝ} (ht : 0 < t) (y : EReal) :
    (τ : EReal) ≤ ((t⁻¹ : ℝ) : EReal) * (y - (a : EReal)) ↔
      (a : EReal) ≤ y - ((t * τ : ℝ) : EReal) := by
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  induction y using EReal.rec with
  | bot =>
    simp only [EReal.bot_sub, EReal.coe_mul_bot_of_pos hti, le_bot_iff, EReal.coe_ne_bot]
  | top =>
    simp only [EReal.top_sub_coe, EReal.coe_mul_top_of_pos hti, le_top]
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff,
      EReal.coe_le_coe_iff, le_inv_mul_iff₀ ht]
    constructor <;> intro h <;> linarith

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The chord inequality at the initial time**: for a subgeodesic ray and `0 < s < t`,
`ℓ_s ≤ (1 - s/t) ℓ_0 + (s/t) ℓ_t`. -/
theorem sourceRay_le_chord_zero {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (hsub : SourceIsSubgeodesicRay omega θ ℓ) {s t : ℝ} (hs : 0 < s) (hst : s < t) (x : M) :
    sourceRayExtension ℓ s x ≤
      eRealChord (ℓ ⟨0, self_mem_Ici⟩ x) (sourceRayExtension ℓ t x) (s / t) := by
  have ht : 0 < t := hs.trans hst
  have hseg := (hsub 0 t le_rfl ht.le).2
  have hst1 : s / t ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hs ht, (div_lt_one ht).mpr hst⟩
  have hc := hseg.le_closedChord (a := 0) (b := 1) le_rfl le_rfl zero_lt_one
    ⟨hst1.1.le, hst1.2.le⟩ x
  rw [show (1 - s / t) * 0 + s / t * 1 = s / t by ring, closedSubgeodesicSlice_zero,
    closedSubgeodesicSlice_one, closedSubgeodesicSlice_eq_curve hst1] at hc
  have e1 : s / t * t + (1 - s / t) * 0 = s := by rw [mul_zero, add_zero, div_mul_cancel₀ s ht.ne']
  rw [e1, sourceRayExtension_nonneg ℓ 0 le_rfl] at hc
  exact hc

/-- **Monotonicity of the difference quotients**: for a subgeodesic ray with `ℓ_0(x)` finite,
`t ↦ (ℓ_t(x) - ℓ_0(x))/t` is nondecreasing on `t > 0`. -/
theorem sourceRayQuotient_mono {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (hsub : SourceIsSubgeodesicRay omega θ ℓ) {x : M} {a : ℝ}
    (ha : ℓ ⟨0, self_mem_Ici⟩ x = (a : EReal)) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    sourceRayQuotient ℓ x s ≤ sourceRayQuotient ℓ x t := by
  have ht : 0 < t := hs.trans hst
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  have hst0 : 0 < s / t := div_pos hs ht
  have hc := sourceRay_le_chord_zero hsub hs hst x
  rw [ha] at hc
  unfold sourceRayQuotient
  rw [ha]
  generalize sourceRayExtension ℓ t x = y at hc ⊢
  generalize sourceRayExtension ℓ s x = z at hc ⊢
  induction y using EReal.rec with
  | bot =>
    have hz : z = ⊥ := by
      apply le_bot_iff.mp
      refine hc.trans_eq ?_
      rw [eRealChord, EReal.coe_mul_bot_of_pos hst0, ← EReal.coe_mul, EReal.add_bot]
    rw [hz, EReal.bot_sub, EReal.coe_mul_bot_of_pos hsi]
    exact bot_le
  | top =>
    rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos hti]
    exact le_top
  | coe r =>
    rw [eRealChord, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
    induction z using EReal.rec with
    | bot =>
      rw [EReal.bot_sub, EReal.coe_mul_bot_of_pos hsi]
      exact bot_le
    | top => exact ((EReal.coe_ne_top _) (top_le_iff.mp hc)).elim
    | coe q =>
      rw [EReal.coe_le_coe_iff] at hc
      rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_mul,
        EReal.coe_le_coe_iff]
      have h1 : q - a ≤ s / t * (r - a) := by
        have : (1 - s / t) * a + s / t * r = a + s / t * (r - a) := by ring
        linarith
      calc s⁻¹ * (q - a) ≤ s⁻¹ * (s / t * (r - a)) := mul_le_mul_of_nonneg_left h1 hsi.le
        _ = t⁻¹ * (r - a) := by field_simp

/-- **The right derivative at `t = 0` exists** in `[-∞, ∞]` wherever `ℓ_0(x)` is finite, and equals
`sourceRayRightSlope ℓ x`. -/
theorem tendsto_sourceRayQuotient {omega : KahlerBackground n M}
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {ℓ : SourceRayFamily M}
    (hsub : SourceIsSubgeodesicRay omega θ ℓ) {x : M} (h0 : ℓ ⟨0, self_mem_Ici⟩ x ≠ ⊥)
    (h0' : ℓ ⟨0, self_mem_Ici⟩ x ≠ ⊤) :
    Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (sourceRayRightSlope ℓ x)) := by
  have ha : ℓ ⟨0, self_mem_Ici⟩ x = (((ℓ ⟨0, self_mem_Ici⟩ x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal h0' h0).symm
  refine MonotoneOn.tendsto_nhdsGT (fun s hs t ht hst => ?_) (OrderBot.bddBelow _)
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact sourceRayQuotient_mono hsub ha hs hlt

/-! ### The pointwise identity `{ℓ̇₀ ≥ τ} = {ℓ*_τ = φ}` -/

variable [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}

/-- `ℓ*_τ ≤ φ` for `τ < ℓ*_max` (the Legendre transform lies below its limit `ℓ*_{-∞} = φ`). -/
theorem sourcePositiveRayInverse_le_model (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ} (hτ : τ < sourceRayLegendreCutoff omega h) :
    sourcePositiveRayInverse ℓ τ ≤ φ := by
  intro x
  have hb : sourceTestCurveLimit (sourceRayLegendreTestCurve omega h).toSourceTestCurvePredata = φ :=
    (source_ray_legendre_test_curve_whole omega h).1
  have hle := (le_iSup (fun σ : Iio (sourceRayLegendreTestCurve omega h).max =>
      (sourceRayLegendreTestCurve omega h).potential σ x) ⟨τ, hτ⟩).trans
    (le_uscRegularization (fun y => ⨆ σ : Iio (sourceRayLegendreTestCurve omega h).max,
      (sourceRayLegendreTestCurve omega h).potential σ y) x)
  exact hle.trans_eq (congrFun hb x)

/-- **The book's `eq:dotell_temp1` at a point**: if `φ(x)` is finite and `d` is the right
derivative of `t ↦ ℓ_t(x)` at `0`, then `d ≥ τ ⟺ ℓ*_τ(x) = φ(x)` (for `τ < ℓ*_max`). -/
theorem le_slope_iff_inverse_eq (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ} (hτ : τ < sourceRayLegendreCutoff omega h)
    {x : M} (hx : φ x ≠ ⊥) {d : EReal}
    (hd : Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 d)) :
    (τ : EReal) ≤ d ↔ sourcePositiveRayInverse ℓ τ x = φ x := by
  have hsub := h.1.isSubgeodesicRay
  have h0 : ℓ ⟨0, self_mem_Ici⟩ = φ := h.2
  have hφ0 : φ x ≤ 0 := by
    rw [hφ.choose_spec.1]
    exact sourceSingularityEnvelope_le_zero θ φ x
  have hxt : φ x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hφ0
  set a : ℝ := (φ x).toReal with hadef
  have ha : φ x = (a : EReal) := (EReal.coe_toReal hxt hx).symm
  have ha0 : ℓ ⟨0, self_mem_Ici⟩ x = (a : EReal) := by rw [h0, ha]
  have hQ : ∀ t : ℝ, 0 < t → ((τ : EReal) ≤ sourceRayQuotient ℓ x t ↔
      φ x ≤ sourceRayExtension ℓ t x - ((t * τ : ℝ) : EReal)) := by
    intro t ht
    unfold sourceRayQuotient
    rw [ha0, ha]
    exact coe_le_inv_mul_sub_iff ht _
  constructor
  · intro hτd
    refine le_antisymm (sourcePositiveRayInverse_le_model omega h hτ x) ?_
    refine le_iInf fun t => ?_
    have ht : 0 < t.1 := t.2
    have hdt : d ≤ sourceRayQuotient ℓ x t.1 := by
      refine le_of_tendsto hd ?_
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs
      exact sourceRayQuotient_mono hsub ha0 hs.1 hs.2
    exact (hQ t.1 ht).mp (hτd.trans hdt)
  · intro heq
    refine ge_of_tendsto hd ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine (hQ t ht).mpr ?_
    rw [← heq]
    exact iInf_le (fun s : Ioi (0 : ℝ) =>
      sourceRayExtension ℓ s.1 x - ((s.1 * τ : ℝ) : EReal)) ⟨t, ht⟩

/-- **`ℓ̇₀` is well-defined quasi-everywhere**: outside the pluripolar set `{φ = -∞}`,
`sourceRayRightSlope ℓ` is the right derivative of `t ↦ ℓ_t` at `0`. -/
theorem sourceRayRightSlope_isRightDerivative_qe (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    SourceQuasiEverywhere (n := n) fun x =>
      Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (sourceRayRightSlope ℓ x)) := by
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH
  have hpole : QuasiEverywhere (n := n) fun x => φ x ≠ ⊥ := by
    have := quasiPsh_poles_manifoldLocallyPluripolar hφn.quasiPshPotential
    simpa only [QuasiEverywhere, ne_eq, not_not] using this
  apply (sourceQuasiEverywhere_iff_native _).mpr
  refine hpole.mono fun x hx => ?_
  have h0 : ℓ ⟨0, self_mem_Ici⟩ = φ := h.2
  have hφ0 : φ x ≤ 0 := by
    rw [hφ.choose_spec.1]
    exact sourceSingularityEnvelope_le_zero θ φ x
  refine tendsto_sourceRayQuotient h.1.isSubgeodesicRay (by rw [h0]; exact hx) ?_
  rw [h0]
  exact ne_top_of_le_ne_top EReal.zero_ne_top hφ0

/-! ### Hisamoto's formula -/

/-- **`prop:His_mass_tc` (Hisamoto)**: for `ℓ ∈ R(X, θ; φ)`, `τ < ℓ*_max` and any `D` which is the
right derivative `ℓ̇₀` of `t ↦ ℓ_t` at `0` quasi-everywhere,
`∫_X (θ + ddᶜℓ*_τ)ⁿ = ∫_{\{ℓ̇₀ ≥ τ\}} θ_φⁿ`. -/
theorem sourceRay_legendre_mass_eq (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ} (hτ : τ < sourceRayLegendreCutoff omega h)
    {D : M → EReal}
    (hD : SourceQuasiEverywhere (n := n) fun x =>
      Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (D x))) :
    sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ)
        (sourceRayLegendre_inverse_thetaPSH omega h hτ.le) univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH {x | (τ : EReal) ≤ D x} := by
  set ψ := sourcePositiveRayInverse ℓ τ with hψdef
  have hψ : (ofFixedModel n M).IsThetaPSH θ ψ := sourceRayLegendre_inverse_thetaPSH omega h hτ.le
  have hψfix : sourceSingularityEnvelope θ ψ = ψ := sourceRayLegendre_inverse_fixedPoint omega h hτ.le
  have hφfix : φ = sourceSingularityEnvelope θ φ := hφ.choose_spec.1
  have hψφ : ψ ≤ φ := sourcePositiveRayInverse_le_model omega h hτ
  have hφ0 : φ ≤ 0 := fun x => by
    rw [hφfix]
    exact sourceSingularityEnvelope_le_zero θ φ x
  -- the two model measures
  have hmψ : sourcePotentialNonPluripolarMeasure θ ψ hψ =
      (positiveTopMeasure omega (atlasClosedFormToNative θ)).restrict {x | ψ x = 0} := by
    rw [sourcePotentialNonPluripolarMeasure_congr hψ (sourceOrdinaryEnvelope_genuine hψ)
      hψfix.symm, sourceSingularityEnvelope_measure_eq omega θ hψ, hψfix]
  have hmφ : sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH =
      (positiveTopMeasure omega (atlasClosedFormToNative θ)).restrict {x | φ x = 0} := by
    rw [sourcePotentialNonPluripolarMeasure_congr hφ.thetaPSH
      (sourceOrdinaryEnvelope_genuine hφ.thetaPSH) hφfix,
      sourceSingularityEnvelope_measure_eq omega θ hφ.thetaPSH, ← hφfix]
  have hφm : MeasurableSet {x | φ x = 0} :=
    hφ.thetaPSH.upperSemicontinuous.measurable (measurableSet_singleton 0)
  -- the pointwise identity holds `θ_φⁿ`-almost everywhere
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH
  have hnc : DoesNotChargeManifoldPluripolar (n := n)
      (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (θ := fun _ : Fin n => atlasClosedFormToNative θ) (u := fun _ => φ) (fun _ => hφn.1)
  have hpole : QuasiEverywhere (n := n) fun x => φ x ≠ ⊥ := by
    have := quasiPsh_poles_manifoldLocallyPluripolar hφn.quasiPshPotential
    simpa only [QuasiEverywhere, ne_eq, not_not] using this
  have hae : {x | (τ : EReal) ≤ D x} =ᵐ[sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH]
      {x | ψ x = φ x} := by
    refine Filter.eventuallyEq_set.mpr ?_
    filter_upwards [hnc.ae_of_quasiEverywhere ((sourceQuasiEverywhere_iff_native _).mp hD),
      hnc.ae_of_quasiEverywhere hpole] with x hx1 hx2
    exact le_slope_iff_inverse_eq omega h hτ hx2 hx1
  rw [measure_congr hae, hmφ, Measure.restrict_apply' hφm, hmψ, Measure.restrict_apply
    MeasurableSet.univ, univ_inter]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro hx
    have h1 : (0 : EReal) ≤ φ x := hx.symm.trans_le (hψφ x)
    exact ⟨hx.trans (le_antisymm (hφ0 x) h1).symm, le_antisymm (hφ0 x) h1⟩
  · rintro ⟨h1, h2⟩
    exact h1.trans h2

/-- **`prop:His_mass_tc`** with `ℓ̇₀ = sourceRayRightSlope ℓ = inf_{t>0} (ℓ_t - φ)/t`:
`∫_X (θ + ddᶜℓ*_τ)ⁿ = ∫_{\{ℓ̇₀ ≥ τ\}} θ_φⁿ`. -/
theorem sourceRay_legendre_mass_eq_rightSlope (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ} (hτ : τ < sourceRayLegendreCutoff omega h) :
    sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ)
        (sourceRayLegendre_inverse_thetaPSH omega h hτ.le) univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH
        {x | (τ : EReal) ≤ sourceRayRightSlope ℓ x} :=
  sourceRay_legendre_mass_eq omega h hτ (sourceRayRightSlope_isRightDerivative_qe omega h)

end SGPT.Envelopes.DNT
