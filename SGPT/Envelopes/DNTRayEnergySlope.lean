import SGPT.Envelopes.DNTRaySlopeMass
import SGPT.PSH.SourceTestCurveFiniteEnergyCorrespondence
import SGPT.PSH.SourceGeodesicEnergyAffinity
import SGPT.PSH.SourceRadialDarvasMetric
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The energy of a finite-energy ray is the integral of its initial slope

Source `cor:ray_energy_slope` (chapter_testcurve): for a finite-energy relative geodesic ray
`ℓ ∈ R¹(X, θ; φ)`, the right derivative `ℓ̇₀` at `t = 0` lies in `L¹(X, θ_φⁿ)` and

  `E^φ(ℓ) = ∫_X ℓ̇₀ θ_φⁿ`.

* `le_inverse_of_le_slope`, `slope_le_cutoff`: `ℓ̇₀ ≥ τ` forces `ℓ*_τ ≥ φ`; hence `ℓ̇₀ ≤ ℓ*_max`
  wherever `φ` is finite (for `τ > ℓ*_max`, `ℓ*_τ ≡ -∞`).
* `aemeasurable_of_rightDerivative`: a quasi-everywhere right derivative is a.e.-measurable for
  `θ_φⁿ` (limit of the measurable difference quotients at `t = 1/(k+1)`).
* `sourceRay_energy_slope` (`cor:ray_energy_slope`, first assertion): with `E^φ(ℓ)` the radial
  energy `sourceRadialEnergy` (`def:radialMAenergy2`) and `D` any function which is the right
  derivative quasi-everywhere: `D` is finite `θ_φⁿ`-a.e., `D ∈ L¹(θ_φⁿ)` and
  `E^φ(ℓ) = ∫_X D θ_φⁿ`.
* `sourceRay_energy_eq_mul_slope` (`cor:ray_energy_slope`, "in particular"):
  `E_θ^φ(ℓ_t) = t ∫_X D θ_φⁿ` for every `t ≥ 0` (from `prop:energylinear` and `E_θ^φ(φ) = 0`).
* `sourceRay_energy_slope_rightSlope`: both assertions for `D = sourceRayRightSlope ℓ`.

The proof is the book's: `E^φ(ℓ) = E^φ(ℓ*)` (`thm:Legenbij`), the test-curve energy
`ℓ*_max ∫θ_φⁿ - ∫_{-∞}^{ℓ*_max} (∫θ_φⁿ - ∫θⁿ_{ℓ*_τ}) dτ` (`eq:tcfiniteenergy`),
`∫θⁿ_{ℓ*_τ} = θ_φⁿ{ℓ̇₀ ≥ τ}` (`prop:His_mass_tc`), and the layer-cake formula for the non-negative
function `ℓ*_max - ℓ̇₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Envelopes.DNT

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.Okounkov.TranscendentalWNReg
open SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}

/-- If the right derivative `d` of `t ↦ ℓ_t(x)` at `0` is `≥ τ` and `φ(x)` is finite, then
`φ(x) ≤ ℓ*_τ(x)` (any `τ`). -/
theorem le_inverse_of_le_slope (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {τ : ℝ} {x : M} (hx : φ x ≠ ⊥) {d : EReal}
    (hd : Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 d)) (hτd : (τ : EReal) ≤ d) :
    φ x ≤ sourcePositiveRayInverse ℓ τ x := by
  have hsub := h.1.isSubgeodesicRay
  have h0 : ℓ ⟨0, self_mem_Ici⟩ = φ := h.2
  have hφ0 : φ x ≤ 0 := by
    rw [hφ.choose_spec.1]
    exact sourceSingularityEnvelope_le_zero θ φ x
  have hxt : φ x ≠ ⊤ := ne_top_of_le_ne_top EReal.zero_ne_top hφ0
  set a : ℝ := (φ x).toReal with hadef
  have ha : φ x = (a : EReal) := (EReal.coe_toReal hxt hx).symm
  have ha0 : ℓ ⟨0, self_mem_Ici⟩ x = (a : EReal) := by rw [h0, ha]
  refine le_iInf fun t => ?_
  have ht : 0 < t.1 := t.2
  have hdt : d ≤ sourceRayQuotient ℓ x t.1 := by
    refine le_of_tendsto hd ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact sourceRayQuotient_mono hsub ha0 hs.1 hs.2
  have hq := hτd.trans hdt
  unfold sourceRayQuotient at hq
  rw [ha0] at hq
  rw [ha]
  exact (coe_le_inv_mul_sub_iff ht _).mp hq

/-- **`ℓ̇₀ ≤ ℓ*_max`** wherever `φ` is finite. -/
theorem slope_le_cutoff (omega : KahlerBackground n M) (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ)
    {x : M} (hx : φ x ≠ ⊥) {d : EReal} (hd : Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 d)) :
    d ≤ (sourceRayLegendreCutoff omega h : EReal) := by
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  obtain ⟨τ, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hle := le_inverse_of_le_slope omega h hx hd h2.le
  have hbot : sourcePositiveRayInverse ℓ τ x = ⊥ :=
    congrFun (sourceRayLegendre_inverse_bot_above omega h (EReal.coe_lt_coe_iff.mp h1)) x
  exact hx (le_bot_iff.mp (hle.trans_eq hbot))

omit [ConnectedSpace M] in
/-- The difference quotients of a subgeodesic ray are measurable in `x`. -/
theorem measurable_sourceRayQuotient {omega : KahlerBackground n M}
    (hsub : SourceIsSubgeodesicRay omega θ ℓ) (t : ℝ) :
    Measurable fun x => sourceRayQuotient ℓ x t := by
  have h1 : Measurable (sourceRayExtension ℓ t) :=
    (hsub.thetaPSH ⟨max t 0, le_max_right t 0⟩).upperSemicontinuous.measurable
  have h0 : Measurable (ℓ ⟨0, self_mem_Ici⟩) :=
    (hsub.thetaPSH ⟨0, self_mem_Ici⟩).upperSemicontinuous.measurable
  unfold sourceRayQuotient
  simp only [sub_eq_add_neg]
  exact measurable_const.mul (h1.add (continuous_neg.measurable.comp h0))

/-- A quasi-everywhere right derivative is a.e.-measurable for every measure not charging
pluripolar sets. -/
theorem aemeasurable_of_rightDerivative (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {D : M → EReal}
    (hD : SourceQuasiEverywhere (n := n) fun x =>
      Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (D x)))
    {μ : Measure M} (hμ : DoesNotChargeManifoldPluripolar (n := n) μ) : AEMeasurable D μ := by
  have hseq : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k =>
        mem_Ioi.mpr (Nat.one_div_pos_of_nat (α := ℝ) (n := k))⟩
  refine aemeasurable_of_tendsto_metrizable_ae'
    (f := fun k x => sourceRayQuotient ℓ x (1 / ((k : ℝ) + 1)))
    (fun k => (measurable_sourceRayQuotient h.1.isSubgeodesicRay _).aemeasurable) ?_
  filter_upwards [hμ.ae_of_quasiEverywhere ((sourceQuasiEverywhere_iff_native _).mp hD)] with x hx
  exact hx.comp hseq

/-- **`cor:ray_energy_slope`, first assertion.**  Let `ℓ ∈ R¹(X, θ; φ)` and let `D` be the right
derivative `ℓ̇₀` of `t ↦ ℓ_t` at `t = 0` quasi-everywhere.  Then `D` is finite `θ_φⁿ`-a.e.,
`D ∈ L¹(X, θ_φⁿ)` and `E^φ(ℓ) = ∫_X D θ_φⁿ`. -/
theorem sourceRay_energy_slope (omega : KahlerBackground n M)
    (hℓ : ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ) {D : M → EReal}
    (hD : SourceQuasiEverywhere (n := n) fun x =>
      Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (D x))) :
    (∀ᵐ x ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH), D x ≠ ⊥ ∧ D x ≠ ⊤) ∧
      Integrable (fun x => (D x).toReal) (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) ∧
      sourceRadialEnergy omega ⟨ℓ, hℓ.1.1, hℓ.2⟩ =
        ((∫ x, (D x).toReal ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) : ℝ) : EReal) := by
  have h : ℓ ∈ sourceGeodesicRays omega θ φ hφ := ⟨hℓ.1.1, hℓ.2⟩
  set μ := sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH with hμdef
  set C := sourceRayLegendreCutoff omega h with hCdef
  set Γ := sourceRayLegendreTestCurve omega h with hΓdef
  have hφn := (isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ.thetaPSH
  have : IsFiniteMeasure μ :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega (fun _ => hφn.1)
  have hnc : DoesNotChargeManifoldPluripolar (n := n) μ :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (θ := fun _ : Fin n => atlasClosedFormToNative θ) (u := fun _ => φ) (fun _ => hφn.1)
  have hpole : QuasiEverywhere (n := n) fun x => φ x ≠ ⊥ := by
    have := quasiPsh_poles_manifoldLocallyPluripolar hφn.quasiPshPotential
    simpa only [QuasiEverywhere, ne_eq, not_not] using this
  have haeD := hnc.ae_of_quasiEverywhere ((sourceQuasiEverywhere_iff_native _).mp hD)
  have haeP := hnc.ae_of_quasiEverywhere hpole
  have hDm : AEMeasurable D μ := aemeasurable_of_rightDerivative omega h hD hnc
  have hDC : ∀ᵐ x ∂μ, D x ≤ (C : EReal) := by
    filter_upwards [haeD, haeP] with x hx1 hx2
    exact slope_le_cutoff omega h hx2 hx1
  have hDtop : ∀ᵐ x ∂μ, D x ≠ ⊤ := by
    filter_upwards [hDC] with x hx
    exact ne_top_of_le_ne_top (EReal.coe_ne_top C) hx
  -- the masses of the Legendre transform
  have hmass : ∀ τ ∈ Iio C, ENNReal.ofReal ((μ univ).toReal - sourceTestCurveRealMassAt omega Γ τ) =
      μ {x | D x < (τ : EReal)} := by
    intro τ hτ
    have hτ' : τ < C := hτ
    rw [sourceTestCurveRealMassAt_of_lt omega Γ hτ']
    have hHis : sourcePotentialNonPluripolarMeasure θ (Γ.potential ⟨τ, hτ'⟩)
        (Γ.thetaPSH ⟨τ, hτ'⟩) univ = μ {x | (τ : EReal) ≤ D x} :=
      sourceRay_legendre_mass_eq omega h hτ' hD
    rw [hHis]
    have hnm : NullMeasurableSet {x | (τ : EReal) ≤ D x} μ := nullMeasurableSet_le aemeasurable_const hDm
    have hsum := measure_add_measure_compl₀ hnm
    have hcompl : {x | (τ : EReal) ≤ D x}ᶜ = {x | D x < (τ : EReal)} := by
      ext x
      simp only [mem_compl_iff, mem_ofPred_eq, not_le]
    rw [hcompl] at hsum
    rw [← hsum, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), add_sub_cancel_left,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- the energy
  have hΓb : Γ ∈ SourceTestCurvesBased θ φ hφ := (source_ray_legendre_test_curve_whole omega h).1
  have hΓE : Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ :=
    ((sourceTestCurveFiniteEnergyLegendreEquiv omega φ hφ).symm ⟨ℓ, hℓ⟩).2
  have hE : sourceRadialEnergy omega ⟨ℓ, h⟩ = sourceTestCurveEnergy omega hφ Γ hΓb := by
    rw [source_test_curve_legendre_radial_energy_identity omega Γ hΓb hΓE]
    congr 1
    exact Subtype.ext (sourceRayLegendre_right_inverse omega h).symm
  set G : ℝ≥0∞ := ∫⁻ τ in Iio C, μ {x | D x < (τ : EReal)} with hGdef
  have hEG : sourceTestCurveEnergy omega hφ Γ hΓb =
      ((C * (μ univ).toReal : ℝ) : EReal) - (G : EReal) := by
    rw [sourceTestCurveEnergy, hGdef]
    congr 2
    exact setLIntegral_congr_fun measurableSet_Iio hmass
  obtain ⟨hb, hEbot, -⟩ := sourceTestCurveEnergy_finite_of_mem omega hφ Γ hΓE
  have hEbot' : sourceTestCurveEnergy omega hφ Γ hΓb ≠ ⊥ := hEbot
  have hGtop : G ≠ ⊤ := by
    intro hG
    apply hEbot'
    rw [hEG, hG, EReal.coe_ennreal_top, EReal.sub_top]
  -- `D > -∞` almost everywhere
  have hbot0 : μ {x | D x = ⊥} = 0 := by
    by_contra hne
    have hle : ∫⁻ _ in Iio C, μ {x | D x = ⊥} ≤ G :=
      setLIntegral_mono' measurableSet_Iio fun τ _ =>
        measure_mono fun x (hx : D x = ⊥) => by
          change D x < (τ : EReal)
          rw [hx]
          exact EReal.bot_lt_coe τ
    rw [setLIntegral_const, Real.volume_Iio, ENNReal.mul_top hne] at hle
    exact hGtop (top_le_iff.mp hle)
  have hDbot : ∀ᵐ x ∂μ, D x ≠ ⊥ := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hbot0
  -- the layer-cake formula for `ℓ*_max - ℓ̇₀`
  set f : M → ℝ := fun x => C - (D x).toReal with hfdef
  have hf_nn : 0 ≤ᵐ[μ] f := by
    filter_upwards [hDC, hDbot] with x hx1 hx2
    have := EReal.toReal_le_toReal hx1 hx2 (EReal.coe_ne_top C)
    rw [EReal.toReal_coe] at this
    simp only [hfdef, Pi.zero_apply, sub_nonneg]
    exact this
  have hf_m : AEMeasurable f μ := aemeasurable_const.sub hDm.ereal_toReal
  have hlayer := lintegral_eq_lintegral_meas_lt μ hf_nn hf_m
  have hlevel : ∀ s : ℝ, μ {x | s < f x} = μ {x | D x < ((C - s : ℝ) : EReal)} := by
    intro s
    refine measure_congr (Filter.eventuallyEq_set.mpr ?_)
    filter_upwards [hDbot, hDtop] with x hx1 hx2
    simp only [hfdef]
    rw [← EReal.coe_toReal hx2 hx1, EReal.coe_lt_coe_iff, EReal.toReal_coe]
    constructor <;> intro h' <;> linarith
  have hshift : ∫⁻ s in Ioi (0 : ℝ), μ {x | D x < ((C - s : ℝ) : EReal)} = G := by
    rw [hGdef, ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Iio,
      ← lintegral_sub_left_eq_self ((Iio C).indicator fun τ => μ {x | D x < (τ : EReal)}) C]
    refine lintegral_congr fun s => ?_
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),
        indicator_of_mem (show C - s ∈ Iio C from by simp only [mem_Iio]; linarith)]
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs),
        indicator_of_notMem (show C - s ∉ Iio C from by
          simp only [mem_Iio, not_lt]; linarith [not_lt.mp hs])]
  have hfG : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = G := by
    rw [hlayer, ← hshift]
    exact setLIntegral_congr_fun measurableSet_Ioi fun s _ => hlevel s
  have hf_int : Integrable f μ :=
    (lintegral_ofReal_ne_top_iff_integrable hf_m.aestronglyMeasurable hf_nn).mp (hfG ▸ hGtop)
  have hD_eq : (fun x => (D x).toReal) = fun x => C - f x := by
    funext x
    simp only [hfdef]
    ring
  have hD_int : Integrable (fun x => (D x).toReal) μ := by
    rw [hD_eq]
    exact (integrable_const C).sub hf_int
  refine ⟨?_, hD_int, ?_⟩
  · filter_upwards [hDbot, hDtop] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  · have hint_f : ∫ x, f x ∂μ = G.toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hf_nn hf_m.aestronglyMeasurable, hfG]
    have hintD : ∫ x, (D x).toReal ∂μ = C * (μ univ).toReal - G.toReal := by
      rw [hD_eq, integral_sub (integrable_const C) hf_int, integral_const, hint_f, smul_eq_mul,
        measureReal_def, mul_comm]
    rw [show (⟨ℓ, hℓ.1.1, hℓ.2⟩ : SourceGeodesicRay omega θ φ hφ) = ⟨ℓ, h⟩ from rfl, hE, hEG,
      hintD, EReal.coe_sub, EReal.coe_ennreal_toReal hGtop]

omit [ConnectedSpace M] in
/-- `E_θ^φ(φ) = 0`. -/
theorem sourceRelativeEnergy_model_eq_zero (omega : KahlerBackground n M) :
    sourceRelativeEnergy θ φ φ hφ = 0 := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega _ hφ.toNative
      ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

/-- **`cor:ray_energy_slope`, "in particular"**: for `ℓ ∈ R¹(X, θ; φ)` and `D` the right derivative
`ℓ̇₀` quasi-everywhere, `E_θ^φ(ℓ_t) = t ∫_X D θ_φⁿ` for every `t ≥ 0`. -/
theorem sourceRay_energy_eq_mul_slope (omega : KahlerBackground n M)
    (hℓ : ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ) {D : M → EReal}
    (hD : SourceQuasiEverywhere (n := n) fun x =>
      Tendsto (sourceRayQuotient ℓ x) (𝓝[>] 0) (𝓝 (D x))) (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (ℓ t) hφ =
      ((t.1 * ∫ x, (D x).toReal ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) : ℝ) :
        EReal) := by
  obtain ⟨-, -, hrad⟩ := sourceRay_energy_slope omega hℓ hD
  set I := ∫ x, (D x).toReal ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) with hI
  have hfin : ∀ s : Ici (0 : ℝ), SourceRelativeFiniteEnergy θ φ (ℓ s) hφ := fun s =>
    (sourceFiniteEnergyRaySlice omega ⟨ℓ, hℓ⟩ s).property
  have hfin' : ∀ s : ℝ, 0 ≤ s → SourceRelativeFiniteEnergy θ φ (sourceRayExtension ℓ s) hφ :=
    fun s hs => by rw [sourceRayExtension_nonneg ℓ s hs]; exact hfin ⟨s, hs⟩
  set b : ℝ := t.1 + 1 with hb
  have hb0 : 0 ≤ b := by have := t.2; simp only [mem_Ici] at this; linarith
  have hseg := hℓ.1.1.2 0 b le_rfl hb0
  obtain ⟨c₀, c₁, hc⟩ := sourceGeodesic_energy_affine hseg (hfin' 0 le_rfl) (hfin' b hb0)
  have hE0 : (sourceRelativeEnergy θ φ (sourceRayExtension ℓ 0) hφ).toReal = 0 := by
    rw [sourceRayExtension_nonneg ℓ 0 le_rfl,
      show ℓ ⟨0, self_mem_Ici⟩ = φ from hℓ.2, sourceRelativeEnergy_model_eq_zero omega, EReal.toReal_zero]
  have hc0 : c₀ = 0 := by
    have := hc 0 ⟨le_rfl, hb0⟩
    rw [hE0, mul_zero, add_zero] at this
    exact this.symm
  have ht1 : (1 : ℝ) ∈ Icc 0 b := ⟨zero_le_one, by have := t.2; simp only [mem_Ici] at this; linarith⟩
  have hE1 : (sourceRelativeEnergy θ φ (sourceRayExtension ℓ 1) hφ).toReal = c₁ := by
    rw [hc 1 ht1, hc0, zero_add, mul_one]
  -- the radial energy is `c₁`
  have hfin1 := sourceRelativeFiniteEnergy_coe_toReal omega (hfin ⟨1, mem_Ici.mpr zero_le_one⟩)
  have hne1 : sourceRelativeEnergy θ φ (ℓ ⟨1, mem_Ici.mpr zero_le_one⟩) hφ ≠ ⊥ := by
    rw [← hfin1]
    exact EReal.coe_ne_bot _
  have hradc : sourceRadialEnergy omega ⟨ℓ, hℓ.1.1, hℓ.2⟩ = (c₁ : EReal) := by
    rw [sourceRadialEnergy_eq omega]
    change (if sourceRelativeEnergy θ φ (ℓ ⟨1, mem_Ici.mpr zero_le_one⟩) hφ = ⊥ then ⊥ else
      (((sourceRelativeEnergy θ φ (ℓ ⟨1, mem_Ici.mpr zero_le_one⟩) hφ).toReal -
        (sourceRelativeEnergy θ φ (ℓ ⟨0, self_mem_Ici⟩) hφ).toReal : ℝ) : EReal)) = _
    rw [if_neg hne1, ← sourceRayExtension_nonneg ℓ 1 zero_le_one,
      ← sourceRayExtension_nonneg ℓ 0 le_rfl, hE1, hE0, sub_zero]
  have hcI : c₁ = I := EReal.coe_injective (hradc.symm.trans hrad)
  -- conclusion
  have htb : t.1 ∈ Icc 0 b := ⟨t.2, by linarith⟩
  have hEt := hc t.1 htb
  rw [sourceRayExtension_nonneg ℓ t.1 t.2] at hEt
  rw [← sourceRelativeFiniteEnergy_coe_toReal omega (hfin t), hEt, hc0, zero_add, hcI, mul_comm]

/-- **`cor:ray_energy_slope`** with `ℓ̇₀ = sourceRayRightSlope ℓ`: `ℓ̇₀` is finite `θ_φⁿ`-a.e. and
integrable, `E^φ(ℓ) = ∫_X ℓ̇₀ θ_φⁿ`, and `E_θ^φ(ℓ_t) = t ∫_X ℓ̇₀ θ_φⁿ` for `t ≥ 0`. -/
theorem sourceRay_energy_slope_rightSlope (omega : KahlerBackground n M)
    (hℓ : ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ) :
    (∀ᵐ x ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH),
        sourceRayRightSlope ℓ x ≠ ⊥ ∧ sourceRayRightSlope ℓ x ≠ ⊤) ∧
      Integrable (fun x => (sourceRayRightSlope ℓ x).toReal)
        (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) ∧
      sourceRadialEnergy omega ⟨ℓ, hℓ.1.1, hℓ.2⟩ =
        ((∫ x, (sourceRayRightSlope ℓ x).toReal
          ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) : ℝ) : EReal) ∧
      ∀ t : Ici (0 : ℝ), sourceRelativeEnergy θ φ (ℓ t) hφ =
        ((t.1 * ∫ x, (sourceRayRightSlope ℓ x).toReal
          ∂(sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH) : ℝ) : EReal) := by
  have hD := sourceRayRightSlope_isRightDerivative_qe omega (h := ⟨hℓ.1.1, hℓ.2⟩)
  obtain ⟨h1, h2, h3⟩ := sourceRay_energy_slope omega hℓ hD
  exact ⟨h1, h2, h3, sourceRay_energy_eq_mul_slope omega hℓ hD⟩

end SGPT.Envelopes.DNT
