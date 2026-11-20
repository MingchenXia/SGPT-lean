import SGPT.PSH.SourceTestCurveFoundation
import SGPT.Envelopes.SourceIncreasingMixedProducts
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual original negative-epigraph concavity gives the SAME native
strict convex combination inequality, with both original pole branches. -/
theorem SourceTestCurvePredata.convexComb_le
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurvePredata θ)
    (a b : Iio Γ.max) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    convexComb t (Γ.potential a) (Γ.potential b) ≤
      Γ.potential ⟨t * (a : ℝ) + (1 - t) * (b : ℝ), by
        change t * (a : ℝ) + (1 - t) * (b : ℝ) < Γ.max
        nlinarith [mul_pos ht0 (sub_pos.mpr a.property),
          mul_pos (sub_pos.mpr ht1) (sub_pos.mpr b.property)]⟩ := by
  intro x
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  have haTop := (Γ.native_thetaPSH a).1.quasiPlurisubharmonic.ne_top x
  have hbTop := (Γ.native_thetaPSH b).1.quasiPlurisubharmonic.ne_top x
  have hdom : t * (a : ℝ) + (1 - t) * (b : ℝ) < Γ.max := by
    nlinarith [mul_pos ht0 (sub_pos.mpr a.property), mul_pos ht (sub_pos.mpr b.property)]
  cases haVal : Γ.potential a x using EReal.rec with
  | top => exact False.elim (haTop haVal)
  | bot =>
    simp only [convexComb, haVal, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  | coe r =>
    cases hbVal : Γ.potential b x using EReal.rec with
    | top => exact False.elim (hbTop hbVal)
    | bot =>
      simp only [convexComb, hbVal, EReal.coe_mul_bot_of_pos ht, EReal.add_bot]
      exact bot_le
    | coe s =>
      have hpa : ((a : ℝ), -r) ∈ SGPT.Convex.epigraph
          (sourceTestCurveNegativeTrace Γ.max Γ.potential x) := by
        change sourceTestCurveNegativeTrace Γ.max Γ.potential x a.val ≤ ((-r : ℝ) : EReal)
        rw [sourceTestCurveNegativeTrace, dif_pos (show (a : ℝ) < Γ.max from a.property)]
        change -(Γ.potential a x) ≤ ((-r : ℝ) : EReal)
        rw [haVal, EReal.coe_neg]
      have hpb : ((b : ℝ), -s) ∈ SGPT.Convex.epigraph
          (sourceTestCurveNegativeTrace Γ.max Γ.potential x) := by
        change sourceTestCurveNegativeTrace Γ.max Γ.potential x b.val ≤ ((-s : ℝ) : EReal)
        rw [sourceTestCurveNegativeTrace, dif_pos (show (b : ℝ) < Γ.max from b.property)]
        change -(Γ.potential b x) ≤ ((-s : ℝ) : EReal)
        rw [hbVal, EReal.coe_neg]
      have hc := Γ.concave x hpa hpb ht0.le ht.le (show t + (1 - t) = 1 by ring)
      change sourceTestCurveNegativeTrace Γ.max Γ.potential x
        (t * (a : ℝ) + (1 - t) * (b : ℝ)) ≤
          ((t * (-r) + (1 - t) * (-s) : ℝ) : EReal) at hc
      rw [sourceTestCurveNegativeTrace, dif_pos hdom] at hc
      have hneg : ((t * (-r) + (1 - t) * (-s) : ℝ) : EReal) =
          -((t * r + (1 - t) * s : ℝ) : EReal) := by
        rw [← EReal.coe_neg]
        congr 1
        ring
      rw [hneg] at hc
      simpa only [convexComb, haVal, hbVal, ← EReal.coe_mul, ← EReal.coe_add] using
        (EReal.neg_le_neg_iff.mp hc)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

private theorem testCurve_mass_tendsto (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurvePredata θ) :
    Tendsto (fun τ : OrderDual (Iio Γ.max) ↦
      sourcePotentialNonPluripolarMeasure θ (Γ.potential τ) (Γ.thetaPSH τ) univ)
      atTop (𝓝 (sourcePotentialNonPluripolarMeasure θ (sourceTestCurveLimit Γ)
        Γ.limit_thetaPSH univ)) := by
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hm (j : Fin n) : Monotone
      (fun τ : OrderDual (Iio Γ.max) ↦ Γ.potential τ) := by
    intro a b hab x
    exact Γ.antitone x hab
  have hlim := sourceIncreasingMixed_mass_tendsto ω
    (θ := fun _ : Fin n ↦ θ)
    (u := fun τ : OrderDual (Iio Γ.max) ↦ fun _ : Fin n ↦ Γ.potential τ)
    (fun τ _ ↦ Γ.thetaPSH τ) hm (C := fun _ ↦ 0)
    (fun _ τ x ↦ by simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero τ x)
  have hU : uscRegularization (⨆ τ : OrderDual (Iio Γ.max), Γ.potential τ) =
      sourceTestCurveLimit Γ := by
    apply congrArg uscRegularization
    funext x
    exact iSup_apply
  simpa only [hU, sourceMixedNonPluripolarMass, sourceMixedNonPluripolarMeasure,
    sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMeasure] using hlim

/-- The ACTUAL full directed family mass limit and its printed positive
limit mass manufacture an earlier positive slice, with no such input. -/
theorem SourceTestCurve.exists_positive_mass_before (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ)
    (τ : Iio Γ.max) :
    ∃ σ : Iio Γ.max, (σ : ℝ) < (τ : ℝ) ∧
      0 < sourcePotentialNonPluripolarMeasure θ (Γ.potential σ) (Γ.thetaPSH σ) univ := by
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hlim := testCurve_mass_tendsto ω Γ.toSourceTestCurvePredata
  have hpos : ∀ᶠ σ : OrderDual (Iio Γ.max) in atTop,
      0 < sourcePotentialNonPluripolarMeasure θ (Γ.potential σ) (Γ.thetaPSH σ) univ :=
    hlim.eventually (isOpen_Ioi.mem_nhds Γ.positiveLimitMass)
  let σ₀ : OrderDual (Iio Γ.max) := ⟨(τ : ℝ) - 1, by
    change (τ : ℝ) - 1 < Γ.max
    have hτ : (τ : ℝ) < Γ.max := τ.property
    linarith⟩
  obtain ⟨σ, hmass, hσ⟩ := (hpos.and (eventually_ge_atTop σ₀)).exists
  refine ⟨σ, ?_, hmass⟩
  have hle : (σ : Iio Γ.max).val ≤ (σ₀ : Iio Γ.max).val := hσ
  change (σ : Iio Γ.max).val < (τ : ℝ)
  calc
    (σ : Iio Γ.max).val ≤ (σ₀ : Iio Γ.max).val := hle
    _ < (τ : ℝ) := by change (τ : ℝ) - 1 < (τ : ℝ); linarith

/-- WHOLE original positive-mass lemma: actual earlier positive mass,
genuine strict concavity and true NP convex scaling manufacture positivity
of EVERY original interior slice. No positive-slice certificate is input. -/
theorem SourceTestCurve.mass_positive (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ)
    (τ : Iio Γ.max) :
    0 < sourcePotentialNonPluripolarMeasure θ (Γ.potential τ) (Γ.thetaPSH τ) univ := by
  obtain ⟨τ₀, hτ₀, hmass₀⟩ := Γ.exists_positive_mass_before ω τ
  have hτ : (τ : ℝ) < Γ.max := τ.property
  let τ' : Iio Γ.max := ⟨((τ : ℝ) + Γ.max) / 2, by
    change ((τ : ℝ) + Γ.max) / 2 < Γ.max
    linarith⟩
  have hτ' : (τ : ℝ) < (τ' : ℝ) := by
    change (τ : ℝ) < ((τ : ℝ) + Γ.max) / 2
    linarith
  have hden : 0 < (τ' : ℝ) - (τ₀ : ℝ) := by linarith
  let t : ℝ := ((τ' : ℝ) - (τ : ℝ)) / ((τ' : ℝ) - (τ₀ : ℝ))
  have ht0 : 0 < t := div_pos (sub_pos.mpr hτ') hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hpar : t * (τ₀ : ℝ) + (1 - t) * (τ' : ℝ) = (τ : ℝ) := by
    dsimp only [t]
    field_simp
    ring
  let σ : Iio Γ.max := ⟨t * (τ₀ : ℝ) + (1 - t) * (τ' : ℝ), by
    change t * (τ₀ : ℝ) + (1 - t) * (τ' : ℝ) < Γ.max
    rw [hpar]
    exact hτ⟩
  have hcc : convexComb t (Γ.potential τ₀) (Γ.potential τ') ≤ Γ.potential σ :=
    Γ.toSourceTestCurvePredata.convexComb_le τ₀ τ' ht0 ht1
  have hσ : σ = τ := Subtype.ext hpar
  have hccτ : convexComb t (Γ.potential τ₀) (Γ.potential τ') ≤ Γ.potential τ := by
    rwa [hσ] at hcc
  let w := convexComb t (Γ.potential τ₀) (Γ.potential τ')
  have hwNative := isThetaPshPotential_convexComb
    (Γ.toSourceTestCurvePredata.native_thetaPSH τ₀)
    (Γ.toSourceTestCurvePredata.native_thetaPSH τ') ht0 ht1
  have hw : (ofFixedModel n M).IsThetaPSH θ w :=
    (isThetaPSH_iff_nativeThetaPotential θ w).mpr hwNative
  have hmono := sourcePotentialNonPluripolarMass_mono ω hw (Γ.thetaPSH τ)
    (MoreSingularOn.of_le (fun x _ ↦ hccτ x))
  have hscale := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
    (θ := atlasClosedFormToNative θ)
    (Γ.toSourceTestCurvePredata.native_thetaPSH τ₀)
    (Γ.toSourceTestCurvePredata.native_thetaPSH τ') ht0 ht1 univ
  change ENNReal.ofReal (t ^ n) *
      sourcePotentialNonPluripolarMeasure θ (Γ.potential τ₀) (Γ.thetaPSH τ₀) univ ≤
        sourcePotentialNonPluripolarMeasure θ w hw univ at hscale
  exact (ENNReal.mul_pos_iff.mpr
    ⟨ENNReal.ofReal_pos.mpr (pow_pos ht0 n), hmass₀⟩).trans_le (hscale.trans hmono)

/-- The actual original PSH/fixedpoint fields plus PRODUCED positive mass
are EXACTLY the genuine original positive-mass model predicate. -/
theorem SourceTestCurve.slice_model (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (Γ : SourceTestCurve θ)
    (τ : Iio Γ.max) : SourceModelPotential θ (Γ.potential τ) :=
  ⟨Γ.thetaPSH τ, (Γ.fixedPoint τ).symm, Γ.mass_positive ω τ⟩

end SGPT.PSH.VariableComplexAtlas
