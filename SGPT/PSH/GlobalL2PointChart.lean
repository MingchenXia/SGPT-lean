import SGPT.PSH.GlobalL2Correction

/-!
# Chart estimates for the point extension

Blueprint `claude-global-l2b.tex`, node `claude-global-l2b:chart-estimates`.

* `GluingSystem.lintegral_ball_le_region`: `∫_{B_R} g dz ≤ A ∫_{z⁻¹ B_R} g ∘ z dμ`
  (the lower density bound `1 ≤ A ρ`), and its consequence `lintegral_ball_r_le_small`.
* `GluingSystem.lintegral_open_le`: `∫_{z⁻¹ Ω} |u|² w dμ ≤ A ∫_Ω |u_i|² W_i dz` for open
  `Ω ⊆ B_R` (the upper density bound `ρ ≤ A`).
* `CoverData.energy_datum_le`: the quantitative form of `CoverData.energy_datum_lt_top`:
  `N_l(χF) ≤ C A ∫_K |F|² e^{-kφ} dμ` with `C` a bound for `|∂̄(χ ∘ z_l⁻¹)|²` (the proof is that
  of `energy_datum_lt_top`, lane S54, with the final finiteness step removed).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

namespace GluingSystem

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} {V : X → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  {w : X → ℝ≥0∞} {ι : Type*} [Fintype ι] (G : GluingSystem n X μ V w ι)

/-- `∫_{B_R} g ≤ A ∫_{region} g ∘ z dμ`. -/
theorem lintegral_ball_le_region (i : ι) (g : ComplexModel n → ℝ≥0∞)
    (hg : AEMeasurable g (volume.restrict (ball (G.center i) (G.R i)))) :
    ∫⁻ z in ball (G.center i) (G.R i), g z ≤ G.A * ∫⁻ x in G.region i, g (G.chart i x) ∂μ := by
  have hmap := G.map_measure i (fun x => g (G.chart i x)) (hg.congr
    ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => by
      simp only [G.chart_symm hz])))
  rw [region, hmap, ← lintegral_const_mul' _ _ G.A_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  rw [G.chart_symm hz]
  calc g z = 1 * g z := (one_mul _).symm
    _ ≤ (G.A * G.dens i z) * g z := mul_le_mul_of_nonneg_right (G.one_le_A_mul_dens i z hz) zero_le
    _ = G.A * (g z * G.dens i z) := by ring

/-- `∫_{B_r} |u_i|² W_i ≤ A ∫_{small} |u|² w dμ`. -/
theorem lintegral_ball_r_le_small (i : ι) (u : (x : X) → V x)
    (hu : ContinuousOn (G.locCoef i u) (ball (G.center i) (G.r i))) :
    ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z ≤
      G.A * ∫⁻ x in G.small i, G.D u x ∂μ := by
  have hrR : ball (G.center i) (G.r i) ⊆ ball (G.center i) (G.R i) :=
    ball_subset_ball (G.r_lt_R i).le
  have hsm : MeasurableSet (G.small i) := (G.isOpen_small i).measurableSet
  calc ∫⁻ z in ball (G.center i) (G.r i), ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z
      = ∫⁻ z in ball (G.center i) (G.R i), (ball (G.center i) (G.r i)).indicator
          (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
        rw [lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
          inter_eq_left.mpr hrR]
    _ ≤ G.A * ∫⁻ x in G.region i, (ball (G.center i) (G.r i)).indicator
          (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) (G.chart i x) ∂μ :=
        G.lintegral_ball_le_region i _ (G.aemeasurable_indicator_ball hu)
    _ = G.A * ∫⁻ x in G.region i, (G.small i).indicator (G.D u) x ∂μ := by
        congr 1
        refine setLIntegral_congr_fun (G.isOpen_region i).measurableSet fun x hx => ?_
        have h := G.indicator_small_eq u hx.2
        rw [(G.chart i).left_inv hx.1] at h
        exact h.symm
    _ = G.A * ∫⁻ x in G.small i, G.D u x ∂μ := by
        rw [lintegral_indicator hsm, Measure.restrict_restrict hsm,
          inter_eq_left.mpr (G.small_subset_region i)]

/-- `∫_{z⁻¹ Ω} |u|² w dμ ≤ A ∫_Ω |u_i|² W_i` for open `Ω ⊆ B_R`. -/
theorem lintegral_open_le (i : ι) (u : (x : X) → V x) {Ω : Set (ComplexModel n)}
    (hΩ : IsOpen Ω) (hΩR : Ω ⊆ ball (G.center i) (G.R i))
    (hu : ContinuousOn (G.locCoef i u) Ω) :
    ∫⁻ x in (G.chart i).source ∩ G.chart i ⁻¹' Ω, G.D u x ∂μ ≤
      G.A * ∫⁻ z in Ω, ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z := by
  set S : Set X := (G.chart i).source ∩ G.chart i ⁻¹' Ω with hS
  have hSo : IsOpen S := (G.chart i).isOpen_inter_preimage hΩ
  have hSm : MeasurableSet S := hSo.measurableSet
  have hSR : S ⊆ G.region i := fun x hx => ⟨hx.1, hΩR hx.2⟩
  have hiff : ∀ z ∈ ball (G.center i) (G.R i), (G.chart i).symm z ∈ S ↔ z ∈ Ω := by
    intro z hz
    constructor
    · intro h; have := h.2; rwa [mem_preimage, G.chart_symm hz] at this
    · intro h; exact ⟨G.symm_mem_source hz, by rw [mem_preimage, G.chart_symm hz]; exact h⟩
  have heq : ∀ z ∈ ball (G.center i) (G.R i), S.indicator (G.D u) ((G.chart i).symm z) =
      Ω.indicator (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · rw [indicator_of_mem ((hiff z hz).mpr hzΩ), indicator_of_mem hzΩ, G.D_chart i u hz]
    · rw [indicator_of_notMem (fun h => hzΩ ((hiff z hz).mp h)), indicator_of_notMem hzΩ]
  have hmeas : AEMeasurable (Ω.indicator
      fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z)
      (volume.restrict (ball (G.center i) (G.R i))) := by
    refine (aemeasurable_indicator_iff hΩ.measurableSet).mpr ?_
    rw [Measure.restrict_restrict hΩ.measurableSet, inter_eq_left.mpr hΩR]
    refine (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hu.aestronglyMeasurable hΩ.measurableSet).norm.aemeasurable.pow_const 2)).mul ?_
    exact (G.aemeasurable_W i).mono_measure (Measure.restrict_mono hΩR le_rfl)
  calc ∫⁻ x in S, G.D u x ∂μ = ∫⁻ x in G.region i, S.indicator (G.D u) x ∂μ := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, inter_eq_left.mpr hSR]
    _ = ∫⁻ z in ball (G.center i) (G.R i), S.indicator (G.D u) ((G.chart i).symm z) *
          G.dens i z := by
        rw [region, G.map_measure i _ ?_]
        exact hmeas.congr ((ae_restrict_iff' measurableSet_ball).mpr
          (Eventually.of_forall fun z hz => (heq z hz).symm))
    _ ≤ ∫⁻ z in ball (G.center i) (G.R i), G.A * Ω.indicator
          (fun z => ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        rw [heq z hz, mul_comm]
        exact mul_le_mul_of_nonneg_right (G.dens_le i z hz) zero_le
    _ = G.A * ∫⁻ z in Ω, ENNReal.ofReal (‖G.locCoef i u z‖ ^ 2) * G.W i z := by
        rw [lintegral_const_mul' _ _ G.A_ne_top, lintegral_indicator hΩ.measurableSet,
          Measure.restrict_restrict hΩ.measurableSet, inter_eq_left.mpr hΩR]

/-- The integral over `X` is at most the sum of the integrals over the middle regions. -/
theorem lintegral_le_sum_small (f : X → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ ≤ ∑ i, ∫⁻ x in G.small i, f x ∂μ := by
  have hU : (⋃ i, G.small i) = univ := eq_univ_of_forall fun x => by
    obtain ⟨i, hi⟩ := G.cover x
    exact mem_iUnion.mpr ⟨i, G.smaller_subset_small i hi⟩
  calc ∫⁻ x, f x ∂μ = ∫⁻ x in ⋃ i, G.small i, f x ∂μ := by rw [hU, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in G.small i, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i, ∫⁻ x in G.small i, f x ∂μ := tsum_fintype _

end GluingSystem

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace CoverData

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

section Datum

variable (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
  {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
  (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
  {U : Set X} (hU : IsOpen U) {F : (x : X) → (twistedPower L T k).Fiber x}
  (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber F U)
  {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hχU : tsupport χ ⊆ U)
  {K : Set X} (hKU : K ⊆ U) (hconst : ∀ x ∈ U \ K, ∀ᶠ y in 𝓝 x, χ y = χ x)
include hL hT hk hφ hU hF hχ hχU hKU hconst

/-- **Quantitative energy of the datum `χF`** (cf. `CoverData.energy_datum_lt_top`). -/
theorem energy_datum_le (hK : IsCompact K) (l : Fin D.m) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ C) :
    (D.toGluingSystem hL hT hk hφ).energy l (fun x => ((χ x : ℝ) : ℂ) • F x) ≤
      ENNReal.ofReal C * ((D.toGluingSystem hL hT hk hφ).A *
        ∫⁻ x in K, (D.toGluingSystem hL hT hk hφ).D F x ∂μ) := by
  set G := D.toGluingSystem hL hT hk hφ
  set g := G.locCoef l F
  have hB : ball (ctr (n := n) (D.pt l)) (D.R l) = ball (G.center l) (G.R l) := rfl
  set f : X → ℝ≥0∞ := K.indicator (G.D F) with hf
  have hpt : ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      ENNReal.ofReal (dbarNormSq (G.locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x)) z) * G.W l z ≤
        ENNReal.ofReal C * f ((D.chartA l).val.symm z) := by
    intro z hz
    have h := (D.datum_spec hL hT hk hφ hU hF hχ hχU hKU hconst l hC hz).2
    by_cases hzK : (D.chartA l).val.symm z ∈ K
    · rw [indicator_of_mem (show z ∈ (D.chartA l).val.symm ⁻¹' K from hzK)] at h
      rw [hf, indicator_of_mem hzK]
      calc ENNReal.ofReal (dbarNormSq (G.locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x)) z) * G.W l z
          ≤ ENNReal.ofReal (C * ‖g z‖ ^ 2) * G.W l z :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le
        _ = ENNReal.ofReal C * G.D F ((D.chartA l).val.symm z) := by
            rw [show G.D F ((D.chartA l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) * G.W l z from
              G.D_chart l F (by rw [← hB]; exact hz), ENNReal.ofReal_mul hC0, mul_assoc]
    · rw [indicator_of_notMem (show z ∉ (D.chartA l).val.symm ⁻¹' K from hzK)] at h
      have h0 : dbarNormSq (G.locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x)) z = 0 :=
        le_antisymm h (dbarNormSq_nonneg _ z)
      rw [h0, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  have hKc : IsClosed K := hK.isClosed
  set S' : Set (ComplexModel n) := closedBall (ctr (n := n) (D.pt l)) (D.R l) ∩
    (D.chartA l).val.symm ⁻¹' K with hS'
  have hS'c : IsClosed S' := ContinuousOn.preimage_isClosed_of_isClosed
    ((D.chartA l).val.continuousOn_symm.mono (D.closedBall_subset_target l)) isClosed_closedBall hKc
  have hS'm : MeasurableSet S' := hS'c.measurableSet
  have hfm : AEMeasurable (fun z => f ((D.chartA l).val.symm z))
      (volume.restrict (ball (ctr (n := n) (D.pt l)) (D.R l))) := by
    have hgc : ContinuousOn g (S' ∩ ball (ctr (n := n) (D.pt l)) (D.R l)) :=
      (D.differentiableOn_locCoef_F hL hT hk hφ hU hF hχ hχU hKU hconst l).continuousOn.mono
        fun z hz => ⟨hz.2, hKU hz.1.2⟩
    have hind : AEMeasurable (S'.indicator fun z => ENNReal.ofReal (‖g z‖ ^ 2) * G.W l z)
        (volume.restrict (ball (ctr (n := n) (D.pt l)) (D.R l))) := by
      refine (aemeasurable_indicator_iff hS'm).mpr ?_
      rw [Measure.restrict_restrict hS'm]
      refine (ENNReal.measurable_ofReal.comp_aemeasurable
        ((hgc.aestronglyMeasurable (hS'm.inter measurableSet_ball)).norm.aemeasurable.pow_const
          2)).mul ?_
      exact (G.aemeasurable_W l).mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
    refine hind.congr ((ae_restrict_iff' measurableSet_ball).mpr (Eventually.of_forall fun z hz => ?_))
    show _ = f ((D.chartA l).val.symm z)
    by_cases hzK : (D.chartA l).val.symm z ∈ K
    · rw [indicator_of_mem (show z ∈ S' from ⟨ball_subset_closedBall hz, hzK⟩), hf,
        indicator_of_mem hzK, show G.D F ((D.chartA l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) *
          G.W l z from G.D_chart l F (by rw [← hB]; exact hz)]
    · rw [indicator_of_notMem (show z ∉ S' from fun h => hzK h.2), hf, indicator_of_notMem hzK]
  calc G.energy l (fun x => ((χ x : ℝ) : ℂ) • F x)
      ≤ ∫⁻ z in ball (ctr (n := n) (D.pt l)) (D.R l),
          ENNReal.ofReal C * (G.A * (f ((D.chartA l).val.symm z) * G.dens l z)) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => (hpt z hz).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc f ((D.chartA l).val.symm z) = 1 * f ((D.chartA l).val.symm z) := (one_mul _).symm
          _ ≤ (G.A * G.dens l z) * f ((D.chartA l).val.symm z) :=
              mul_le_mul_of_nonneg_right (G.one_le_A_mul_dens l z (by rw [← hB]; exact hz)) zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal C * (G.A * ∫⁻ x in G.region l, f x ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ G.A_ne_top,
          GluingSystem.region, G.map_measure l f hfm]
        rfl
    _ ≤ ENNReal.ofReal C * (G.A * ∫⁻ x in K, G.D F x ∂μ) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
        rw [← lintegral_indicator hKc.measurableSet]
        exact setLIntegral_le_lintegral _ _

end Datum

end CoverData

end SGPT.PSH.GlobalL2
