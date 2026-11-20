import SGPT.PSH.GlobalL2CoverSystem

/-!
# The global `L²` correction of a cut-off holomorphic section

Blueprint `claude-global-l2:global-correction`.  `globalCutoffCorrection` proves
`GlobalCutoffCorrectionStatement n X`: on a compact complex manifold with a Kähler background,
for `k ≥ k₀(L, T, δ)` and `φ ∈ PSH(X, θ - δω)` (`θ = c₁(L, h_L)`), a cut-off `χ F` of a local
holomorphic section of `L^k ⊗ T` is corrected to a global holomorphic section `s` with
`∫ |χF - s|² e^{-kφ} dμ < ∞`.

Proof: the gluing system of `CoverData.toGluingSystem` has contraction factor `≤ 1/4`
(`CoverData.kappa_le`); the datum `χF` has smooth coefficients and finite `∂̄`-energy (its `∂̄` is
`∂̄χ ⊗ F`, supported over `K`); `GluingSystem.exists_correction` gives the correction, which is a
holomorphic section because it is given near every point by a holomorphic coefficient
(`CoverData.exists_section_of_local`).
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
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

section Coord

variable {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The coefficient of a holomorphic section in an atlas frame is holomorphic in the chart. -/
theorem differentiableOn_coord_of_holomorphicSectionOn
    (e : Trivialization ℂ (TotalSpace.proj : TotalSpace ℂ V → X)) [MemTrivializationAtlas e]
    (c : ComplexChart n X) {F : (x : X) → V x} {U : Set X} (hU : IsOpen U)
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) V F U) :
    DifferentiableOn ℂ (fun z => e.continuousLinearMapAt ℂ (c.val.symm z) (F (c.val.symm z)))
      (c.val.target ∩ c.val.symm ⁻¹' (U ∩ e.baseSet)) := by
  intro z hz
  have hy : c.val.symm z ∈ U ∩ e.baseSet := hz.2
  have hFm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ))
      (fun x => TotalSpace.mk' ℂ x (F x)) (c.val.symm z) :=
    (hF _ hy.1).mdifferentiableAt (hU.mem_nhds hy.1)
  have hco := (Trivialization.mdifferentiableAt_section_iff (IB := 𝓘(ℂ, ComplexModel n)) e F hy.2).mp hFm
  have hsy : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) c.val.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) (IsManifold.subset_maximalAtlas c.property)
      hz.1).mdifferentiableAt (by simp)
  have hd : DifferentiableAt ℂ (fun z => (e ⟨c.val.symm z, F (c.val.symm z)⟩).2) z :=
    (hco.comp z hsy).differentiableAt
  refine (hd.differentiableWithinAt).congr (fun w hw => ?_) ?_
  · exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hw.2.2 _
  · exact Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e hy.2 _

end Coord

variable [MeasurableSpace X] [BorelSpace X]

namespace CoverData

variable {ωb : KahlerBackground n X} {μ : Measure X}
  {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {θ : ClosedRealOneOneForm n X} {δ : ℝ}
  (D : CoverData ωb μ L T θ δ)

/-- **A section given locally by holomorphic coefficients is holomorphic.** -/
theorem exists_section_of_local (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
    (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ) (S : (x : X) → (twistedPower L T k).Fiber x)
    (hS : ∀ a, ∃ s : ComplexModel n → ℂ,
      DifferentiableOn ℂ s (ball ((D.toGluingSystem hL hT hk hφ).center a)
        ((D.toGluingSystem hL hT hk hφ).r a)) ∧
      ∀ x ∈ (D.toGluingSystem hL hT hk hφ).small a,
        S x = s ((D.toGluingSystem hL hT hk hφ).chart a x) •
          (D.toGluingSystem hL hT hk hφ).frame a x) :
    ∃ σ : twistedSections L T k, ∀ x, σ x = S x := by
  set G := D.toGluingSystem hL hT hk hφ with hG
  refine ⟨⟨S, fun x => ?_⟩, fun x => rfl⟩
  obtain ⟨a, ha⟩ := G.cover x
  have hxs : x ∈ G.small a := G.smaller_subset_small a ha
  obtain ⟨s, hs, hSa⟩ := hS a
  have hxR : (D.chartA a).val x ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
    ball_subset_ball (show D.R a / 2 ≤ D.R a by linarith [D.R_pos a]) hxs.2
  have hE : x ∈ (D.frameE k a).val.baseSet := D.mem_frameE_baseSet hxs.1 hxR
  rw [Trivialization.contMDiffAt_section_iff (D.frameE k a).val hE]
  have hev : (fun y => ((D.frameE k a).val ⟨y, S y⟩).2) =ᶠ[𝓝 x]
      fun y => s ((D.chartA a).val y) := by
    filter_upwards [(G.isOpen_small a).mem_nhds hxs] with y hy
    have hyR : (D.chartA a).val y ∈ ball (ctr (n := n) (D.pt a)) (D.R a) :=
      ball_subset_ball (show D.R a / 2 ≤ D.R a by linarith [D.R_pos a]) hy.2
    have hEy : y ∈ (D.frameE k a).val.baseSet := D.mem_frameE_baseSet hy.1 hyR
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hEy, hSa y hy, map_smul,
      smul_eq_mul]
    change s ((D.chartA a).val y) * ((D.frameE k a).val.continuousLinearMapAt ℂ y
      ((D.frameE k a).val.symm y 1)) = _
    rw [trivialization_coef_frame _ hEy, mul_one]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have hsC : ContDiffAt ℂ ∞ s ((D.chartA a).val x) :=
    contDiffAt_of_differentiableOn_complex hs isOpen_ball hxs.2
  exact hsC.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (D.chartA a).property) hxs.1)

section Datum

variable (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
  {k : ℕ} (hk : D.GoodPower k) {φ : X → EReal}
  (hφ : IsThetaPshPotential (θ - δ • ωb.form).val φ)
  {U : Set X} (hU : IsOpen U) {F : (x : X) → (twistedPower L T k).Fiber x}
  (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) (twistedPower L T k).Fiber F U)
  {χ : X → ℝ} (hχ : ChartSmooth (n := n) χ) (hχU : tsupport χ ⊆ U)
  {K : Set X} (hKU : K ⊆ U) (hconst : ∀ x ∈ U \ K, ∀ᶠ y in 𝓝 x, χ y = χ x)
include hL hT hk hφ hU hF hχ hχU hKU hconst

/-- The coefficient of `F` is holomorphic over `U`. -/
theorem differentiableOn_locCoef_F (l : Fin D.m) :
    DifferentiableOn ℂ ((D.toGluingSystem hL hT hk hφ).locCoef l F)
      (ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' U) := by
  refine (differentiableOn_coord_of_holomorphicSectionOn (D.frameE k l).val (D.chartA l) hU hF).mono
    fun z hz => ⟨D.ball_subset_target l hz.1, hz.2, ?_⟩
  have hs : (D.chartA l).val.symm z ∈ (D.chartA l).val.source :=
    (D.chartA l).val.map_target (D.ball_subset_target l hz.1)
  exact D.mem_frameE_baseSet hs (by rw [(D.chartA l).val.right_inv (D.ball_subset_target l hz.1)]; exact hz.1)

theorem locCoef_datum (l : Fin D.m) :
    (D.toGluingSystem hL hT hk hφ).locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x) =
      fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ) *
        (D.toGluingSystem hL hT hk hφ).locCoef l F z :=
  (D.toGluingSystem hL hT hk hφ).locCoef_real_smul l χ F

/-- Smoothness and the `∂̄`-density bound of the datum `χF`. -/
theorem datum_spec (l : Fin D.m) {C : ℝ} (hC : ∀ z ∈ ball (ctr (n := n) (D.pt l)) (D.R l),
      dbarNormSq (fun z => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)) z ≤ C)
    {z : ComplexModel n} (hz : z ∈ ball (ctr (n := n) (D.pt l)) (D.R l)) :
    ContDiffAt ℝ ∞ ((D.toGluingSystem hL hT hk hφ).locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x)) z ∧
      dbarNormSq ((D.toGluingSystem hL hT hk hφ).locCoef l (fun x => ((χ x : ℝ) : ℂ) • F x)) z ≤
        ((D.chartA l).val.symm ⁻¹' K).indicator
          (fun z => C * ‖(D.toGluingSystem hL hT hk hφ).locCoef l F z‖ ^ 2) z := by
  set G := D.toGluingSystem hL hT hk hφ
  set g := G.locCoef l F
  have hzt : z ∈ (D.chartA l).val.target := D.ball_subset_target l hz
  have hχs : ContDiffAt ℝ ∞ (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hχ (D.chartA l)).contDiffAt ((D.chartA l).val.open_target.mem_nhds hzt))
  rw [D.locCoef_datum hL hT hk hφ hU hF hχ hχU hKU hconst l]
  by_cases hzU : (D.chartA l).val.symm z ∈ U
  · have hO : IsOpen (ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' U) := by
      have := (D.chartA l).val.isOpen_inter_preimage_symm hU
      have heq : ball (ctr (n := n) (D.pt l)) (D.R l) ∩ (D.chartA l).val.symm ⁻¹' U =
          ball (ctr (n := n) (D.pt l)) (D.R l) ∩ ((D.chartA l).val.target ∩ (D.chartA l).val.symm ⁻¹' U) := by
        ext y; simp only [mem_inter_iff, mem_preimage]
        exact ⟨fun h => ⟨h.1, D.ball_subset_target l h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [heq]; exact isOpen_ball.inter this
    have hgd := D.differentiableOn_locCoef_F hL hT hk hφ hU hF hχ hχU hKU hconst l
    have hgC : ContDiffAt ℝ ∞ g z := contDiffAt_real_of_differentiableOn_complex hgd hO ⟨hz, hzU⟩
    have hgD : DifferentiableAt ℂ g z := hgd.differentiableAt (hO.mem_nhds ⟨hz, hzU⟩)
    refine ⟨hχs.mul hgC, ?_⟩
    have hdb : ∀ e : ComplexModel n, dbarDir e (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarDir e (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ)) z * g z := by
      intro e
      rw [dbarDir_mul (hχs.differentiableAt (by simp)) (hgC.differentiableAt (by simp)),
        dbarDir_eq_zero_of_differentiableAt hgD, mul_zero, add_zero]
    have hsq : dbarNormSq (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarNormSq (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ)) z * ‖g z‖ ^ 2 := by
      unfold dbarNormSq
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hdb, norm_mul, mul_pow]
    rw [hsq]
    by_cases hzK : (D.chartA l).val.symm z ∈ K
    · rw [indicator_of_mem (show z ∈ (D.chartA l).val.symm ⁻¹' K from hzK)]
      exact mul_le_mul_of_nonneg_right (hC z hz) (sq_nonneg _)
    · rw [indicator_of_notMem (show z ∉ (D.chartA l).val.symm ⁻¹' K from hzK)]
      have hloc : ∀ᶠ y in 𝓝 z, χ ((D.chartA l).val.symm y) = χ ((D.chartA l).val.symm z) :=
        ((D.chartA l).val.continuousAt_symm hzt).eventually (hconst _ ⟨hzU, hzK⟩)
      have h0 : dbarNormSq (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ)) z = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [dbarDir_congr (g := fun _ => ((χ ((D.chartA l).val.symm z) : ℝ) : ℂ)), dbarDir_const,
          norm_zero]
        · norm_num
        · filter_upwards [hloc] with y hy; rw [hy]
      rw [h0, zero_mul]
  · have hns : (D.chartA l).val.symm z ∉ tsupport χ := fun h => hzU (hχU h)
    have h1 : ∀ᶠ y in 𝓝 z, χ ((D.chartA l).val.symm y) = 0 :=
      ((D.chartA l).val.continuousAt_symm hzt).eventually (notMem_tsupport_iff_eventuallyEq.mp hns)
    have heq : (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ) * g y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h1] with y hy; rw [hy, Complex.ofReal_zero, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, ?_⟩
    have h0 : dbarNormSq (fun y => ((χ ((D.chartA l).val.symm y) : ℝ) : ℂ) * g y) z = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dbarDir_congr heq, dbarDir_const, norm_zero]
      norm_num
    rw [h0]
    exact indicator_nonneg (fun _ _ => mul_nonneg (le_trans (dbarNormSq_nonneg _ z) (hC z hz))
      (sq_nonneg _)) z

/-- The datum `χF` has finite `∂̄`-energy in every chart. -/
theorem energy_datum_lt_top (hK : IsCompact K)
    (hint : ∫⁻ x in K, ENNReal.ofReal (‖F x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) ∂μ < ⊤)
    (l : Fin D.m) :
    (D.toGluingSystem hL hT hk hφ).energy l (fun x => ((χ x : ℝ) : ℂ) • F x) < ⊤ := by
  set G := D.toGluingSystem hL hT hk hφ
  set g := G.locCoef l F
  obtain ⟨C, hC0, hC⟩ := bound_dbarNormSq_χ hχ (D.pt l) (D.closedBall_subset_target l)
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
  -- measurability of the transferred integrand
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
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr G.A_ne_top) hint)

end Datum

end CoverData

/-- **Global `L²` correction of a cut-off holomorphic section** (`claude-global-l2:global-correction`):
`GlobalCutoffCorrectionStatement` holds on every compact complex manifold. -/
theorem globalCutoffCorrection : GlobalCutoffCorrectionStatement n X := by
  intro hX ωb μ hμ L T hL hT θ hθ δ hδ
  have := hX
  obtain ⟨D⟩ := exists_coverData ωb hμ hL hT hθ hδ
  obtain ⟨k₀, hk₀⟩ := D.exists_goodPower hδ
  refine ⟨k₀, fun k hk φ hφ U hU F hF χ hχ hχU K hK hKU hconst hint => ?_⟩
  have hkg := hk₀ k hk
  set G := D.toGluingSystem hL hT hkg hφ with hG
  have hv : G.IsSmooth (fun x => ((χ x : ℝ) : ℂ) • F x) := by
    intro l z hz
    obtain ⟨C, -, hC⟩ := bound_dbarNormSq_χ hχ (D.pt l) (D.closedBall_subset_target l)
    exact (D.datum_spec hL hT hkg hφ hU hF hχ hχU hKU hconst l hC hz).1.contDiffWithinAt
  have hE : G.totalEnergy (fun x => ((χ x : ℝ) : ℂ) • F x) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun l _ =>
      D.energy_datum_lt_top hL hT hkg hφ hU hF hχ hχU hKU hconst hK hint l).ne
  obtain ⟨S, hSloc, hSint⟩ := G.exists_correction (D.kappa_le hL hT hkg hφ) hv hE
  obtain ⟨σ, hσ⟩ := D.exists_section_of_local hL hT hkg hφ S hSloc
  have hfin : (Fintype.card (Fin D.m) : ℝ≥0∞) *
      (G.A * G.K₀ (fun x => ((χ x : ℝ) : ℂ) • F x)) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr G.A_ne_top) (lt_top_iff_ne_top.mpr (G.K₀_ne_top hE)))
  refine ⟨σ, lt_of_le_of_lt (le_of_eq_of_le ?_ hSint) hfin⟩
  refine lintegral_congr fun x => ?_
  simp only [GluingSystem.D, hσ x]

end SGPT.PSH.GlobalL2
