import SGPT.Bergman.SiuUniformGenerationSystem
import SGPT.Bergman.SiuUniformGenerationProductFrame
import SGPT.PSH.SiuGenCorrection

/-!
# Actual fixed-frame cutoff data and finite energy

The original cutoff section is smooth in every actual fixed-ball frame;
its dbar density is supported in the actual compact transition set. The
native geometric measure transfer then gives finite solver energy from
the original intrinsic transition-energy hypothesis.

Blueprint: `siu-uniform-fixed-datum.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} {G E : HermitianHolomorphicLineBundle.{0, 0} n X} (D : SiuCover μ G G)

section System

variable [SFinite μ] (hG : IsSourceSmoothHermitianMetric G)
  (hE : IsSourceSmoothHermitianMetric E) {θ θG : ClosedRealOneOneForm n X}
  (hθG : IsOwnFirstChernForm G θG) {s : ℝ} {K m : ℕ}
  (hK : D.GoodPower s K) (hm : 0 < m)
  (hOwnE : IsOwnFirstChernForm E ((m : ℝ) • θ + (K : ℝ) • θG))
  (σ : Fin D.m → (x : X) → E.Fiber x)
  (hσ : ∀ a, IsHolomorphicSectionOn (n := n) E.Fiber (σ a)
    ((D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
      ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2)))
  (hσ0 : ∀ a, ∀ x ∈ (D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
    ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2), σ a x ≠ 0)
  {Φ : X × unitDisc → EReal}
  (hΦ : IsThetaPshPotential
    (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
  {Ψ : X × unitDisc → EReal}
  (hΨ : ThetaPlurisubharmonic
    (ClosedRealOneOneForm.pullback (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc))
      (s • θG)).val Ψ) (hΨt : ∀ q, Ψ q ≠ ⊤)

section Datum

variable {U : Set (X × unitDisc)} (hU : IsOpen U)
  {F : (q : X × unitDisc) → E.Fiber q.1}
  (hF : IsHolomorphicProdSectionOn E F U)
  {χ : X × unitDisc → ℝ} (hχ : ChartSmooth (n := n + 1) χ) (hχU : tsupport χ ⊆ U)
  {K' : Set (X × unitDisc)} (hK'U : K' ⊆ U) (hconst : ∀ q ∈ U \ K', ∀ᶠ q' in 𝓝 q, χ q' = χ q)

include hU hF in
/-- Actual local-frame coordinates of the native product section are holomorphic. -/
theorem differentiableOn_fixedFrame_locCoef (l : Fin D.m) :
    DifferentiableOn ℂ ((fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).locCoef l F)
      (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U) := by
  apply (differentiableOn_prodSectionCoordinate (D.chartP l)
    (isOpen_fixedFrameBaseDomain D l) hU (σ l)
    (hσ l) (hσ0 l) F hF).mono
  intro w hw
  refine ⟨D.prodDom_subset_target l hw.1, ?_, hw.2⟩
  exact mem_fixedFrameBaseDomain D
    ((D.chartP l).val.map_target (D.prodDom_subset_target l hw.1))
    (by rw [(D.chartP l).val.right_inv (D.prodDom_subset_target l hw.1)]; exact hw.1)

omit [SFinite μ] in
include hχ in
/-- A uniform bound for `|∂̄(χ ∘ z_l⁻¹)|²` over the compact `K'`. -/
theorem exists_bound_dbar_cutoff (hK' : IsCompact K') (l : Fin D.m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
      (D.chartP l).val.symm z ∈ K' →
        dbarNormSq (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)) z ≤ C := by
  -- `K'` lies over a smaller disc
  obtain ⟨ρ, hρ1, hρK⟩ : ∃ ρ : ℝ, ρ < 1 ∧ ∀ q ∈ K', ‖q.2.val‖ ≤ ρ := by
    rcases K'.eq_empty_or_nonempty with h | h
    · exact ⟨0, one_pos, fun q hq => by rw [h] at hq; exact absurd hq (notMem_empty _)⟩
    obtain ⟨q₀, hq₀, hmax⟩ := hK'.exists_isMaxOn h
      ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).continuousOn)
    exact ⟨‖q₀.2.val‖, mem_unitDisc.mp q₀.2.property, fun q hq => hmax hq⟩
  set Cl : Set (ComplexModel (n + 1)) :=
    (prodL n) '' (closedBall (ctr (n := n) (D.pt l)) (D.R l) ×ˢ closedBall (0 : ComplexModel 1) ρ)
    with hCl
  have hClc : IsCompact Cl :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).image (prodL n).continuous
  have hClt : Cl ⊆ (D.chartP l).val.target := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    rw [pChart_target, mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨(D.hball l ((closedBall_subset_ball (by linarith [D.R_pos l])) hz)).1, ?_⟩
    rw [mem_closedBall_zero_iff] at ht
    exact mem_unitDisc.mpr (lt_of_le_of_lt ht hρ1)
  have hs : ContDiffOn ℝ ∞ (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ))
      (D.chartP l).val.target :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ (D.chartP l))
  have hcont := continuousOn_dbarNormSq (D.chartP l).val.open_target
    (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  obtain ⟨C, hC⟩ := hClc.exists_bound_of_continuousOn (hcont.mono hClt)
  refine ⟨|C|, abs_nonneg C, fun z hz hzK => ?_⟩
  have hzCl : z ∈ Cl := by
    refine ⟨((prodL n).symm z), ⟨ball_subset_closedBall hz.1, ?_⟩, (prodL n).apply_symm_apply z⟩
    rw [mem_closedBall_zero_iff]
    have := hρK _ hzK
    rwa [D.symm_snd hz] at this
  have := hC z hzCl
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_abs_self C))

include hU hF hχ hχU hconst in
/-- Smoothness and the `∂̄`-density bound of the datum `χF`. -/
theorem fixedFrameDatum_spec (l : Fin D.m) {C : ℝ}
    (hC : ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1, (D.chartP l).val.symm z ∈ K' →
      dbarNormSq (fun z => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)) z ≤ C)
    (hC0 : 0 ≤ C) {z : ComplexModel (n + 1)} (hz : z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1) :
    ContDiffAt ℝ ∞ ((fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).locCoef l
        (fun q => ((χ q : ℝ) : ℂ) • F q)) z ∧
      dbarNormSq ((fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).locCoef l
        (fun q => ((χ q : ℝ) : ℂ) • F q)) z ≤
        ((D.chartP l).val.symm ⁻¹' K').indicator
          (fun z => C * ‖(fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).locCoef l F z‖ ^ 2) z := by
  set GS := fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
  set g := GS.locCoef l F
  have hzt : z ∈ (D.chartP l).val.target := D.prodDom_subset_target l hz
  have hχs : ContDiffAt ℝ ∞ (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hχ (D.chartP l)).contDiffAt ((D.chartP l).val.open_target.mem_nhds hzt))
  rw [GS.locCoef_real_smul l χ F]
  change ContDiffAt ℝ ∞ (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z ∧
    dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z ≤
      ((D.chartP l).val.symm ⁻¹' K').indicator (fun z => C * ‖g z‖ ^ 2) z
  by_cases hzU : (D.chartP l).val.symm z ∈ U
  · have hO : IsOpen (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U) := by
      have := (D.chartP l).val.isOpen_inter_preimage_symm hU
      have heq : prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩ (D.chartP l).val.symm ⁻¹' U =
          prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩
            ((D.chartP l).val.target ∩ (D.chartP l).val.symm ⁻¹' U) := by
        ext y; simp only [mem_inter_iff, mem_preimage]
        exact ⟨fun h => ⟨h.1, D.prodDom_subset_target l h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [heq]; exact (isOpen_prodDom _ _ _).inter this
    have hgd := differentiableOn_fixedFrame_locCoef D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt hU hF l
    have hgC : ContDiffAt ℝ ∞ g z := contDiffAt_real_of_differentiableOn_complex hgd hO ⟨hz, hzU⟩
    have hgD : DifferentiableAt ℂ g z := hgd.differentiableAt (hO.mem_nhds ⟨hz, hzU⟩)
    refine ⟨hχs.mul hgC, ?_⟩
    have hdb : ∀ e : ComplexModel (n + 1),
        dbarDir e (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarDir e (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z * g z := by
      intro e
      rw [dbarDir_mul (hχs.differentiableAt (by simp)) (hgC.differentiableAt (by simp)),
        dbarDir_eq_zero_of_differentiableAt hgD, mul_zero, add_zero]
    have hsq : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z =
        dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z * ‖g z‖ ^ 2 := by
      unfold dbarNormSq
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [hdb, norm_mul, mul_pow]
    rw [hsq]
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ (D.chartP l).val.symm ⁻¹' K' from hzK)]
      exact mul_le_mul_of_nonneg_right (hC z hz hzK) (sq_nonneg _)
    · rw [indicator_of_notMem (show z ∉ (D.chartP l).val.symm ⁻¹' K' from hzK)]
      have hloc : ∀ᶠ y in 𝓝 z, χ ((D.chartP l).val.symm y) = χ ((D.chartP l).val.symm z) :=
        ((D.chartP l).val.continuousAt_symm hzt).eventually (hconst _ ⟨hzU, hzK⟩)
      have h0 : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ)) z = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [dbarDir_congr (g := fun _ => ((χ ((D.chartP l).val.symm z) : ℝ) : ℂ)), dbarDir_const,
          norm_zero]
        · norm_num
        · filter_upwards [hloc] with y hy; rw [hy]
      rw [h0, zero_mul]
  · have hns : (D.chartP l).val.symm z ∉ tsupport χ := fun h => hzU (hχU h)
    have h1 : ∀ᶠ y in 𝓝 z, χ ((D.chartP l).val.symm y) = 0 :=
      ((D.chartP l).val.continuousAt_symm hzt).eventually (notMem_tsupport_iff_eventuallyEq.mp hns)
    have heq : (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h1] with y hy; rw [hy, Complex.ofReal_zero, zero_mul]
    refine ⟨contDiffAt_const.congr_of_eventuallyEq heq, ?_⟩
    have h0 : dbarNormSq (fun y => ((χ ((D.chartP l).val.symm y) : ℝ) : ℂ) * g y) z = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [dbarDir_congr heq, dbarDir_const, norm_zero]
      norm_num
    rw [h0]
    exact indicator_nonneg (fun _ _ => mul_nonneg hC0 (sq_nonneg _)) z

include hU hF hχ hχU hK'U hconst in
/-- The datum `χF` has finite `∂̄`-energy in every chart. -/
theorem energy_fixedFrameDatum_lt_top (hK' : IsCompact K')
    (hint : ∫⁻ q in K', ENNReal.ofReal (‖F q‖ ^ 2) *
      multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ) < ⊤) (l : Fin D.m) :
    (fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt).energy l
      (fun q => ((χ q : ℝ) : ℂ) • F q) < ⊤ := by
  set GS := fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
  set g := GS.locCoef l F
  obtain ⟨C, hC0, hC⟩ := exists_bound_dbar_cutoff D hχ hK' l
  set f : X × unitDisc → ℝ≥0∞ := K'.indicator (GS.D F) with hf
  have hB : GS.domR l = prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 := rfl
  have hpt : ∀ z ∈ prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
      ENNReal.ofReal (dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z) * GS.W l z ≤
        ENNReal.ofReal C * f ((D.chartP l).val.symm z) := by
    intro z hz
    have h := (fixedFrameDatum_spec D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt hU hF hχ hχU hconst l
      hC hC0 hz).2
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ (D.chartP l).val.symm ⁻¹' K' from hzK)] at h
      rw [hf, indicator_of_mem hzK]
      calc ENNReal.ofReal (dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z) * GS.W l z
          ≤ ENNReal.ofReal (C * ‖g z‖ ^ 2) * GS.W l z :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal h) zero_le
        _ = ENNReal.ofReal C * GS.D F ((D.chartP l).val.symm z) := by
            rw [show GS.D F ((D.chartP l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) * GS.W l z from
              GS.D_chart l F (by rw [hB]; exact hz), ENNReal.ofReal_mul hC0, mul_assoc]
    · rw [indicator_of_notMem (show z ∉ (D.chartP l).val.symm ⁻¹' K' from hzK)] at h
      have h0 : dbarNormSq (GS.locCoef l (fun q => ((χ q : ℝ) : ℂ) • F q)) z = 0 :=
        le_antisymm h (dbarNormSq_nonneg _ z)
      rw [h0, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
  -- measurability of the transferred integrand
  have hKc : IsClosed K' := hK'.isClosed
  set S' : Set (ComplexModel (n + 1)) := prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 ∩
    (D.chartP l).val.symm ⁻¹' K' with hS'
  have hS'm : MeasurableSet S' := by
    have hO := (D.chartP l).val.isOpen_inter_preimage_symm hKc.isOpen_compl
    have heq : S' = prodDom (ctr (n := n) (D.pt l)) (D.R l) 1 \
        ((D.chartP l).val.target ∩ (D.chartP l).val.symm ⁻¹' K'ᶜ) := by
      ext z
      simp only [hS', mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff, not_and, not_not]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 (D.prodDom_subset_target l h.1)⟩⟩
    rw [heq]
    exact (isOpen_prodDom _ _ _).measurableSet.diff hO.measurableSet
  have hfm : AEMeasurable (fun z => f ((D.chartP l).val.symm z))
      (volume.restrict (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1)) := by
    have hgc : ContinuousOn g S' :=
      (differentiableOn_fixedFrame_locCoef D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
        hU hF l).continuousOn.mono fun z hz => ⟨hz.1, hK'U hz.2⟩
    have hind : AEMeasurable (S'.indicator fun z => ENNReal.ofReal (‖g z‖ ^ 2) * GS.W l z)
        (volume.restrict (prodDom (ctr (n := n) (D.pt l)) (D.R l) 1)) := by
      refine (aemeasurable_indicator_iff hS'm).mpr ?_
      rw [Measure.restrict_restrict hS'm, inter_eq_left.mpr inter_subset_left]
      refine (ENNReal.measurable_ofReal.comp_aemeasurable
        ((hgc.aestronglyMeasurable hS'm).norm.aemeasurable.pow_const 2)).mul ?_
      exact (GS.aemeasurable_W l).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    refine hind.congr ((ae_restrict_iff' (isOpen_prodDom _ _ _).measurableSet).mpr
      (Eventually.of_forall fun z hz => ?_))
    show _ = f ((D.chartP l).val.symm z)
    by_cases hzK : (D.chartP l).val.symm z ∈ K'
    · rw [indicator_of_mem (show z ∈ S' from ⟨hz, hzK⟩), hf,
        indicator_of_mem hzK, show GS.D F ((D.chartP l).val.symm z) = ENNReal.ofReal (‖g z‖ ^ 2) *
          GS.W l z from GS.D_chart l F (by rw [hB]; exact hz)]
    · rw [indicator_of_notMem (show z ∉ S' from fun h => hzK h.2), hf, indicator_of_notMem hzK]
  have hDle : ∫⁻ q in K', GS.D F q ∂(prodMeasure μ) < ⊤ := by
    refine lt_of_le_of_lt (setLIntegral_mono' hKc.measurableSet fun q _ => ?_) hint
    change ENNReal.ofReal (‖F q‖ ^ 2) * (multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) *
      ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))) ≤ _
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) *
          ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))
        ≤ multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.exp_le_one_iff, neg_nonpos]
          have := D.lam_pos
          positivity
      _ = _ := mul_one _
  calc GS.energy l (fun q => ((χ q : ℝ) : ℂ) • F q)
      ≤ ∫⁻ z in prodDom (ctr (n := n) (D.pt l)) (D.R l) 1,
          ENNReal.ofReal C * (GS.A * (f ((D.chartP l).val.symm z) * GS.dens l z)) := by
        refine setLIntegral_mono' (isOpen_prodDom _ _ _).measurableSet fun z hz => (hpt z hz).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc f ((D.chartP l).val.symm z) = 1 * f ((D.chartP l).val.symm z) := (one_mul _).symm
          _ ≤ (GS.A * GS.dens l z) * f ((D.chartP l).val.symm z) :=
              mul_le_mul_of_nonneg_right (GS.one_le_A_mul_dens l z (by rw [hB]; exact hz)) zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal C * (GS.A * ∫⁻ q in GS.region l, f q ∂(prodMeasure μ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ GS.A_ne_top,
          DomainGluingSystem.region, GS.map_measure l f hfm]
        rfl
    _ ≤ ENNReal.ofReal C * (GS.A * ∫⁻ q in K', GS.D F q ∂(prodMeasure μ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ zero_le) zero_le
        rw [← lintegral_indicator hKc.measurableSet]
        exact setLIntegral_le_lintegral _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
        (lt_top_iff_ne_top.mpr GS.A_ne_top) hDle)


end Datum

end System

end SGPT.Bergman.SiuUniformGeneration
