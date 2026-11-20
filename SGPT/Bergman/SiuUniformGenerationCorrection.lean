import SGPT.Bergman.SiuUniformGenerationSystemCorrection
import SGPT.Bergman.SiuUniformGenerationDatum
import SGPT.NAPotential.SiuGenStep

/-!
# Actual uniform intrinsic correction from the fixed geometric cover

The target bundle is arbitrary with the stated native physical curvature.
Its actual local frames are constructed on the fixed balls by LocalFrame;
all chart, partition, measure and contraction data remain those of `G`.
Blueprint: `siu-uniform-fixed-correction.tex`.
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
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.PSH.LineBundleMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} {G E : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The actual product correction property for arbitrary target bundle `E`.
The cover and its `GoodPower` threshold are chosen before `E`, `m` and `Φ`;
all local frames are constructed internally on its preselected balls. -/
theorem hasProdCorrection_fixedCover [CompactSpace X] [SFinite μ]
    (D : SiuCover μ G G) (hG : IsSourceSmoothHermitianMetric G)
    (hE : IsSourceSmoothHermitianMetric E)
    {θ θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG)
    {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
    (hOwnE : IsOwnFirstChernForm E ((m : ℝ) • θ + (K : ℝ) • θG))
    {Φ : X × unitDisc → EReal}
    (hΦ : IsThetaPshPotential
      (ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ) :
    SGPT.NAPotential.SiuGen.HasProdCorrection μ E m Φ (s • θG) := by
  intro Ψ hΨ hΨt U hU F hF χ hχ hχU K' hK' hK'U hconst hint
  obtain ⟨σ, hσσ⟩ := exists_fixedCover_holomorphicFrames D E
  have hσ := fun a => (hσσ a).1
  have hσ0 := fun a => (hσσ a).2
  set GS := fixedFrameSystem D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
  have hv : GS.IsSmooth (fun q => ((χ q : ℝ) : ℂ) • F q) := by
    intro l z hz
    obtain ⟨C, hC0, hC⟩ := exists_bound_dbar_cutoff D hχ hK' l
    exact (fixedFrameDatum_spec D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
      hU hF hχ hχU hconst l hC hC0 hz).1.contDiffWithinAt
  have hEnergy : GS.totalEnergy (fun q => ((χ q : ℝ) : ℂ) • F q) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun l _ =>
      energy_fixedFrameDatum_lt_top D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt
        hU hF hχ hχU hK'U hconst hK' hint l).ne
  obtain ⟨S, hSloc, hSint⟩ := GS.exists_correction
    (kappa_fixedFrameSystem_le D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt) hv hEnergy
  refine ⟨S, isHolomorphicProdSectionOn_of_fixedFrameLocal
    D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ hΨt S hSloc, ?_⟩
  have hfin : (Fintype.card (Fin D.m) : ℝ≥0∞) *
      (GS.A * GS.K₀ (fun q => ((χ q : ℝ) : ℂ) • F q)) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr GS.A_ne_top) (lt_top_iff_ne_top.mpr (GS.K₀_ne_top hEnergy)))
  have hlam := D.lam_pos
  calc ∫⁻ q, ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
        multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) ∂(prodMeasure μ)
      ≤ ∫⁻ q, ENNReal.ofReal (Real.exp D.lam) *
          GS.D (fun q => ((χ q : ℝ) : ℂ) • F q - S q) q ∂(prodMeasure μ) := by
        refine lintegral_mono fun q => ?_
        change _ ≤ ENNReal.ofReal (Real.exp D.lam) * (ENNReal.ofReal
          (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) * (multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) *
            ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))))
        have h1 : 1 ≤ ENNReal.ofReal (Real.exp D.lam) *
            ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.one_le_exp_iff]
          have ht : ‖q.2.val‖ < 1 := mem_unitDisc.mp q.2.property
          have ht2 : ‖q.2.val‖ ^ 2 ≤ 1 := by
            have := norm_nonneg q.2.val
            nlinarith
          nlinarith
        calc ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
              multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q)
            = ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal (‖((χ q : ℝ) : ℂ) • F q - S q‖ ^ 2) *
                multiplierWeight 1 (SiuCover.thetaGen m Φ Ψ q) * (ENNReal.ofReal (Real.exp D.lam) *
                ENNReal.ofReal (Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)))) :=
              mul_le_mul_of_nonneg_left h1 zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.exp D.lam) *
          ∫⁻ q, GS.D (fun q => ((χ q : ℝ) : ℂ) • F q - S q) q ∂(prodMeasure μ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hSint hfin)


end SGPT.Bergman.SiuUniformGeneration
