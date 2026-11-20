import SGPT.Bergman.SiuUniformGenerationWeights
import SGPT.Bergman.SiuUniformGenerationProductFrame

/-!
# The actual domain gluing system on the fixed geometric cover

The target bundle is arbitrary with the stated native physical curvature.
Its actual local frames are constructed on the fixed balls by LocalFrame;
all chart, partition, measure and contraction data remain those of `G`.
Blueprint: `siu-uniform-fixed-system.tex`.
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

/-- The fixed base frame domain, chosen before the varying target bundle. -/
abbrev fixedFrameBaseDomain (D : SiuCover μ G G) (a : Fin D.m) : Set X :=
  (D.chartX a).val.source ∩ (D.chartX a).val ⁻¹'
    ball (ctr (n := n) (D.pt a)) (3 * D.R a / 2)

omit [BorelSpace X] in
theorem isOpen_fixedFrameBaseDomain (D : SiuCover μ G G) (a : Fin D.m) :
    IsOpen (fixedFrameBaseDomain D a) :=
  (D.chartX a).val.isOpen_inter_preimage isOpen_ball

theorem mem_fixedFrameBaseDomain (D : SiuCover μ G G) {a : Fin D.m} {q : X × unitDisc}
    (hq : q ∈ (D.chartP a).val.source)
    (hqz : (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    q.1 ∈ fixedFrameBaseDomain D a := by
  have hx := D.mem_of_chartP hq hqz
  exact ⟨hx.1, ball_subset_ball (by linarith [D.R_pos a]) hx.2⟩

/-- Exact equality between the native physical density and the scalar
fixed-frame solver density; no frame oscillation bound occurs. -/
theorem fixedFrameDensity_eq (D : SiuCover μ G G)
    (σ : Fin D.m → (x : X) → E.Fiber x)
    (hσ0 : ∀ a, ∀ x ∈ fixedFrameBaseDomain D a, σ a x ≠ 0)
    {m : ℕ} (hm : 0 < m) {Φ Ψ : X × unitDisc → EReal}
    (hΦ : ∀ q, Φ q ≠ ⊤) (hΨ : ∀ q, Ψ q ≠ ⊤)
    (a : Fin D.m) (q : X × unitDisc) (u : E.Fiber q.1)
    (hq : q ∈ (D.chartP a).val.source)
    (hqz : (D.chartP a).val q ∈ prodDom (ctr (n := n) (D.pt a)) (D.R a) 1) :
    ENNReal.ofReal (‖u‖ ^ 2) * D.weightGen m Φ Ψ q =
      ENNReal.ofReal (‖sectionCoordinate (σ a) q.1 u‖ ^ 2) *
        ballWeight (fixedFramePsi D σ m Φ Ψ a) D.lam (D.ctrP a) ((D.chartP a).val q) := by
  have hx := D.mem_of_chartP hq hqz
  have hs := hσ0 a q.1 (mem_fixedFrameBaseDomain D hq hqz)
  have hN : 0 < ‖σ a q.1‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs)
  have hsymm := (D.chartP a).val.left_inv hq
  have hpX : projX n ((D.chartP a).val q) = (D.chartX a).val q.1 := by
    rw [SiuCover.chartP_apply, projX_prodL]
  have hsx := (D.chartX a).val.left_inv hx.1
  have hpsi : fixedFramePsi D σ m Φ Ψ a ((D.chartP a).val q) +
      ((D.lam * ‖(D.chartP a).val q - D.ctrP a‖ ^ 2 : ℝ) : EReal) =
      SiuCover.thetaGen m Φ Ψ q +
        ((-Real.log (‖σ a q.1‖ ^ 2) + D.lam * ‖q.2.val‖ ^ 2 : ℝ) : EReal) := by
    rw [fixedFramePsi, hsymm, hpX, sectionWeight, hsx,
      add_assoc, ← EReal.coe_add, D.norm_chartP_sub_ctrP a q]
    congr 2
    ring
  have hexp : Real.exp (-(-Real.log (‖σ a q.1‖ ^ 2) + D.lam * ‖q.2.val‖ ^ 2)) =
      ‖σ a q.1‖ ^ 2 * Real.exp (-(D.lam * ‖q.2.val‖ ^ 2)) := by
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hN]
  rw [ballWeight, hpsi,
    multiplierWeight_one_add_coe_real (SiuCover.thetaGen_ne_top hm hΦ hΨ q), hexp,
    SiuCover.weightGen, norm_eq_sectionCoordinate_mul (σ a) hs u, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]
  ring

section System

variable [SFinite μ] (D : SiuCover μ G G)
  (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
  {θ θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG)
  {s : ℝ} {K m : ℕ} (hK : D.GoodPower s K) (hm : 0 < m)
  (hOwnE : IsOwnFirstChernForm E ((m : ℝ) • θ + (K : ℝ) • θG))
  (σ : Fin D.m → (x : X) → E.Fiber x)
  (hσ : ∀ a, IsHolomorphicSectionOn (n := n) E.Fiber (σ a) (fixedFrameBaseDomain D a))
  (hσ0 : ∀ a, ∀ x ∈ fixedFrameBaseDomain D a, σ a x ≠ 0)
  {Φ : X × unitDisc → EReal}
  (hΦ : IsThetaPshPotential
    (ClosedRealOneOneForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ)
  {Ψ : X × unitDisc → EReal}
  (hΨ : ThetaPlurisubharmonic
    (ClosedRealOneOneForm.pullback
      (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) (s • θG)).val Ψ)
  (hΨt : ∀ q, Ψ q ≠ ⊤)

/-- The actual target bundle on the fixed `G`-only geometric cover. -/
def fixedFrameSystem :
    DomainGluingSystem (n + 1) (X × unitDisc) (prodMeasure μ)
      (fun q => E.Fiber q.1) (D.weightGen m Φ Ψ) (Fin D.m) where
  chart a := (D.chartP a).val
  center := D.ctrP
  domR a := prodDom (ctr (n := n) (D.pt a)) (D.R a) 1
  domr a := prodDom (ctr (n := n) (D.pt a)) (D.R a / 2) 1
  domr' a := prodDom (ctr (n := n) (D.pt a)) (D.R a / 4) 1
  isOpen_domR a := isOpen_prodDom _ _ _
  isOpen_domr a := isOpen_prodDom _ _ _
  isOpen_domr' a := isOpen_prodDom _ _ _
  isBounded_domR a := isBounded_prodDom _ _ _
  domr'_sub a := prodDom_mono (by linarith [D.R_pos a]) le_rfl
  domr_sub a := prodDom_mono (by linarith [D.R_pos a]) le_rfl
  domR_sub a := D.prodDom_subset_target a
  cover q := by
    have hne : ∑ a, D.χ a q.1 ≠ 0 := by rw [D.sum_χ q.1]; exact one_ne_zero
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h := D.tsupport_χ a (subset_tsupport _ ha)
    exact ⟨a, by rw [SiuCover.chartP_source]; exact ⟨h.1, mem_univ _⟩, D.chartP_mem_prodDom.mpr h.2⟩
  coef a q := sectionCoordinate (σ a) q.1
  frame a q := σ a q.1
  coef_frame a q hq hqz := sectionCoordinate_section (σ a)
    (hσ0 a q.1 (mem_fixedFrameBaseDomain D hq hqz))
  eq_coef_smul_frame a q u hq hqz := eq_sectionCoordinate_smul (σ a)
    (hσ0 a q.1 (mem_fixedFrameBaseDomain D hq hqz)) u
  transition_holo i l := by
    have hd := differentiableOn_prodSectionCoordinate (D.chartP l)
      (isOpen_fixedFrameBaseDomain D l)
      ((isOpen_fixedFrameBaseDomain D i).preimage continuous_fst)
      (σ l) (hσ l) (hσ0 l) (fun q : X × unitDisc => σ i q.1)
      (isHolomorphicProdSectionOn_baseSection (isOpen_fixedFrameBaseDomain D i) (σ i) (hσ i))
    exact hd.mono fun z hz =>
      ⟨D.prodDom_subset_target l hz.1,
        mem_fixedFrameBaseDomain D ((D.chartP l).val.map_target (D.prodDom_subset_target l hz.1))
          (by rw [(D.chartP l).val.right_inv (D.prodDom_subset_target l hz.1)]; exact hz.1),
        mem_fixedFrameBaseDomain D hz.2.1 hz.2.2⟩
  chart_holo i l := D.chart_holo i l
  dens a w := ENNReal.ofReal (D.dens a (projX n w))
  A := ENNReal.ofReal D.Aμ
  A_ne_top := ENNReal.ofReal_ne_top
  dens_le a w hw := ENNReal.ofReal_le_ofReal (D.dens_le a _ hw.1)
  one_le_A_mul_dens a w hw := by
    rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (D.one_le a _ hw.1)
  map_measure a f hf :=
    setLIntegral_chart_ball (D.chartP a) (ρ := fun w => D.dens a (projX n w))
      ((D.dens_cont a).comp (projX n).continuous.continuousOn fun w hw => by
        rw [pChart_target] at hw; exact hw.1)
      (map_pChart (D.pt a, discOrigin) (D.dens_cont a) (D.dens_map a))
      (isOpen_prodDom _ _ _) (D.prodDom_subset_target a) hf
  Ψ := fixedFramePsi D σ m Φ Ψ
  Ψ_psh := fixedFramePsi_psh D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ
  lam := D.lam
  lam_pos := D.lam_pos
  density_eq a q u hq hqz := fixedFrameDensity_eq D σ hσ0 hm
    (fun q => hΦ.1.quasiPlurisubharmonic.ne_top q) hΨt a q u hq hqz
  localCorr a f hf := productCorrection (ctr (n := n) (D.pt a)) (by linarith [D.R_pos a])
    (D.ctrP a) D.lam_pos (fixedFramePsi_psh D hG hE hθG hK hm hOwnE σ hσ hσ0 hΦ hΨ a) hf
  χ a q := D.χ a q.1
  χ_smooth i l := D.χ_smoothP i l
  χ_nonneg i q := D.χ_nonneg i q.1
  sum_χ q := D.sum_χ q.1
  tsupport_χ a := D.tsupport_χP a
  M := D.M
  dbar_χ_le i l w hw := D.dbar_χ_le' i l hw

end System

end SGPT.Bergman.SiuUniformGeneration
